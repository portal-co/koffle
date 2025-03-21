use std::{
    collections::{BTreeMap, BTreeSet},
    default,
    mem::take,
    sync::Arc,
    usize,
};

use anyhow::Context;
// use arena_traits::IndexAlloc;

use waffle::{
    cfg::CFGInfo,
    const_eval,
    passes::{basic_opt::value_is_pure, tcore::results_ref_2},
    util::new_sig,
    Block, BlockTarget, ConstVal, Func, FuncDecl, FunctionBody, ImportKind, Module, Operator, Type,
    Value, ValueDef,
};
// #[derive(Default)]
pub struct Hustle<'a> {
    pub blocks: BTreeMap<Block, BTreeMap<Vec<Option<(ConstVal, usize)>>, Block>>,
    pub core: &'a mut Core,
}
pub struct Core {
    pub opaque: BTreeMap<Vec<Type>, Func>,
    pub cfg: Arc<Cfg>,
}
pub struct Cfg {
    pub bool_funcs: BTreeSet<Func>,
    pub gl: usize,
    pub inline_constants: BTreeMap<Func, Vec<ConstVal>>,
}
fn cv(k2: &ConstVal, k: Type, new: Block, dst: &mut FunctionBody) -> Value {
    match k2 {
        ConstVal::I32(a) => dst.add_op(new, Operator::I32Const { value: *a }, &[], &[k.clone()]),
        ConstVal::I64(a) => dst.add_op(new, Operator::I64Const { value: *a }, &[], &[k.clone()]),
        ConstVal::F32(a) => dst.add_op(new, Operator::F32Const { value: *a }, &[], &[k.clone()]),
        ConstVal::F64(a) => dst.add_op(new, Operator::F64Const { value: *a }, &[], &[k.clone()]),
        ConstVal::None => dst.add_op(new, Operator::RefNull { ty: k.clone() }, &[], &[k.clone()]),
        ConstVal::Ref(func) => match func.as_ref() {
            None => dst.add_op(new, Operator::RefNull { ty: k.clone() }, &[], &[k.clone()]),
            Some(f) => dst.add_op(new, Operator::RefFunc { func_index: *f }, &[], &[k.clone()]),
        },
    }
}
impl Hustle<'_> {
    pub fn translate(
        &mut self,
        module: &mut Module,
        dst: &mut FunctionBody,
        src: &FunctionBody,
        k: Block,
        cvals: Vec<Option<(ConstVal, usize)>>,
    ) -> anyhow::Result<Block> {
        return stacker::maybe_grow(32 * 1024, 1024 * 1024, move || loop {
            if let Some(l) = self.blocks.get(&k).and_then(|x| x.get(&cvals)) {
                return Ok(*l);
            }
            let new = dst.add_block();
            let mut state = src.blocks[k]
                .params
                .iter()
                .zip(cvals.iter())
                .map(|((k, v), cv2)| {
                    (
                        *v,
                        match cv2.as_ref() {
                            None => (vec![dst.add_blockparam(new, *k)], None, usize::MAX),
                            Some(k2) => (vec![cv(&k2.0, *k, new, dst)], Some(k2.0.clone()), k2.1),
                        },
                    )
                })
                .collect::<BTreeMap<_, _>>();
            self.blocks.entry(k).or_default().insert(cvals.clone(), new);

            let mut state = [(new, state)].into_iter().collect::<BTreeMap<_, _>>();
            'a: for i in src.blocks[k].insts.iter().cloned() {
                if value_is_pure(i, src) {
                    let mut unused = true;
                    for j in src.blocks[k].insts.iter().cloned() {
                        src.values[j].visit_uses(&src.arg_pool, |u| {
                            if u == i {
                                unused = false;
                            }
                        });
                    }
                    src.blocks[k].terminator.visit_uses(|u| {
                        if u == i {
                            unused = false;
                        }
                    });
                    if unused {
                        continue 'a;
                    }
                }
                for (new, mut state2) in take(&mut state) {
                    let mut u =
                        |state2: &mut BTreeMap<_, (Vec<Value>, Option<ConstVal>, usize)>,
                         dst: &mut FunctionBody,
                         s: Value| {
                            let Some((t, v, u)) = state2.remove(&s) else {
                                return None;
                            };
                            if u == usize::MAX {
                                state2.insert(s, (t, v, u));
                            } else {
                                if let Some(u) = u.checked_sub(1) {
                                    state2.insert(s, (t, v, u));
                                } else {
                                    let v = t
                                        .iter()
                                        .filter_map(|a| dst.values[*a].ty(&dst.type_pool))
                                        .collect::<Vec<_>>();
                                    let f =
                                        *self.core.opaque.entry(v.to_owned()).or_insert_with_key(
                                            |a| {
                                                let a = a.clone();
                                                let sig = new_sig(
                                                    module,
                                                    waffle::SignatureData::Func {
                                                        params: a.clone(),
                                                        returns: a,
                                                    },
                                                );
                                                let mut g = FunctionBody::new(module, sig);
                                                let args = g.blocks[g.entry]
                                                    .params
                                                    .iter()
                                                    .map(|a| a.1)
                                                    .collect();
                                                g.set_terminator(
                                                    g.entry,
                                                    waffle::Terminator::Return { values: args },
                                                );
                                                module.funcs.push(waffle::FuncDecl::Body(
                                                    sig,
                                                    format!("opaquify"),
                                                    g,
                                                ))
                                            },
                                        );
                                    let args = t;
                                    let v = dst.add_op(
                                        new,
                                        Operator::Call { function_index: f },
                                        &args,
                                        &v,
                                    );
                                    let v = results_ref_2(dst, v);
                                    state2.insert(s, (v, None, usize::MAX));
                                }
                            };
                            return state2.get(&s).cloned();
                        };
                    let new = new;
                    let v = match &src.values[i] {
                        waffle::ValueDef::BlockParam(block, _, _) => todo!(),
                        waffle::ValueDef::Operator(operator, list_ref, list_ref1) => match operator
                        {
                            Operator::Call { function_index }
                                if self.core.cfg.inline_constants.contains_key(function_index) =>
                            {
                                let tys = &src.type_pool[*list_ref1];
                                let Some(v) = self.core.cfg.inline_constants.get(function_index)
                                else {
                                    unreachable!()
                                };
                                let v2 = v
                                    .iter()
                                    .zip(tys.iter().cloned())
                                    .map(|(a, b)| cv(a, b, new, dst))
                                    .collect::<Vec<_>>();
                                let c = if v.len() == 1 {
                                    Some(v[0].clone())
                                } else {
                                    None
                                };
                                (v2, c, self.core.cfg.gl)
                            }
                            operator => {
                                let mut a = usize::MAX;
                                let mut d = vec![];
                                let args = src.arg_pool[*list_ref]
                                    .iter()
                                    .filter_map(|a| u(&mut state2, dst, *a))
                                    .map(|(v, c, b)| {
                                        a = a.min(b);
                                        d.push(c);
                                        v
                                    })
                                    .flatten()
                                    .collect::<Vec<_>>();
                                let tys = &src.type_pool[*list_ref1];
                                let d = d.into_iter().collect::<Option<Vec<_>>>();
                                let c = d.and_then(|d| const_eval(operator, &d, None));
                                let a = if c.is_some() {
                                    a.min(self.core.cfg.gl)
                                } else {
                                    a
                                };
                                let a = match operator {
                                    Operator::Call { .. }
                                    | Operator::CallIndirect { .. }
                                    | Operator::CallRef { .. } => usize::MAX,
                                    _ => a,
                                };
                                let v = match c.as_ref() {
                                    None => dst.add_op(new, operator.clone(), &args, tys),
                                    Some(a) => cv(a, tys[0].clone(), new, dst),
                                };
                                (results_ref_2(dst, v), c, a)
                            }
                        },
                        waffle::ValueDef::PickOutput(value, a, b) => {
                            let value = state2
                                .get(value)
                                .cloned()
                                .context("in getting the referenced value")?;
                            let new_value = value.0[*a as usize];
                            dst.append_to_block(new, new_value);
                            (vec![new_value], None, value.2)
                        }
                        waffle::ValueDef::Alias(value) => state2
                            .get(value)
                            .cloned()
                            .context("in getting the referenced value")?,
                        waffle::ValueDef::Placeholder(_) => todo!(),
                        _ => (
                            vec![dst.add_op(new, Operator::Nop, &[], &[])],
                            None,
                            usize::MAX,
                        ),
                    };
                    match &src.values[i] {
                        ValueDef::Operator(
                            Operator::I32Eqz
                            | Operator::I64Eqz
                            | Operator::I32Eq
                            | Operator::I64Eq
                            | Operator::I32Ne
                            | Operator::I64Ne
                            | Operator::I32LtS
                            | Operator::I32LtU
                            | Operator::I32LeU
                            | Operator::I32LeS
                            | Operator::I32GtS
                            | Operator::I32GtU
                            | Operator::I32GeS
                            | Operator::I32GeU
                            | Operator::I64LtS
                            | Operator::I64LtU
                            | Operator::I64LeU
                            | Operator::I64LeS
                            | Operator::I64GtS
                            | Operator::I64GtU
                            | Operator::I64GeS
                            | Operator::I64GeU,
                            _,
                            _,
                        ) if v.1.is_none() => {
                            let (t, mut ts) = (dst.add_block(), state2.clone());
                            let (f, mut fs) = (dst.add_block(), state2.clone());
                            dst.set_terminator(
                                new,
                                waffle::Terminator::CondBr {
                                    cond: v.0[0],
                                    if_true: BlockTarget {
                                        block: t,
                                        args: vec![],
                                    },
                                    if_false: BlockTarget {
                                        block: f,
                                        args: vec![],
                                    },
                                },
                            );
                            // let i2 = v.1;
                            let i3 = v.2.max(self.core.cfg.gl);
                            let v =
                                dst.add_op(t, Operator::I32Const { value: 1 }, &[], &[Type::I32]);
                            ts.insert(i, (vec![v], Some(ConstVal::I32(1)), i3));
                            let v =
                                dst.add_op(f, Operator::I32Const { value: 0 }, &[], &[Type::I32]);
                            fs.insert(i, (vec![v], Some(ConstVal::I32(0)), i3));
                            state.insert(t, ts);
                            state.insert(f, fs);
                        }
                        ValueDef::Operator(Operator::Call { function_index }, _, _)
                            if self.core.cfg.bool_funcs.contains(function_index) =>
                        {
                            let (t, mut ts) = (dst.add_block(), state2.clone());
                            let (f, mut fs) = (dst.add_block(), state2.clone());
                            dst.set_terminator(
                                new,
                                waffle::Terminator::CondBr {
                                    cond: v.0[0],
                                    if_true: BlockTarget {
                                        block: t,
                                        args: vec![],
                                    },
                                    if_false: BlockTarget {
                                        block: f,
                                        args: vec![],
                                    },
                                },
                            );
                            // let i2 = v.1;
                            let i3 = v.2.max(self.core.cfg.gl);
                            let v =
                                dst.add_op(t, Operator::I32Const { value: 1 }, &[], &[Type::I32]);
                            ts.insert(i, (vec![v], Some(ConstVal::I32(1)), i3));
                            let v =
                                dst.add_op(f, Operator::I32Const { value: 0 }, &[], &[Type::I32]);
                            fs.insert(i, (vec![v], Some(ConstVal::I32(0)), i3));
                            state.insert(t, ts);
                            state.insert(f, fs);
                        }
                        _ => {
                            state2.insert(i, v);
                            state.insert(new, state2);
                        }
                    }
                }
            }
            for (new, state) in state.into_iter() {
                let mut target_ = |k: &BlockTarget| {
                    let mut cp = vec![];
                    anyhow::Ok(BlockTarget {
                        args: k
                            .args
                            .iter()
                            .filter_map(|b| state.get(b))
                            .cloned()
                            .filter_map(|(a, b, c)| match b.map(|b| (b, c)) {
                                None => Some(a),
                                Some(d) => {
                                    cp.push(Some(d));
                                    None
                                }
                            })
                            .flatten()
                            .collect(),
                        block: self.translate(module, dst, src, k.block, cp)?,
                    })
                };
                let t = match &src.blocks[k].terminator {
                    waffle::Terminator::Br { target } => waffle::Terminator::Br {
                        target: target_(target)?,
                    },
                    waffle::Terminator::CondBr {
                        cond,
                        if_true,
                        if_false,
                    } => {
                        let cond = state
                            .get(cond)
                            .cloned()
                            .context("in getting the referenced value")?;
                        match cond.1.clone() {
                            Some(ConstVal::I32(a)) => waffle::Terminator::Br {
                                target: target_(if a == 0 { if_false } else { if_true })?,
                            },
                            Some(ConstVal::I64(a)) => waffle::Terminator::Br {
                                target: target_(if a == 0 { if_false } else { if_true })?,
                            },
                            _ => {
                                let if_true = target_(if_true)?;
                                let if_false = target_(if_false)?;
                                waffle::Terminator::CondBr {
                                    cond: cond.0[0],
                                    if_true,
                                    if_false,
                                }
                            }
                        }
                    }
                    waffle::Terminator::Select {
                        value,
                        targets,
                        default,
                    } => {
                        let value = state
                            .get(value)
                            .cloned()
                            .context("in getting the referenced value")?;

                        match value.1.clone() {
                            Some(ConstVal::I32(a)) => waffle::Terminator::Br {
                                target: target_(targets.get(a as usize).unwrap_or(default))?,
                            },
                            Some(ConstVal::I64(a)) => waffle::Terminator::Br {
                                target: target_(targets.get(a as usize).unwrap_or(default))?,
                            },
                            _ => {
                                let default = target_(default)?;
                                let targets = targets
                                    .iter()
                                    .map(target_)
                                    .collect::<anyhow::Result<Vec<_>>>()?;
                                waffle::Terminator::Select {
                                    value: value.0[0],
                                    targets,
                                    default,
                                }
                            }
                        }
                    }
                    waffle::Terminator::Return { values } => waffle::Terminator::Return {
                        values: values
                            .iter()
                            .filter_map(|b| state.get(b))
                            .flat_map(|a| a.0.clone())
                            .collect(),
                    },
                    waffle::Terminator::ReturnCall { func, args } => {
                        waffle::Terminator::ReturnCall {
                            func: *func,
                            args: args
                                .iter()
                                .filter_map(|b| state.get(b))
                                .flat_map(|a| a.0.clone())
                                .collect(),
                        }
                    }
                    waffle::Terminator::ReturnCallIndirect { sig, table, args } => {
                        waffle::Terminator::ReturnCallIndirect {
                            sig: *sig,
                            table: *table,
                            args: args
                                .iter()
                                .filter_map(|b| state.get(b))
                                .flat_map(|a| a.0.clone())
                                .collect(),
                        }
                    }
                    waffle::Terminator::ReturnCallRef { sig, args } => match args.split_last() {
                        Some((a, args))
                            if matches!(
                                state.get(a),
                                Some((_, Some(ConstVal::Ref(Some(_))), _))
                            ) =>
                        {
                            let Some((_, Some(ConstVal::Ref(Some(f))), _)) = state.get(a) else {
                                unreachable!()
                            };
                            waffle::Terminator::ReturnCall {
                                func: *f,
                                args: args
                                    .iter()
                                    .filter_map(|b| state.get(b))
                                    .flat_map(|a| a.0.clone())
                                    .collect(),
                            }
                        }
                        _ => waffle::Terminator::ReturnCallRef {
                            sig: *sig,
                            args: args
                                .iter()
                                .filter_map(|b| state.get(b))
                                .flat_map(|a| a.0.clone())
                                .collect(),
                        },
                    },
                    waffle::Terminator::Unreachable => waffle::Terminator::Unreachable,
                    _ => waffle::Terminator::None,
                };
                dst.set_terminator(new, t);
            }
        });
    }
}
pub fn hustle_mod(m: &mut Module, cfg: Cfg) -> anyhow::Result<()> {
    let mut c = Core {
        // gl,
        opaque: Default::default(),
        // bool_funcs,
        cfg: Arc::new(cfg),
    };
    for f in m.funcs.iter().collect::<BTreeSet<_>>() {
        let mut g = take(&mut m.funcs[f]);
        if let FuncDecl::Body(s, _, b) = &mut g {
            b.convert_to_max_ssa(None);
            let s = *s;
            let mut new = FunctionBody::new(&m, s);
            new.entry = match (Hustle {
                blocks: Default::default(),
                core: &mut c,
            })
            .translate(
                m,
                &mut new,
                &*b,
                b.entry,
                b.blocks[b.entry].params.iter().map(|_| None).collect(),
            ) {
                Ok(a) => a,
                Err(e) => {
                    m.funcs[f] = g;
                    return Err(e);
                }
            };
            new.recompute_edges();
            *b = new;
        }
        m.funcs[f] = g;
    }
    Ok(())
}
impl Cfg {
    pub fn wasi(&mut self, m: &mut Module) {
        for mut i in take(&mut m.imports) {
            let ImportKind::Func(f) = i.kind.clone() else {
                m.imports.push(i);
                continue;
            };
            if i.module != "wasi_snapshot_preview1"
                && i.module != "wasix_32v1"
                && i.module != "wasix_64v1"
            {
                m.imports.push(i);
                continue;
            }
            let val = 8;
            self.inline_constants.insert(f, vec![ConstVal::I32(val)]);
            let sig = m.funcs[f].sig();
            let name = m.funcs[f].name().to_owned();
            let mut new = FunctionBody::new(&m, sig);
            let v = new.add_op(
                new.entry,
                Operator::I32Const { value: val },
                &[],
                &[Type::I32],
            );
            new.set_terminator(new.entry, waffle::Terminator::Return { values: vec![v] });
            m.funcs[f] = FuncDecl::Body(sig, name, new);
        }
    }
}

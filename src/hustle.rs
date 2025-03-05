use std::{collections::BTreeMap, default, mem::take, usize};

use anyhow::Context;
// use arena_traits::IndexAlloc;

use waffle::{
    cfg::CFGInfo,
    const_eval,
    passes::{basic_opt::value_is_pure, tcore::results_ref_2},
    util::new_sig,
    Block, BlockTarget, ConstVal, Func, FunctionBody, Module, Operator, Type, ValueDef,
};
// #[derive(Default)]
pub struct Hustle<'a> {
    pub blocks: BTreeMap<Block, BTreeMap<Vec<Option<(ConstVal, usize)>>, Block>>,
    pub core: &'a mut Core,
}
pub struct Core {
    pub opaque: BTreeMap<Vec<Type>, Func>,
    pub gl: usize,
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
                .map(|((k, v), cv)| {
                    (
                        *v,
                        match cv.as_ref() {
                            None => (dst.add_blockparam(new, *k), None, usize::MAX),
                            Some(k2) => (
                                match &k2.0 {
                                    ConstVal::I32(a) => dst.add_op(
                                        new,
                                        Operator::I32Const { value: *a },
                                        &[],
                                        &[k.clone()],
                                    ),
                                    ConstVal::I64(a) => dst.add_op(
                                        new,
                                        Operator::I64Const { value: *a },
                                        &[],
                                        &[k.clone()],
                                    ),
                                    ConstVal::F32(a) => dst.add_op(
                                        new,
                                        Operator::F32Const { value: *a },
                                        &[],
                                        &[k.clone()],
                                    ),
                                    ConstVal::F64(a) => dst.add_op(
                                        new,
                                        Operator::F64Const { value: *a },
                                        &[],
                                        &[k.clone()],
                                    ),
                                    ConstVal::None => dst.add_op(
                                        new,
                                        Operator::RefNull { ty: k.clone() },
                                        &[],
                                        &[k.clone()],
                                    ),
                                    ConstVal::Ref(func) => match func.as_ref() {
                                        None => dst.add_op(
                                            new,
                                            Operator::RefNull { ty: k.clone() },
                                            &[],
                                            &[k.clone()],
                                        ),
                                        Some(f) => dst.add_op(
                                            new,
                                            Operator::RefFunc { func_index: *f },
                                            &[],
                                            &[k.clone()],
                                        ),
                                    },
                                },
                                Some(k2.0.clone()),
                                k2.1,
                            ),
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
                    for (s, (t, v, mut u)) in take(&mut state2) {
                        if u == usize::MAX {
                            state2.insert(s, (t, v, u));
                        } else {
                            if let Some(u) = u.checked_sub(1) {
                                state2.insert(s, (t, v, u));
                            } else {
                                let v = dst.values[t].tys(&dst.type_pool).to_owned();
                                let f =
                                    *self
                                        .core
                                        .opaque
                                        .entry(v.to_owned())
                                        .or_insert_with_key(|a| {
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
                                        });
                                let args = results_ref_2(dst, t);
                                let v = dst.add_op(
                                    new,
                                    Operator::Call { function_index: f },
                                    &args,
                                    &v,
                                );
                                state2.insert(s, (v, None, usize::MAX));
                            }
                        }
                    }
                    let new = new;
                    let v = match &src.values[i] {
                        waffle::ValueDef::BlockParam(block, _, _) => todo!(),
                        waffle::ValueDef::Operator(operator, list_ref, list_ref1) => {
                            let mut a = usize::MAX;
                            let mut d = vec![];
                            let args = src.arg_pool[*list_ref]
                                .iter()
                                .filter_map(|a| state2.get(a))
                                .cloned()
                                .map(|(v, c, b)| {
                                    a = a.min(b);
                                    d.push(c);
                                    v
                                })
                                .collect::<Vec<_>>();
                            let tys = &src.type_pool[*list_ref1];
                            let d = d.into_iter().collect::<Option<Vec<_>>>();
                            let c = d.and_then(|d| const_eval(operator, &d, None));
                            let a = if c.is_some() { a.min(self.core.gl) } else { a };
                            let a = match operator {
                                Operator::Call { .. }
                                | Operator::CallIndirect { .. }
                                | Operator::CallRef { .. } => usize::MAX,
                                _ => a,
                            };
                            (dst.add_op(new, operator.clone(), &args, tys), c, a)
                        }
                        waffle::ValueDef::PickOutput(value, a, b) => {
                            let value = state2
                                .get(value)
                                .cloned()
                                .context("in getting the referenced value")?;
                            let new_value = dst.values.push(ValueDef::PickOutput(value.0, *a, *b));
                            dst.append_to_block(new, new_value);
                            (new_value, None, value.2)
                        }
                        waffle::ValueDef::Alias(value) => state2
                            .get(value)
                            .cloned()
                            .context("in getting the referenced value")?,
                        waffle::ValueDef::Placeholder(_) => todo!(),
                        _ => (dst.add_op(new, Operator::Nop, &[], &[]), None, usize::MAX),
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
                                    cond: v.0,
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
                            let i3 = v.2.max(self.core.gl);
                            let v =
                                dst.add_op(t, Operator::I32Const { value: 1 }, &[], &[Type::I32]);
                            ts.insert(i, (v, Some(ConstVal::I32(1)), i3));
                            let v =
                                dst.add_op(f, Operator::I32Const { value: 0 }, &[], &[Type::I32]);
                            fs.insert(i, (v, Some(ConstVal::I32(0)), i3));
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
                            .map(|(a, b, c)| {
                                cp.push(b.map(|b| (b, c)));
                                a
                            })
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
                                    cond: cond.0,
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
                                    value: value.0,
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
                            .map(|a| a.0)
                            .collect(),
                    },
                    waffle::Terminator::ReturnCall { func, args } => {
                        waffle::Terminator::ReturnCall {
                            func: *func,
                            args: args
                                .iter()
                                .filter_map(|b| state.get(b))
                                .map(|a| a.0)
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
                                .map(|a| a.0)
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
                                    .map(|a| a.0)
                                    .collect(),
                            }
                        }
                        _ => waffle::Terminator::ReturnCallRef {
                            sig: *sig,
                            args: args
                                .iter()
                                .filter_map(|b| state.get(b))
                                .map(|a| a.0)
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

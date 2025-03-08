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
    Block, BlockTarget, ConstVal, Func, FuncDecl, FunctionBody, ImportKind, Module, Operator,
    SignatureData, Terminator, Type, Value, ValueDef,
};

use crate::FuncCollector;
#[derive(Clone)]
pub struct InlineCfg {
    pub funcs: BTreeSet<Func>,
}
impl FuncCollector for InlineCfg {
    fn add_func(&mut self, f: Func) {
        self.funcs.insert(f);
    }
}
pub struct Inline {
    pub blocks: BTreeMap<Block, Block>,
    pub return_to: Option<Block>,
    pub inline_funcs: Arc<InlineCfg>,
    pub stack: BTreeSet<Func>,
}
pub fn inline_mod(m: &mut Module, cfg: InlineCfg) -> anyhow::Result<()> {
    for f in m.funcs.iter().collect::<BTreeSet<_>>() {
        let mut g = take(&mut m.funcs[f]);
        if let FuncDecl::Body(s, _, b) = &mut g {
            b.convert_to_max_ssa(None);
            let s = *s;
            let mut new = FunctionBody::new(&m, s);
            new.entry = match (Inline::new(cfg.clone())).translate(
                m, &mut new, &*b,
                b.entry,
                // b.blocks[b.entry].params.iter().map(|_| None).collect(),
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
impl Inline {
    pub fn new(a: InlineCfg) -> Self {
        Self {
            blocks: BTreeMap::new(),
            return_to: None,
            inline_funcs: Arc::new(a),
            stack: Default::default(),
        }
    }
    pub fn translate(
        &mut self,
        module: &Module,
        dst: &mut FunctionBody,
        src: &FunctionBody,
        k: Block,
    ) -> anyhow::Result<Block> {
        return stacker::maybe_grow(32 * 1024, 1024 * 1024, move || loop {
            if let Some(l) = self.blocks.get(&k) {
                return Ok(*l);
            }
            let mut new = dst.add_block();
            let mut state = src.blocks[k]
                .params
                .iter()
                .map(|(k, v)| (*v, vec![dst.add_blockparam(new, *k)]))
                .collect::<BTreeMap<_, _>>();
            self.blocks.insert(k, new);
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
                let v = match &src.values[i] {
                    waffle::ValueDef::BlockParam(block, _, _) => todo!(),
                    waffle::ValueDef::Operator(operator, list_ref, list_ref1) => match operator {
                        Operator::Call { function_index }
                            if self.inline_funcs.funcs.contains(function_index)
                                && !self.stack.contains(function_index)
                                && module.funcs[*function_index].body().is_some() =>
                        {
                            let Some(b) = module.funcs[*function_index].body() else {
                                unreachable!()
                            };
                            let k2 = dst.add_block();
                            let tys = &src.type_pool[*list_ref1];
                            let args = src.arg_pool[*list_ref]
                                .iter()
                                .filter_map(|a| state.get(a))
                                .flatten()
                                .cloned()
                                .collect::<Vec<_>>();
                            let ke = Inline {
                                blocks: Default::default(),
                                return_to: Some(k2),
                                inline_funcs: self.inline_funcs.clone(),
                                stack: match self.stack.clone() {
                                    mut a => {
                                        a.insert(*function_index);
                                        a
                                    }
                                },
                            }
                            .translate(module, dst, b, b.entry)?;
                            dst.set_terminator(
                                new,
                                waffle::Terminator::Br {
                                    target: BlockTarget {
                                        block: ke,
                                        args: args,
                                    },
                                },
                            );
                            new = k2;
                            tys.iter()
                                .cloned()
                                .map(|a| dst.add_blockparam(new, a))
                                .collect()
                        }
                        operator => {
                            let args = src.arg_pool[*list_ref]
                                .iter()
                                .filter_map(|a| state.get(a))
                                .flatten()
                                .cloned()
                                .collect::<Vec<_>>();
                            let tys = &src.type_pool[*list_ref1];
                            let v = dst.add_op(new, operator.clone(), &args, tys);
                            results_ref_2(dst, v)
                        }
                    },
                    waffle::ValueDef::PickOutput(value, a, b) => {
                        let value = state
                            .get(value)
                            .cloned()
                            .context("in getting the referenced value")?;
                        let new_value = value[*a as usize];
                        dst.append_to_block(new, new_value);
                        vec![new_value]
                    }
                    waffle::ValueDef::Alias(value) => state
                        .get(value)
                        .cloned()
                        .context("in getting the referenced value")?,
                    waffle::ValueDef::Placeholder(_) => todo!(),
                    waffle::ValueDef::None => vec![],
                };
                state.insert(i, v);
            }
            let mut target_ = |k: &BlockTarget| {
                anyhow::Ok(BlockTarget {
                    args: k
                        .args
                        .iter()
                        .filter_map(|b| state.get(b))
                        .flatten()
                        .cloned()
                        .collect(),
                    block: self.translate(module, dst, src, k.block)?,
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
                    let if_true = target_(if_true)?;
                    let if_false = target_(if_false)?;
                    let cond = state
                        .get(cond)
                        .cloned()
                        .context("in getting the referenced value")?;
                    waffle::Terminator::CondBr {
                        cond: cond[0],
                        if_true,
                        if_false,
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
                    let default = target_(default)?;
                    let targets = targets
                        .iter()
                        .map(target_)
                        .collect::<anyhow::Result<Vec<_>>>()?;
                    waffle::Terminator::Select {
                        value: value[0],
                        targets,
                        default,
                    }
                }
                waffle::Terminator::Return { values } => match self.return_to {
                    None => waffle::Terminator::Return {
                        values: values
                            .iter()
                            .filter_map(|b| state.get(b))
                            .flatten()
                            .cloned()
                            .collect(),
                    },
                    Some(k) => waffle::Terminator::Br {
                        target: BlockTarget {
                            block: k,
                            args: values
                                .iter()
                                .filter_map(|b| state.get(b))
                                .flatten()
                                .cloned()
                                .collect(),
                        },
                    },
                },
                waffle::Terminator::ReturnCall { func, args } => match self.return_to {
                    None => waffle::Terminator::ReturnCall {
                        func: *func,
                        args: args
                            .iter()
                            .filter_map(|b| state.get(b))
                            .flatten()
                            .cloned()
                            .collect(),
                    },
                    Some(k) => {
                        if self.inline_funcs.funcs.contains(func)
                            && !self.stack.contains(func)
                            && module.funcs[*func].body().is_some()
                        {
                            let Some(b) = module.funcs[*func].body() else {
                                unreachable!()
                            };
                            // let k2 = dst.add_block();
                            let tys = match &module.signatures[module.funcs[*func].sig()] {
                                SignatureData::Func { params, returns } => returns,
                                _ => todo!(),
                            };
                            let args = args
                                .iter()
                                .filter_map(|a| state.get(a))
                                .flatten()
                                .cloned()
                                .collect::<Vec<_>>();
                            let ke = Inline {
                                blocks: Default::default(),
                                return_to: Some(k),
                                inline_funcs: self.inline_funcs.clone(),
                                stack: match self.stack.clone() {
                                    mut a => {
                                        a.insert(*func);
                                        a
                                    }
                                },
                            }
                            .translate(module, dst, b, b.entry)?;
                            Terminator::Br {
                                target: BlockTarget {
                                    block: ke,
                                    args: args,
                                },
                            }
                        } else {
                            let tys = match &module.signatures[module.funcs[*func].sig()] {
                                SignatureData::Func { params, returns } => returns,
                                _ => todo!(),
                            };
                            let values = dst.add_op(
                                new,
                                Operator::Call {
                                    function_index: *func,
                                },
                                &args,
                                &tys,
                            );
                            let values = results_ref_2(dst, values);
                            waffle::Terminator::Br {
                                target: BlockTarget {
                                    block: k,
                                    args: values
                                        .iter()
                                        .filter_map(|b| state.get(b))
                                        .flatten()
                                        .cloned()
                                        .collect(),
                                },
                            }
                        }
                    }
                },
                waffle::Terminator::ReturnCallIndirect { sig, table, args } => match self.return_to
                {
                    None => waffle::Terminator::ReturnCallIndirect {
                        sig: *sig,
                        table: *table,
                        args: args
                            .iter()
                            .filter_map(|b| state.get(b))
                            .flatten()
                            .cloned()
                            .collect(),
                    },
                    Some(k) => {
                        let tys = match &module.signatures[*sig] {
                            SignatureData::Func { params, returns } => returns,
                            _ => todo!(),
                        };
                        let values = dst.add_op(
                            new,
                            Operator::CallIndirect {
                                sig_index: *sig,
                                table_index: *table,
                            },
                            &args,
                            &tys,
                        );
                        let values = results_ref_2(dst, values);
                        waffle::Terminator::Br {
                            target: BlockTarget {
                                block: k,
                                args: values
                                    .iter()
                                    .filter_map(|b| state.get(b))
                                    .flatten()
                                    .cloned()
                                    .collect(),
                            },
                        }
                    }
                },
                waffle::Terminator::ReturnCallRef { sig, args } => match self.return_to {
                    None => waffle::Terminator::ReturnCallRef {
                        sig: *sig,
                        args: args
                            .iter()
                            .filter_map(|b| state.get(b))
                            .flatten()
                            .cloned()
                            .collect(),
                    },
                    Some(k) => {
                        let tys = match &module.signatures[*sig] {
                            SignatureData::Func { params, returns } => returns,
                            _ => todo!(),
                        };
                        let values =
                            dst.add_op(new, Operator::CallRef { sig_index: *sig }, &args, &tys);
                        let values = results_ref_2(dst, values);
                        waffle::Terminator::Br {
                            target: BlockTarget {
                                block: k,
                                args: values
                                    .iter()
                                    .filter_map(|b| state.get(b))
                                    .flatten()
                                    .cloned()
                                    .collect(),
                            },
                        }
                    }
                },
                waffle::Terminator::Unreachable => waffle::Terminator::Unreachable,
                _ => waffle::Terminator::None,
            };
            dst.set_terminator(new, t);
        });
    }
}

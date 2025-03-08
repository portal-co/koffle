use std::{
    collections::{BTreeMap, BTreeSet},
    default,
    mem::replace,
    sync::Arc,
};

use anyhow::Context;
// use arena_traits::IndexAlloc;

use waffle::{
    cfg::CFGInfo, passes::basic_opt::value_is_pure, Block, BlockTarget, FunctionBody, Operator,
    Type, ValueDef,
};

use crate::TableInfo;
#[derive(Default)]
pub struct Detta {
    pub blocks: BTreeMap<Block, BTreeMap<Vec<Option<TableInfo>>, Block>>,
    pub tables: Arc<BTreeSet<TableInfo>>,
}
impl Detta {
    pub fn translate(
        &mut self,
        dst: &mut FunctionBody,
        src: &FunctionBody,
        k: Block,
        wraps: Vec<Option<TableInfo>>,
    ) -> anyhow::Result<Block> {
        return stacker::maybe_grow(32 * 1024, 1024 * 1024, move || loop {
            if let Some(l) = self.blocks.get(&k).and_then(|a| a.get(&wraps)) {
                return Ok(*l);
            }
            let new = dst.add_block();
            let mut state = src.blocks[k]
                .params
                .iter()
                .zip(wraps.iter())
                .map(|((k, v), w)| (*v, (dst.add_blockparam(new, *k), *w)))
                .collect::<BTreeMap<_, _>>();
            self.blocks.entry(k).or_default().insert(wraps.clone(), new);
            // let mut taffy = BTreeMap::new();
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
                            if self.tables.iter().any(|x| x.talloc == *function_index) =>
                        {
                            let args = src.arg_pool[*list_ref]
                                .iter()
                                .filter_map(|a| state.get(a))
                                .cloned()
                                .map(|(a, b)| match b {
                                    None => a,
                                    Some(c) => dst.add_op(
                                        new,
                                        Operator::TableGet {
                                            table_index: c.table,
                                        },
                                        &[a],
                                        &[Type::Heap(c.ty)],
                                    ),
                                })
                                .collect::<Vec<_>>();
                            (
                                args[0],
                                Some(
                                    *self
                                        .tables
                                        .iter()
                                        .find(|a| a.talloc == *function_index)
                                        .unwrap(),
                                ),
                            )
                        }
                        Operator::TableGet { table_index }
                            if self.tables.iter().any(|x| x.table == *table_index) =>
                        {
                            let args = src.arg_pool[*list_ref]
                                .iter()
                                .filter_map(|a| state.get(a))
                                .cloned()
                                .next()
                                .and_then(|(a, b)| match b {
                                    Some(c) if c.table == *table_index => Some(a),
                                    _ => None,
                                });
                            // .unwrap();
                            match args {
                                Some(a) => (a, None),
                                None => {
                                    let args = src.arg_pool[*list_ref]
                                        .iter()
                                        .filter_map(|a| state.get(a))
                                        .cloned()
                                        .map(|(a, b)| match b {
                                            None => a,
                                            Some(c) => dst.add_op(
                                                new,
                                                Operator::TableGet {
                                                    table_index: c.table,
                                                },
                                                &[a],
                                                &[Type::Heap(c.ty)],
                                            ),
                                        })
                                        .collect::<Vec<_>>();
                                    let tys = &src.type_pool[*list_ref1];
                                    (dst.add_op(new, operator.clone(), &args, tys), None)
                                }
                            }
                        }
                        Operator::Call { function_index }
                            if self.tables.iter().any(|x| x.tfree == *function_index) =>
                        {
                            let args = src.arg_pool[*list_ref]
                                .iter()
                                .find_map(|a| state.get_mut(a) .and_then(|(a, b)| match b {
                                    Some(c) if c.tfree == *function_index => Some({
                                        replace(a,dst.add_op(new, Operator::Call { function_index: c.talloc }, &[*a], &[Type::I32]))
                                    }),
                                    _ => None,
                                }))
                                // .cloned()
                               ;
                            // .unwrap();
                            match args {
                                Some(a) => (a, None),
                                None => {
                                    let args = src.arg_pool[*list_ref]
                                        .iter()
                                        .filter_map(|a| state.get(a))
                                        .cloned()
                                        .map(|(a, b)| match b {
                                            None => a,
                                            Some(c) => dst.add_op(
                                                new,
                                                Operator::TableGet {
                                                    table_index: c.table,
                                                },
                                                &[a],
                                                &[Type::Heap(c.ty)],
                                            ),
                                        })
                                        .collect::<Vec<_>>();
                                    let tys = &src.type_pool[*list_ref1];
                                    (dst.add_op(new, operator.clone(), &args, tys), None)
                                }
                            }
                        }
                        _ => {
                            let args = src.arg_pool[*list_ref]
                                .iter()
                                .filter_map(|a| state.get(a))
                                .cloned()
                                .map(|(a, b)| match b {
                                    None => a,
                                    Some(c) => dst.add_op(
                                        new,
                                        Operator::TableGet {
                                            table_index: c.table,
                                        },
                                        &[a],
                                        &[Type::Heap(c.ty)],
                                    ),
                                })
                                .collect::<Vec<_>>();
                            let tys = &src.type_pool[*list_ref1];
                            (dst.add_op(new, operator.clone(), &args, tys), None)
                        }
                    },
                    waffle::ValueDef::PickOutput(value, a, b) => {
                        let value = state
                            .get(value)
                            .cloned()
                            .context("in getting the referenced value")?;
                        let new_value = dst.values.push(ValueDef::PickOutput(value.0, *a, *b));
                        dst.append_to_block(new, new_value);
                        (new_value, None)
                    }
                    waffle::ValueDef::Alias(value) => state
                        .get(value)
                        .cloned()
                        .context("in getting the referenced value")?,
                    waffle::ValueDef::Placeholder(_) => todo!(),
                    waffle::ValueDef::None => (dst.add_op(new, Operator::Nop, &[], &[]), None),
                };
                state.insert(i, v);
            }
            let mut target_ = |dst: &mut FunctionBody, k: &BlockTarget| {
                let mut w = vec![];
                anyhow::Ok(BlockTarget {
                    args: k
                        .args
                        .iter()
                        .filter_map(|b| state.get(b))
                        .cloned()
                        .map(|(a, b)| {
                            w.push(b);
                            a
                        })
                        .collect(),
                    block: self.translate(dst, src, k.block, w)?,
                })
            };
            let t = match &src.blocks[k].terminator {
                waffle::Terminator::Br { target } => waffle::Terminator::Br {
                    target: target_(dst, target)?,
                },
                waffle::Terminator::CondBr {
                    cond,
                    if_true,
                    if_false,
                } => {
                    let if_true = target_(dst, if_true)?;
                    let if_false = target_(dst, if_false)?;
                    let cond = state
                        .get(cond)
                        .cloned()
                        .map(|(a, b)| match b {
                            None => a,
                            Some(c) => dst.add_op(
                                new,
                                Operator::TableGet {
                                    table_index: c.table,
                                },
                                &[a],
                                &[Type::Heap(c.ty)],
                            ),
                        })
                        .context("in getting the referenced value")?;
                    waffle::Terminator::CondBr {
                        cond,
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
                        .map(|(a, b)| match b {
                            None => a,
                            Some(c) => dst.add_op(
                                new,
                                Operator::TableGet {
                                    table_index: c.table,
                                },
                                &[a],
                                &[Type::Heap(c.ty)],
                            ),
                        })
                        .context("in getting the referenced value")?;
                    let default = target_(dst, default)?;
                    let targets = targets
                        .iter()
                        .map(|a| target_(dst, a))
                        .collect::<anyhow::Result<Vec<_>>>()?;
                    waffle::Terminator::Select {
                        value,
                        targets,
                        default,
                    }
                }
                waffle::Terminator::Return { values } => waffle::Terminator::Return {
                    values: values
                        .iter()
                        .filter_map(|b| state.get(b))
                        .cloned()
                        .map(|(a, b)| match b {
                            None => a,
                            Some(c) => dst.add_op(
                                new,
                                Operator::Call {
                                    function_index: c.tfree,
                                },
                                &[a],
                                &[Type::Heap(c.ty)],
                            ),
                        })
                        .collect(),
                },
                waffle::Terminator::ReturnCall { func, args } => waffle::Terminator::ReturnCall {
                    func: *func,
                    args: args
                        .iter()
                        .filter_map(|b| state.get(b))
                        .cloned()
                        .map(|(a, b)| match b {
                            None => a,
                            Some(c) => dst.add_op(
                                new,
                                Operator::Call {
                                    function_index: c.tfree,
                                },
                                &[a],
                                &[Type::Heap(c.ty)],
                            ),
                        })
                        .collect(),
                },
                waffle::Terminator::ReturnCallIndirect { sig, table, args } => {
                    waffle::Terminator::ReturnCallIndirect {
                        sig: *sig,
                        table: *table,
                        args: args
                            .iter()
                            .filter_map(|b| state.get(b))
                            .cloned()
                            .map(|(a, b)| match b {
                                None => a,
                                Some(c) => dst.add_op(
                                    new,
                                    Operator::Call {
                                        function_index: c.tfree,
                                    },
                                    &[a],
                                    &[Type::Heap(c.ty)],
                                ),
                            })
                            .collect(),
                    }
                }
                waffle::Terminator::ReturnCallRef { sig, args } => {
                    waffle::Terminator::ReturnCallRef {
                        sig: *sig,
                        args: args
                            .iter()
                            .filter_map(|b| state.get(b))
                            .cloned()
                            .map(|(a, b)| match b {
                                None => a,
                                Some(c) => dst.add_op(
                                    new,
                                    Operator::Call {
                                        function_index: c.tfree,
                                    },
                                    &[a],
                                    &[Type::Heap(c.ty)],
                                ),
                            })
                            .collect(),
                    }
                }
                waffle::Terminator::Unreachable => waffle::Terminator::Unreachable,
                _ => waffle::Terminator::None,
            };
            dst.set_terminator(new, t);
        });
    }
}

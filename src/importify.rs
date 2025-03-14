use std::{
    collections::BTreeMap,
    default,
    mem::{replace, take},
    sync::{atomic::AtomicUsize, Arc},
};

use anyhow::Context;

use waffle::{
    cfg::CFGInfo,
    passes::{basic_opt::value_is_pure, tcore::results_ref_2},
    util::new_sig,
    Block, BlockTarget, Export, Func, FunctionBody, Import, ImportKind, Module, Operator, Type,
    Value, ValueDef,
};
fn manifest_of(m: &Module, src: &FunctionBody, k: Block) -> BTreeMap<Value, (String, Vec<Type>)> {
    return src.blocks[k]
        .insts
        .iter()
        .cloned()
        .filter_map(|a| {
            let ValueDef::Operator(Operator::Call { function_index }, _, types) = &src.values[a]
            else {
                return None;
            };
            let function_index = *function_index;
            for i in m.imports.iter() {
                if i.module == "importify" {
                    if i.kind == ImportKind::Func(function_index) {
                        return Some((a, (i.name.clone(), src.type_pool[*types].to_owned())));
                    }
                }
            }
            None
        })
        .collect();
}
#[derive(Default)]
pub struct Importify {
    blocks: BTreeMap<Block, Block>,
    manifest: BTreeMap<Value, (String, Vec<Type>)>,
    funcs: Arc<once_map::OnceMap<Block, Box<Func>>>,
    ids: Arc<AtomicUsize>,
}
impl Importify {
    pub fn to_ids(self) -> Arc<AtomicUsize>{
        self.ids
    }
    pub fn new(ids: Arc<AtomicUsize>) -> Self {
        Self {
            blocks: Default::default(),
            manifest: Default::default(),
            funcs: Default::default(),
            ids: ids,
        }
    }
    pub fn translate_f(
        &mut self,
        module: &mut Module,
        // dst: &mut FunctionBody,
        src: &FunctionBody,
        k: Block,
    ) -> anyhow::Result<Func> {
        self.funcs
            .try_insert(k, |k| {
                let k = *k;
                let sig = new_sig(
                    module,
                    waffle::SignatureData::Func {
                        params: manifest_of(&module, src, k)
                            .values()
                            .map(|a| &a.1)
                            .flatten()
                            .cloned()
                            .chain(src.blocks[k].params.iter().map(|a| a.0))
                            .collect(),
                        returns: src.rets.clone(),
                    },
                );
                let mut dst = FunctionBody::new(module, sig);
                dst.entry = Importify {
                    blocks: Default::default(),
                    manifest: manifest_of(&module, src, k),
                    funcs: self.funcs.clone(),
                    ids: self.ids.clone(),
                }
                .translate(module, &mut dst, src, k)?;
                dst.recompute_edges();
                anyhow::Ok(Box::new(module.funcs.push(waffle::FuncDecl::Body(
                    sig,
                    format!("synthetic import/export"),
                    dst,
                ))))
            })
            .map(|a| *a)
    }
    pub fn translate(
        &mut self,
        module: &mut Module,
        dst: &mut FunctionBody,
        src: &FunctionBody,
        k: Block,
    ) -> anyhow::Result<Block> {
        return stacker::maybe_grow(32 * 1024, 1024 * 1024, move || loop {
            if let Some(l) = self.blocks.get(&k) {
                return Ok(*l);
            }
            let new = dst.add_block();
            if self.manifest.is_empty() && !manifest_of(&module, src, k).is_empty() {
                let vals = src.blocks[k].params.iter().map(|a| a.0).collect::<Vec<_>>();
                let vtys = vals
                    .iter()
                    .cloned()
                    .map(|a| dst.add_blockparam(new, a))
                    .collect();
                let proper = self.translate_f(module, src, k)?;
                let mut chain = proper;
                let mut m2 = manifest_of(&module, src, k);
                loop {
                    let Some((_, (ky, ts))) = m2.pop_first() else {
                        break;
                    };
                    let siga = new_sig(
                        module,
                        waffle::SignatureData::Func {
                            params: m2
                                .values()
                                .map(|a| &a.1)
                                .flatten()
                                .cloned()
                                .chain(src.blocks[k].params.iter().map(|a| a.0))
                                .collect(),
                            returns: src.rets.clone(),
                        },
                    );
                    let i = module
                        .funcs
                        .push(waffle::FuncDecl::Import(siga, format!("{ky}/import")));
                    let n = self.ids.fetch_and(1, std::sync::atomic::Ordering::SeqCst);
                    let n = format!("{n}");
                    module.imports.push(Import {
                        module: ky,
                        name: n.clone(),
                        kind: ImportKind::Func(i),
                    });
                    let x = replace(&mut chain, i);
                    module.exports.push(Export {
                        name: n,
                        kind: waffle::ExportKind::Func(x),
                    });
                }
                dst.set_terminator(
                    k,
                    waffle::Terminator::ReturnCall {
                        func: chain,
                        args: vtys,
                    },
                );
                self.blocks.insert(k, new);
                continue;
            }
            let mut manifest = take(&mut self.manifest)
                .into_iter()
                .map(|(a, (b, c))| {
                    (
                        a,
                        (
                            b,
                            c.into_iter()
                                .map(|d| dst.add_blockparam(new, d))
                                .collect::<Vec<_>>(),
                        ),
                    )
                })
                .collect::<BTreeMap<_, _>>();
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
                let v = match manifest.remove(&i) {
                    None => match &src.values[i] {
                        waffle::ValueDef::BlockParam(block, _, _) => todo!(),
                        waffle::ValueDef::Operator(operator, list_ref, list_ref1) => {
                            let args = src.arg_pool[*list_ref]
                                .iter()
                                .filter_map(|a| state.get(a))
                                .flatten()
                                .cloned()
                                .collect::<Vec<_>>();
                            let tys = &src.type_pool[*list_ref1];
                            let c = dst.add_op(new, operator.clone(), &args, tys);
                            results_ref_2(dst, c)
                        }
                        waffle::ValueDef::PickOutput(value, a, b) => {
                            let value = state
                                .get(value)
                                .cloned()
                                .context("in getting the referenced value")?;
                            vec![value[*a as usize]]
                        }
                        waffle::ValueDef::Alias(value) => state
                            .get(value)
                            .cloned()
                            .context("in getting the referenced value")?,
                        waffle::ValueDef::Placeholder(_) => todo!(),
                        waffle::ValueDef::None => vec![],
                    },
                    Some((n, vs)) => vs,
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
                waffle::Terminator::Return { values } => waffle::Terminator::Return {
                    values: values
                        .iter()
                        .filter_map(|b| state.get(b))
                        .flatten()
                        .cloned()
                        .collect(),
                },
                waffle::Terminator::ReturnCall { func, args } => waffle::Terminator::ReturnCall {
                    func: *func,
                    args: args
                        .iter()
                        .filter_map(|b| state.get(b))
                        .flatten()
                        .cloned()
                        .collect(),
                },
                waffle::Terminator::ReturnCallIndirect { sig, table, args } => {
                    waffle::Terminator::ReturnCallIndirect {
                        sig: *sig,
                        table: *table,
                        args: args
                            .iter()
                            .filter_map(|b| state.get(b))
                            .flatten()
                            .cloned()
                            .collect(),
                    }
                }
                waffle::Terminator::ReturnCallRef { sig, args } => {
                    waffle::Terminator::ReturnCallRef {
                        sig: *sig,
                        args: args
                            .iter()
                            .filter_map(|b| state.get(b))
                            .flatten()
                            .cloned()
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

use once_map::OnceMap;
use std::{
    collections::BTreeMap,
    iter::once,
    mem::{replace, take},
};
use waffle::{
    BlockTarget, ExportKind, Func, FuncDecl, FunctionBody, Global, GlobalData, HeapType,
    ImportKind, Memory, Module, Operator, Table, TableData, Type, WithNullable,
};
use waffle_ast::tutils::{talloc, tfree};
pub mod bulk_memory_lowering;
#[cfg(feature = "corpack")]
pub mod corpack;
pub fn init_with(module: &mut Module, init: Func) {
    let idg = module.globals.push(GlobalData {
        ty: Type::I32,
        mutable: true,
        value: Some(1),
    });
    for fi in module
        .funcs
        .iter()
        .filter(|f| {
            module
                .imports
                .iter()
                .filter_map(|a| match &a.kind {
                    ImportKind::Func(f) => Some(f),
                    _ => None,
                })
                .all(|g| *g != *f)
        })
        // .filter(|a| funcs.contains(a))
        .collect::<Vec<_>>()
    {
        // let mut f = take(&mut module.funcs[fi]);
        // if let Some(f) = f.body_mut() {
        with_swizz(module, fi, |(module, f, fi)| {
            let new = f.add_block();
            let params = f.blocks[f.entry]
                .params
                .iter()
                .map(|a| a.0)
                .collect::<Vec<_>>();
            let params = params
                .into_iter()
                .map(|a| f.add_blockparam(new, a))
                .collect::<Vec<_>>();
            let old = f.add_block();
            let id = f.add_op(
                f.entry,
                Operator::GlobalGet { global_index: idg },
                &[],
                &[Type::I32],
            );
            let fix = f.add_block();
            f.set_terminator(
                f.entry,
                waffle::Terminator::CondBr {
                    cond: id,
                    if_true: BlockTarget {
                        block: fix,
                        args: vec![],
                    },
                    if_false: BlockTarget {
                        block: old,
                        args: params.clone(),
                    },
                },
            );
            let id = f.add_op(fix, Operator::I32Const { value: 0 }, &[], &[Type::I32]);
            f.add_op(fix, Operator::GlobalSet { global_index: idg }, &[id], &[]);
            f.add_op(
                fix,
                Operator::Call {
                    function_index: init,
                },
                &[],
                &[],
            );
            // let retvals = f
            //     .rets
            //     .clone()
            //     .into_iter()
            //     .map(|a| default_val(a, f, fix))
            //     .collect();
            f.set_terminator(
                fix,
                waffle::Terminator::Br {
                    target: BlockTarget {
                        block: f.entry,
                        args: params,
                    },
                },
            );
            let params = f.blocks[f.entry]
                .params
                .iter()
                .map(|a| a.0)
                .collect::<Vec<_>>();
            let params = params
                .into_iter()
                .map(|p| f.add_blockparam(old, p))
                .collect();
            f.set_terminator(
                old,
                waffle::Terminator::ReturnCall {
                    func: fi,
                    args: params,
                },
            );
        });
        // }

        // module.funcs[fi] = f;
    }
    // Ok(())
}

#[derive(Default)]
pub struct TableMap {
    tables: OnceMap<WithNullable<HeapType>, Box<(Table, Func, Func)>>,
}
impl TableMap {
    pub fn table_in(&self, module: &mut Module, ty: WithNullable<HeapType>) -> (Table, Func, Func) {
        let (t, alloc, free) = self.tables.insert(ty, |ty| {
            Box::new({
                let t = module.tables.push(TableData {
                    ty: Type::Heap(ty.clone()),
                    initial: 0,
                    max: None,
                    func_elements: None,
                    table64: false,
                });
                (
                    t,
                    talloc(module, t, &[]).unwrap(),
                    tfree(module, t, &[]).unwrap(),
                )
            })
        });
        (*t, *alloc, *free)
    }
}

pub fn ift(module: &Module) -> Option<Table> {
    module.exports.iter().find_map(|x| {
        if x.name == "__indirect_function_table" {
            match &x.kind {
                ExportKind::Table(t) => Some(*t),
                _ => None,
            }
        } else {
            None
        }
    })
}

pub fn memory(module: &Module) -> Option<Memory> {
    module.exports.iter().find_map(|x| {
        if x.name == "memory" {
            match &x.kind {
                ExportKind::Memory(t) => Some(*t),
                _ => None,
            }
        } else {
            None
        }
    })
}

pub fn with_swizz<R>(
    module: &mut Module,
    f: Func,
    shim: impl FnOnce((&mut Module, &mut FunctionBody, Func)) -> R,
) -> R {
    let sig = module.funcs[f].sig();
    let name = module.funcs[f].name().to_owned();
    let g = replace(
        &mut module.funcs[f],
        waffle::FuncDecl::Import(sig, name.clone()),
    );
    let g = module.funcs.push(g);
    for i in module.imports.iter_mut() {
        if let ImportKind::Func(i) = &mut i.kind {
            if *i == f {
                *i = g;
            }
        }
    }
    let mut dst = FunctionBody::new(module, sig);
    let r = shim((module, &mut dst, g));
    module.funcs[f] = FuncDecl::Body(sig, name, dst);
    return r;
}
#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub enum Cond {
    Func{
        func: Func,
        pass_args: bool,
    },
    // ViaTable { table: Table, dispatch: Func },
}
pub fn guard_table(module: &mut Module, f: Func, table: Table) -> Global {
    with_swizz(module, f, |(module, b, f)| {
        let idx = need(module, table, f);
        let ty = if module.tables[table].table64 {
            Type::I64
        } else {
            Type::I32
        };
        let g = module.globals.push(GlobalData {
            ty: ty.clone(),
            value: Some(idx as u64),
            mutable: true,
        });
        let gv = b.add_op(
            b.entry,
            Operator::GlobalGet { global_index: g },
            &[],
            &[ty.clone()],
        );
        let mut p = b.blocks[b.entry]
            .params
            .iter()
            .map(|p| p.1)
            .collect::<Vec<_>>();
        p.push(gv);
        b.set_terminator(
            b.entry,
            waffle::Terminator::ReturnCallIndirect {
                sig: module.funcs[f].sig(),
                table: table,
                args: p,
            },
        );
        return g;
    })
}
#[derive(Default)]
pub struct GuardMap {
    all: OnceMap<(Func, Table), Box<Global>>,
}
impl GuardMap {
    pub fn guard(&self, module: &mut Module, f: Func, t: Table) -> Global {
        return *self
            .all
            .insert((f, t), |_| Box::new(guard_table(module, f, t)));
    }
}
pub fn swap_fns(module: &mut Module, a: Func, b: Func, cond: Option<Cond>) {
    if a == b {
        return;
    }
    with_swizz(module, a, |(module, ab, a)| {
        with_swizz(module, b, |(module, bb, b)| {
            let (a, b) = (b, a);
            for (x, b, y) in [(a, ab, b), (b, bb, a)] {
                let p = b.blocks[b.entry].params.iter().map(|a| a.1).collect();
                match cond {
                    None => {
                        b.set_terminator(
                            b.entry,
                            waffle::Terminator::ReturnCall { func: x, args: p },
                        );
                    }
                    Some(cond) => match cond {
                        Cond::Func{func: cond, pass_args} => {
                            let [xb, yb] = [x, y].map(|f| {
                                let k = b.add_block();
                                b.set_terminator(
                                    k,
                                    waffle::Terminator::ReturnCall {
                                        func: f,
                                        args: p.clone(),
                                    },
                                );
                                BlockTarget {
                                    block: k,
                                    args: vec![],
                                }
                            });
                            let cond = b.add_op(
                                b.entry,
                                Operator::Call {
                                    function_index: cond,
                                },
                                if pass_args{&p}else{&[]},
                                &[Type::I32],
                            );
                            b.set_terminator(
                                b.entry,
                                waffle::Terminator::CondBr {
                                    cond: cond,
                                    if_true: xb,
                                    if_false: yb,
                                },
                            );
                        }
                    },
                }
            }
        })
    })
}
pub fn guard_fn(module: &mut Module, x: Func, y: Func, cond: Option<Cond>) {
    with_swizz(module, x, |(module, b, x)| {
        let p = b.blocks[b.entry].params.iter().map(|a| a.1).collect();
        match cond {
            None => {
                b.set_terminator(b.entry, waffle::Terminator::ReturnCall { func: x, args: p });
            }
            Some(cond) => match cond {
                Cond::Func{func: cond, pass_args} => {
                    let [xb, yb] = [x, y].map(|f| {
                        let k = b.add_block();
                        b.set_terminator(
                            k,
                            waffle::Terminator::ReturnCall {
                                func: f,
                                args: p.clone(),
                            },
                        );
                        BlockTarget {
                            block: k,
                            args: vec![],
                        }
                    });
                    let cond = b.add_op(
                        b.entry,
                        Operator::Call {
                            function_index: cond,
                        },
                        if pass_args{&p}else{&[]},
                        &[Type::I32],
                    );
                    b.set_terminator(
                        b.entry,
                        waffle::Terminator::CondBr {
                            cond: cond,
                            if_true: xb,
                            if_false: yb,
                        },
                    );
                }
            },
        }
    })
}
pub fn replace_fns(
    module: &mut Module,
    f: impl Iterator<Item = Func>,
    mut a: Func,
    cond: Option<Cond>,
) -> Func {
    for f in f {
        a = with_swizz(module, f, |(module, b, x)| {
            let (x, a) = (a, x);

            let p = b.blocks[b.entry].params.iter().map(|a| a.1).collect();
            match cond {
                None => {
                    b.set_terminator(b.entry, waffle::Terminator::ReturnCall { func: x, args: p });
                }
                Some(cond) => match cond {
                    Cond::Func{func: cond, pass_args} => {
                        let [xb, yb] = [x, a].map(|f| {
                            let k = b.add_block();
                            b.set_terminator(
                                k,
                                waffle::Terminator::ReturnCall {
                                    func: f,
                                    args: p.clone(),
                                },
                            );
                            BlockTarget {
                                block: k,
                                args: vec![],
                            }
                        });
                        let cond = b.add_op(
                            b.entry,
                            Operator::Call {
                                function_index: cond,
                            },
                            if pass_args{&p}else{&[]},
                            &[Type::I32],
                        );
                        b.set_terminator(
                            b.entry,
                            waffle::Terminator::CondBr {
                                cond: cond,
                                if_true: xb,
                                if_false: yb,
                            },
                        );
                    }
                },
            }

            return a;
        });
    }

    return a;
}
pub fn loop_fns(module: &mut Module, mut a: impl Iterator<Item = Func>, cond: Option<Cond>) {
    if let Some(b) = a.next() {
        let c = replace_fns(module, a, b, cond);
        swap_fns(module, c, b, cond);
    }
}
pub fn need(module: &mut Module, table: Table, x: Func) -> usize {
    let tab = module.tables[table].func_elements.as_mut().unwrap();
    for (idx, y) in tab.iter().enumerate() {
        if *y == x {
            return idx;
        }
    }
    let idx = tab.len();
    tab.push(x);
    return idx;
}

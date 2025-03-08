use waffle::{
    passes::tcore::results_ref_2, util::new_sig, Block, MemoryArg, Signature, SignatureData, Value,
};

use crate::*;

pub fn ser(
    dst: &mut FunctionBody,
    module: &mut Module,
    t: &TableMap,
    mem: Memory,
    input: Value,
    k: Block,
    state: &mut u64,
    base: Value,
) {
    let input = match dst.values[input].ty(&dst.type_pool) {
        Some(Type::Heap(h)) => {
            let TableInfo {
                table,
                talloc,
                tfree,
                ..
            } = t.table_in(module, h);
            dst.add_op(
                k,
                Operator::Call {
                    function_index: talloc,
                },
                &[input],
                &[Type::I32],
            )
        }
        _ => input,
    };
    dst.add_op(
        k,
        match dst.values[input].ty(&dst.type_pool).unwrap() {
            Type::I32 => Operator::I32Store {
                memory: MemoryArg {
                    align: 0,
                    offset: *state,
                    memory: mem,
                },
            },
            Type::I64 => Operator::I64Store {
                memory: MemoryArg {
                    align: 0,
                    offset: *state,
                    memory: mem,
                },
            },
            Type::F32 => Operator::F32Store {
                memory: MemoryArg {
                    align: 0,
                    offset: *state,
                    memory: mem,
                },
            },
            Type::F64 => Operator::F64Store {
                memory: MemoryArg {
                    align: 0,
                    offset: *state,
                    memory: mem,
                },
            },

            _ => todo!(),
        },
        &[base, input],
        &[],
    );
    *state += match dst.values[input].ty(&dst.type_pool).unwrap() {
        Type::I32 => 4,
        Type::I64 => 8,
        Type::F32 => 4,
        Type::F64 => 8,

        _ => todo!(),
    };
}
pub fn des(
    dst: &mut FunctionBody,
    module: &mut Module,
    t: &TableMap,
    mem: Memory,
    input: Type,
    k: Block,
    state: &mut u64,
    base: Value,
) -> Value {
    // let input = match dst.values[input].ty(&dst.type_pool){
    //     Some(Type::Heap(h)) => {
    //         let (table,talloc,tfree) = t.table_in(module,h);
    //         dst.add_op(k,Operator::Call { function_index: talloc },&[input],&[Type::I32])
    //     },
    //     _ => input,
    // };
    let ret = dst.add_op(
        k,
        match &input {
            Type::I32 | Type::Heap(_) => Operator::I32Load {
                memory: MemoryArg {
                    align: 0,
                    offset: *state,
                    memory: mem,
                },
            },
            Type::I64 => Operator::I64Load {
                memory: MemoryArg {
                    align: 0,
                    offset: *state,
                    memory: mem,
                },
            },
            Type::F32 => Operator::F32Load {
                memory: MemoryArg {
                    align: 0,
                    offset: *state,
                    memory: mem,
                },
            },
            Type::F64 => Operator::F64Load {
                memory: MemoryArg {
                    align: 0,
                    offset: *state,
                    memory: mem,
                },
            },

            _ => todo!(),
        },
        &[base],
        &[match input.clone() {
            Type::Heap(_) => Type::I32,
            x => x,
        }],
    );
    *state += match &input {
        Type::I32 | Type::Heap(_) => 4,
        Type::I64 => 8,
        Type::F32 => 4,
        Type::F64 => 8,

        _ => todo!(),
    };
    let ret = match &input {
        Type::Heap(h) => {
            let TableInfo {
                table,
                talloc,
                tfree,
                ..
            } = t.table_in(module, h.clone());
            dst.add_op(
                k,
                Operator::Call {
                    function_index: tfree,
                },
                &[ret],
                &[input],
            )
        }
        _ => ret,
    };
    return ret;
}
pub fn new_serdes(
    module: &mut Module,
    t: &TableMap,
    mem: Memory,
    sig: Signature,
    bump: Func,
    send: Func,
    fin: Func,
    id: u64,
) -> Func {
    let mut dst = FunctionBody::new(module, sig);
    let idxtype = if module.memories[mem].memory64 {
        Type::I64
    } else {
        Type::I32
    };
    let base = dst.blocks[dst.entry]
        .params
        .iter()
        .map(|a| &a.0)
        .chain(dst.rets.iter())
        .map(|t| match t {
            Type::I64 | Type::F64 => 8,
            _ => 4,
        })
        .sum();
    let base = dst.add_op(
        dst.entry,
        Operator::I64Const { value: base },
        &[],
        &[Type::I64],
    );
    let base = dst.add_op(
        dst.entry,
        Operator::Call {
            function_index: bump,
        },
        &[base],
        &[idxtype],
    );
    let mut state = 0;
    let k = dst.entry;
    for param in dst.blocks[dst.entry]
        .params
        .iter()
        .map(|a| a.1)
        .collect::<Vec<_>>()
    {
        ser(&mut dst, module, t, mem, param, k, &mut state, base);
    }
    let [idi, si] = [id, state].map(|u| {
        dst.add_op(
            dst.entry,
            Operator::I64Const { value: u },
            &[],
            &[Type::I64],
        )
    });
    dst.add_op(
        dst.entry,
        Operator::Call {
            function_index: send,
        },
        &[base, idi, si],
        &[],
    );
    let rets = dst
        .rets
        .clone()
        .into_iter()
        .map(|r| des(&mut dst, module, t, mem, r, k, &mut state, base))
        .collect();
    dst.add_op(
        dst.entry,
        Operator::Call {
            function_index: fin,
        },
        &[base],
        &[],
    );
    dst.set_terminator(dst.entry, waffle::Terminator::Return { values: rets });
    return module
        .funcs
        .push(FuncDecl::Body(sig, format!("~serdes"), dst));
}
pub fn desser(
    dst: &mut FunctionBody,
    module: &mut Module,
    t: &TableMap,
    mem: Memory,
    f: Func,
    k: Block,
    state: &mut u64,
    base: Value,
) -> u64 {
    let SignatureData::Func { params, returns } = module.signatures[module.funcs[f].sig()].clone()
    else {
        return *state;
    };
    let args = params
        .into_iter()
        .map(|r| des(dst, module, t, mem, r, k, state, base))
        .collect::<Vec<_>>();
    let ps = *state;
    let v = dst.add_op(k, Operator::Call { function_index: f }, &args, &returns);
    let v = results_ref_2(dst, v);
    for v in v {
        ser(dst, module, t, mem, v, k, state, base);
    }
    return ps;
}
pub fn new_desser(module: &mut Module, t: &TableMap, mem: Memory, f: Func) -> Func {
    let idxtype = if module.memories[mem].memory64 {
        Type::I64
    } else {
        Type::I32
    };
    let sig = new_sig(
        module,
        SignatureData::Func {
            params: vec![idxtype.clone(), idxtype.clone()],
            returns: vec![Type::I64],
        },
    );
    let mut dst = FunctionBody::new(module, sig);
    let done = dst.add_block();
    let base = dst.blocks[dst.entry].params[0].1;
    let psi = dst.blocks[dst.entry].params[1].1;
    let new = dst.add_block();
    let baz = if module.memories[mem].memory64 {
        Operator::I64Eqz
    } else {
        Operator::I32Eqz
    };
    let baz = dst.add_op(dst.entry, baz, &[base], &[Type::I32]);
    dst.set_terminator(
        dst.entry,
        waffle::Terminator::CondBr {
            cond: baz,
            if_true: BlockTarget {
                block: done,
                args: vec![],
            },
            if_false: BlockTarget {
                block: new,
                args: vec![],
            },
        },
    );
    let mut state = 0;
    let ps = desser(&mut dst, module, t, mem, f, new, &mut state, base);
    dst.set_terminator(
        new,
        waffle::Terminator::Br {
            target: BlockTarget {
                block: done,
                args: vec![],
            },
        },
    );
    let state = dst.add_op(done, Operator::I64Const { value: state }, &[], &[Type::I64]);
    let ps = dst.add_op(done, Operator::I64Const { value: ps }, &[], &[Type::I64]);
    dst.add_op(
        done,
        Operator::I64Store {
            memory: MemoryArg {
                align: 0,
                offset: 0,
                memory: mem,
            },
        },
        &[psi, ps],
        &[],
    );
    dst.set_terminator(
        done,
        waffle::Terminator::Return {
            values: vec![state],
        },
    );
    return module
        .funcs
        .push(FuncDecl::Body(sig, format!("~desser"), dst));
}
#[derive(Default)]
pub struct SerCache {
    desser: OnceMap<Func, Box<Func>>,
    serdes: OnceMap<(Signature, Func, Func, Func, u64), Box<Func>>,
}
impl SerCache {
    pub fn new_desser(&self, module: &mut Module, t: &TableMap, mem: Memory, f: Func) -> Func {
        return *self
            .desser
            .insert(f, |_| Box::new(new_desser(module, t, mem, f)));
    }
    pub fn new_serdes(
        &self,
        module: &mut Module,
        t: &TableMap,
        mem: Memory,
        sig: Signature,
        bump: Func,
        send: Func,
        fin: Func,
        id: u64,
    ) -> Func {
        return *self.serdes.insert((sig, bump, send, fin, id), |_| {
            Box::new(new_serdes(module, t, mem, sig, bump, send, fin, id))
        });
    }
}

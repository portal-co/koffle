use std::collections::BTreeMap;

use anyhow::Context;
use waffle::{
    util::new_sig, Block, BlockTarget, Func, FunctionBody, Memory, MemoryArg, Module, Operator,
    SignatureData, Type,
};

use waffle_ast::{
    add_op,
    fcopy::{obf_mod, DontObf, Obfuscate},
    Builder, Expr,
};

#[derive(Default, Clone, Copy)]
pub struct Reload<T, F> {
    pub wrapped: T,
    pub predicate: F,
}
impl<T: Obfuscate, F: FnMut(Memory) -> bool> Reload<T, F> {
    fn store(
        &mut self,
        o: usize,
        memory: &MemoryArg,
        f: &mut waffle::FunctionBody,
        b: waffle::Block,
        args: &[waffle::Value],
        types: &[waffle::Type],
        module: &mut Module,
    ) -> anyhow::Result<(waffle::Value, waffle::Block)> {
        let r = f.values[args[0]].ty(&f.type_pool).unwrap();
        let r2 = f.values[args[1]].ty(&f.type_pool).unwrap();
        if o == 1 {
            return self.obf(
                match r2 {
                    Type::I32 => Operator::I32Store8 {
                        memory: memory.clone(),
                    },
                    Type::I64 => Operator::I64Store8 {
                        memory: memory.clone(),
                    },
                    _ => anyhow::bail!("nop!"),
                },
                f,
                b,
                args,
                types,
                module,
            );
        }
        let (a, b) = self.obf(
            match r2 {
                Type::I32 => Operator::I32Const { value: 0xff },
                Type::I64 => Operator::I64Const { value: 0xff },
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[],
            &[r2],
            module,
        )?;
        let (a, b) = self.obf(
            match r2 {
                Type::I32 => Operator::I32And,
                Type::I64 => Operator::I64And,
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[args[1], a],
            &[r2],
            module,
        )?;
        let (_, b) = self.obf(
            match r2 {
                Type::I32 => Operator::I32Store8 {
                    memory: memory.clone(),
                },
                Type::I64 => Operator::I64Store8 {
                    memory: memory.clone(),
                },
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[args[0], a],
            types,
            module,
        )?;
        let (a, b) = self.obf(
            match r2 {
                Type::I32 => Operator::I32Const { value: 8 },
                Type::I64 => Operator::I64Const { value: 8 },
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[],
            &[r2],
            module,
        )?;
        let (c, b) = self.obf(
            match r2 {
                Type::I32 => Operator::I32ShrU,
                Type::I64 => Operator::I64ShrU,
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[args[1], a],
            &[r2],
            module,
        )?;
        let (a, b) = self.obf(
            match r {
                Type::I32 => Operator::I32Const { value: 1 },
                Type::I64 => Operator::I64Const { value: 1 },
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[],
            &[r],
            module,
        )?;
        let (a, b) = self.obf(
            match r {
                Type::I32 => Operator::I32Add,
                Type::I64 => Operator::I64Add,
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[args[0], a],
            &[r],
            module,
        )?;
        return self.store(o - 1, memory, f, b, &[a, c], types, module);
    }
    fn load(
        &mut self,
        o: usize,
        memory: &MemoryArg,
        f: &mut waffle::FunctionBody,
        b: waffle::Block,
        args: &[waffle::Value],
        types: &[waffle::Type],
        module: &mut Module,
    ) -> anyhow::Result<(waffle::Value, waffle::Block)> {
        let r = f.values[args[0]].ty(&f.type_pool).unwrap();
        if o == 0 {
            return self.obf(
                match types[0] {
                    Type::I32 => Operator::I32Const { value: 0 },
                    Type::I64 => Operator::I64Const { value: 0 },
                    _ => anyhow::bail!("nop!"),
                },
                f,
                b,
                args,
                types,
                module,
            );
        }
        if o == 1 {
            return self.obf(
                match types[0] {
                    Type::I32 => Operator::I32Load8U {
                        memory: memory.clone(),
                    },
                    Type::I64 => Operator::I64Load8U {
                        memory: memory.clone(),
                    },
                    _ => anyhow::bail!("nop!"),
                },
                f,
                b,
                args,
                types,
                module,
            );
        }
        let (first, b) = self.obf(
            match types[0] {
                Type::I32 => Operator::I32Load8U {
                    memory: memory.clone(),
                },
                Type::I64 => Operator::I64Load8U {
                    memory: memory.clone(),
                },
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            args,
            types,
            module,
        )?;
        let (n, b) = self.obf(
            match r {
                Type::I32 => Operator::I32Const { value: 1 },
                Type::I64 => Operator::I64Const { value: 1 },
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[],
            &[r],
            module,
        )?;
        let (n, b) = self.obf(
            match types[0] {
                Type::I32 => Operator::I32Add,
                Type::I64 => Operator::I64Add,
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[args[0], n],
            &[r],
            module,
        )?;
        let (second, b) = self.load(o - 1, memory, f, b, &[n], types, module)?;
        let (n, b) = self.obf(
            Operator::I32Const { value: 8 },
            f,
            b,
            &[],
            &[Type::I32],
            module,
        )?;
        let (m, b) = self.obf(
            match types[0] {
                Type::I32 => Operator::I32Shl,
                Type::I64 => Operator::I64Shl,
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[second, n],
            types,
            module,
        )?;
        return self.obf(
            match types[0] {
                Type::I32 => Operator::I32Add,
                Type::I64 => Operator::I64Add,
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[m, first],
            types,
            module,
        );
    }
}
impl<T: Obfuscate, F: FnMut(Memory) -> bool> Obfuscate for Reload<T, F> {
    fn boot(
        &mut self,
        b: waffle::Block,
        f: &mut waffle::FunctionBody,
    ) -> anyhow::Result<waffle::Block> {
        return self.wrapped.boot(b, f);
    }
    fn obf_term(
        &mut self,
        t: waffle::Terminator,
        b: waffle::Block,
        f: &mut waffle::FunctionBody,
    ) -> anyhow::Result<()> {
        return self.wrapped.obf_term(t, b, f);
    }
    fn sig(&mut self, a: waffle::SignatureData) -> anyhow::Result<waffle::SignatureData> {
        return self.wrapped.sig(a);
    }
    fn obf(
        &mut self,
        o: waffle::Operator,
        f: &mut waffle::FunctionBody,
        b: waffle::Block,
        args: &[waffle::Value],
        types: &[waffle::Type],
        module: &mut Module,
    ) -> anyhow::Result<(waffle::Value, waffle::Block)> {
        if let Some(m) = waffle::op_traits::memory_arg(&o) {
            if !(self.predicate)(m.memory) {
                return self.wrapped.obf(o, f, b, args, types, module);
            }
        }
        match &o {
            //Signed operations
            Operator::I32Load8S { memory } => {
                let (unsigned, b) = self.obf(
                    Operator::I32Load8U {
                        memory: memory.clone(),
                    },
                    f,
                    b,
                    args,
                    types,
                    module,
                )?;
                let (signed, b) =
                    self.obf(Operator::I32Extend8S, f, b, &[unsigned], types, module)?;
                return Ok((signed, b));
            }
            Operator::I64Load8S { memory } => {
                let (unsigned, b) = self.obf(
                    Operator::I64Load8U {
                        memory: memory.clone(),
                    },
                    f,
                    b,
                    args,
                    types,
                    module,
                )?;
                let (signed, b) =
                    self.obf(Operator::I64Extend8S, f, b, &[unsigned], types, module)?;
                return Ok((signed, b));
            }
            Operator::I32Load16S { memory } => {
                let (unsigned, b) = self.obf(
                    Operator::I32Load16U {
                        memory: memory.clone(),
                    },
                    f,
                    b,
                    args,
                    types,
                    module,
                )?;
                let (signed, b) =
                    self.obf(Operator::I32Extend16S, f, b, &[unsigned], types, module)?;
                return Ok((signed, b));
            }
            Operator::I64Load16S { memory } => {
                let (unsigned, b) = self.obf(
                    Operator::I64Load16U {
                        memory: memory.clone(),
                    },
                    f,
                    b,
                    args,
                    types,
                    module,
                )?;
                let (signed, b) =
                    self.obf(Operator::I64Extend16S, f, b, &[unsigned], types, module)?;
                return Ok((signed, b));
            }
            Operator::I64Load32S { memory } => {
                let (unsigned, b) = self.obf(
                    Operator::I64Load32U {
                        memory: memory.clone(),
                    },
                    f,
                    b,
                    args,
                    types,
                    module,
                )?;
                let (signed, b) =
                    self.obf(Operator::I64Extend32S, f, b, &[unsigned], types, module)?;
                return Ok((signed, b));
            }
            //Unsigned loads
            Operator::I32Load16U { memory } => {
                return self.load(2, memory, f, b, args, types, module);
            }
            Operator::I64Load16U { memory } => {
                return self.load(2, memory, f, b, args, types, module);
            }
            Operator::I32Load { memory } => {
                return self.load(4, memory, f, b, args, types, module);
            }
            Operator::I64Load32U { memory } => {
                return self.load(4, memory, f, b, args, types, module);
            }
            Operator::I64Load { memory } => {
                return self.load(8, memory, f, b, args, types, module);
            }
            //Unsigned stores
            Operator::I32Store16 { memory } => {
                return self.store(2, memory, f, b, args, types, module);
            }
            Operator::I64Store16 { memory } => {
                return self.store(2, memory, f, b, args, types, module);
            }
            Operator::I32Store { memory } => {
                return self.store(4, memory, f, b, args, types, module);
            }
            Operator::I64Store32 { memory } => {
                return self.store(4, memory, f, b, args, types, module);
            }
            Operator::I64Store { memory } => {
                return self.store(8, memory, f, b, args, types, module);
            }
            //Float loads
            Operator::F32Load { memory } => {
                let (a, b) = self.load(4, memory, f, b, args, &[Type::I32], module)?;
                return self.obf(Operator::F32ReinterpretI32, f, b, &[a], types, module);
            }
            Operator::F64Load { memory } => {
                let (a, b) = self.load(8, memory, f, b, args, &[Type::I64], module)?;
                return self.obf(Operator::F64ReinterpretI64, f, b, &[a], types, module);
            }
            //Float stores
            Operator::F32Store { memory } => {
                let (a, b) = self.obf(
                    Operator::I32ReinterpretF32,
                    f,
                    b,
                    args,
                    &[Type::I32],
                    module,
                )?;
                return self.store(4, memory, f, b, &[a], types, module);
            }
            Operator::F64Store { memory } => {
                let (a, b) = self.obf(
                    Operator::I64ReinterpretF64,
                    f,
                    b,
                    args,
                    &[Type::I64],
                    module,
                )?;
                return self.store(8, memory, f, b, &[a], types, module);
            }
            //64 Bit Ops
            Operator::I64Load8U { memory } => {
                let (a, b) = self.obf(
                    Operator::I32Load8U {
                        memory: memory.clone(),
                    },
                    f,
                    b,
                    args,
                    &[Type::I32],
                    module,
                )?;
                return self.obf(Operator::I64ExtendI32U, f, b, &[a], types, module);
            }
            Operator::I64Store8 { memory } => {
                let (a, b) =
                    self.obf(Operator::I32WrapI64, f, b, &[args[1]], &[Type::I32], module)?;
                return self.obf(
                    Operator::I32Store8 {
                        memory: memory.clone(),
                    },
                    f,
                    b,
                    &[args[0], a],
                    types,
                    module,
                );
            }
            _ => {
                return self.wrapped.obf(o, f, b, args, types, module);
            }
        }
    }
}
pub struct LowerBulkMemory<F> {
    pub predicate: F,
}
impl<F: FnMut(Memory) -> bool> Obfuscate for LowerBulkMemory<F> {
    fn obf(
        &mut self,
        o: Operator,
        f: &mut waffle::FunctionBody,
        b: waffle::Block,
        args: &[waffle::Value],
        types: &[Type],
        mo: &mut Module,
    ) -> anyhow::Result<(waffle::Value, waffle::Block)> {
        match o {
            Operator::MemoryFill { mem } if (self.predicate)(mem) => {
                let n = f.add_block();
                let dstt = f.values[args[0]].ty(&f.type_pool).unwrap();
                let mut dst = f.add_blockparam(n, dstt);
                let srct = f.values[args[1]].ty(&f.type_pool).unwrap();
                let mut src = f.add_blockparam(n, srct);
                let countt = f.values[args[2]].ty(&f.type_pool).unwrap();
                let mut count = f.add_blockparam(n, countt);
                f.set_terminator(
                    b,
                    waffle::Terminator::Br {
                        target: BlockTarget {
                            block: n,
                            args: args.to_owned(),
                        },
                    },
                );
                let b = n;
                let mut e = Expr::Bind(
                    Operator::I32Store8 {
                        memory: MemoryArg {
                            align: 0,
                            offset: 0,
                            memory: mem,
                        },
                    },
                    vec![Expr::Leaf(dst), Expr::Leaf(src)],
                );
                let (_, b) = e.build(mo, f, b)?;
                let oc = count;
                for (r, sub) in vec![(&mut dst, false), (&mut count, true)] {
                    let t = f.values[*r].ty(&f.type_pool).unwrap();
                    let s = add_op(
                        f,
                        &[],
                        &[t],
                        match t {
                            Type::I32 => Operator::I32Const { value: 1 },
                            Type::I64 => Operator::I64Const { value: 1 },
                            _ => anyhow::bail!("wrong type"),
                        },
                    );
                    f.append_to_block(b, s);
                    let s = add_op(
                        f,
                        &[*r, s],
                        &[t],
                        match t {
                            Type::I32 => {
                                if sub {
                                    Operator::I32Sub
                                } else {
                                    Operator::I32Add
                                }
                            }
                            Type::I64 => {
                                if sub {
                                    Operator::I64Sub
                                } else {
                                    Operator::I64Add
                                }
                            }
                            _ => anyhow::bail!("wrong type"),
                        },
                    );
                    f.append_to_block(b, s);
                    *r = s;
                }
                let oc = add_op(
                    f,
                    &[oc],
                    &[countt],
                    match countt {
                        Type::I32 => Operator::I32Eqz,
                        Type::I64 => Operator::I64Eqz,
                        _ => anyhow::bail!("wrong type"),
                    },
                );
                f.append_to_block(b, oc);
                let m = f.add_block();
                f.set_terminator(
                    b,
                    waffle::Terminator::CondBr {
                        cond: oc,
                        if_true: BlockTarget {
                            block: m,
                            args: vec![],
                        },
                        if_false: BlockTarget {
                            block: n,
                            args: vec![src, dst, count],
                        },
                    },
                );
                let o = add_op(f, &[], &[], Operator::Nop);
                f.append_to_block(m, o);
                return Ok((o, m));
            }
            Operator::MemoryCopy { dst_mem, src_mem }
                if (self.predicate)(dst_mem) || (self.predicate)(src_mem) =>
            {
                let n = f.add_block();
                let dstt = f.values[args[0]].ty(&f.type_pool).unwrap();
                let mut dst = f.add_blockparam(n, dstt);
                let srct = f.values[args[1]].ty(&f.type_pool).unwrap();
                let mut src = f.add_blockparam(n, srct);
                let countt = f.values[args[2]].ty(&f.type_pool).unwrap();
                let mut count = f.add_blockparam(n, countt);
                f.set_terminator(
                    b,
                    waffle::Terminator::Br {
                        target: BlockTarget {
                            block: n,
                            args: args.to_owned(),
                        },
                    },
                );
                let b = n;
                let mut e = Expr::Bind(
                    Operator::I32Store8 {
                        memory: MemoryArg {
                            align: 0,
                            offset: 0,
                            memory: dst_mem,
                        },
                    },
                    vec![
                        Expr::Leaf(dst),
                        Expr::Bind(
                            Operator::I32Load8U {
                                memory: MemoryArg {
                                    align: 0,
                                    offset: 0,
                                    memory: src_mem,
                                },
                            },
                            vec![Expr::Leaf(src)],
                        ),
                    ],
                );
                let (_, b) = e.build(mo, f, b)?;
                let oc = count;
                for (r, sub) in vec![(&mut dst, false), (&mut src, false), (&mut count, true)] {
                    let t = f.values[*r].ty(&f.type_pool).unwrap();
                    let s = add_op(
                        f,
                        &[],
                        &[t],
                        match t {
                            Type::I32 => Operator::I32Const { value: 1 },
                            Type::I64 => Operator::I64Const { value: 1 },
                            _ => anyhow::bail!("wrong type"),
                        },
                    );
                    f.append_to_block(b, s);
                    let s = add_op(
                        f,
                        &[*r, s],
                        &[t],
                        match t {
                            Type::I32 => {
                                if sub {
                                    Operator::I32Sub
                                } else {
                                    Operator::I32Add
                                }
                            }
                            Type::I64 => {
                                if sub {
                                    Operator::I64Sub
                                } else {
                                    Operator::I64Add
                                }
                            }
                            _ => anyhow::bail!("wrong type"),
                        },
                    );
                    f.append_to_block(b, s);
                    *r = s;
                }
                let oc = add_op(
                    f,
                    &[oc],
                    &[countt],
                    match countt {
                        Type::I32 => Operator::I32Eqz,
                        Type::I64 => Operator::I64Eqz,
                        _ => anyhow::bail!("wrong type"),
                    },
                );
                f.append_to_block(b, oc);
                let m = f.add_block();
                f.set_terminator(
                    b,
                    waffle::Terminator::CondBr {
                        cond: oc,
                        if_true: BlockTarget {
                            block: m,
                            args: vec![],
                        },
                        if_false: BlockTarget {
                            block: n,
                            args: vec![src, dst, count],
                        },
                    },
                );
                let o = add_op(f, &[], &[], Operator::Nop);
                f.append_to_block(m, o);
                return Ok((o, m));
            }
            _ => {
                let v = waffle_ast::add_op(f, args, types, o);
                f.append_to_block(b, v);
                return Ok((v, b));
            }
        }
    }
}
pub fn lower(m: &mut Module, mut f: impl FnMut(Memory) -> bool) -> anyhow::Result<()>{
    obf_mod(m, &mut LowerBulkMemory{predicate: &mut f})?;
    obf_mod(m,&mut Reload{predicate: f, wrapped: DontObf{}})?;
    return Ok(())
}
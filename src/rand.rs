use ::rand::{seq::IndexedRandom, Rng};
use modinverse::modinverse;
use waffle::{Block, Terminator, Value};
use waffle_ast::fcopy::{DontObf, Obfuscate};

use crate::*;
pub fn random_val(ty: Type, dst: &mut FunctionBody, k: Block, rng: &mut impl Rng) -> Value {
    dst.add_op(
        k,
        match ty.clone() {
            Type::I32 => Operator::I32Const { value: rng.gen() },
            Type::I64 => Operator::I64Const { value: rng.gen() },
            Type::F32 => Operator::F32Const { value: rng.gen() },
            Type::F64 => Operator::F64Const { value: rng.gen() },
            Type::V128 => todo!(),
            Type::Heap(_) => Operator::RefNull { ty: ty.clone() },
            _ => todo!(),
        },
        &[],
        &[ty],
    )
}
pub struct Obf<R> {
    pub rng: R,
    pub locked_tables: Vec<Table>,
}
impl<R: Rng> Obfuscate for Obf<R> {
    fn obf(
        &mut self,
        o: Operator,
        f: &mut FunctionBody,
        b: Block,
        args: &[Value],
        types: &[Type],
        module: &mut Module,
    ) -> anyhow::Result<(Value, Block)> {
        loop {
            if self.rng.random_bool(0.1) {
                return DontObf {}.obf(o, f, b, args, types, module);
            }
            if let Operator::I32Const { value } = o {
                for t in self
                    .locked_tables
                    .iter()
                    .filter(|t| !module.tables[**t].table64)
                    .cloned()
                    .collect::<Vec<_>>()
                {
                    if self.rng.random_bool(0.1) {
                        let s = module.tables[t].func_elements.as_ref().unwrap().len();
                        let s = s as u32;
                        let sv = f.add_op(b, Operator::TableSize { table_index: t }, args, types);
                        let (tv, b) = self.obf(
                            Operator::I32Const {
                                value: value.wrapping_sub(s),
                            },
                            f,
                            b,
                            args,
                            types,
                            module,
                        )?;
                        return self.obf(Operator::I32Add, f, b, &[tv, sv], types, module);
                    }
                }
                if value == 0 {
                    for v in f.blocks[b]
                        .insts
                        .iter()
                        .cloned()
                        .chain(f.blocks[b].params.iter().map(|a| a.1))
                        .collect::<Vec<_>>()
                    {
                        if f.values[v].ty(&f.type_pool) == Some(Type::I32)
                            && self.rng.random_bool(0.1)
                        {
                            return self.obf(Operator::I32Sub, f, b, &[v, v], types, module);
                        }
                    }
                }
                if self.rng.random_bool(0.1) {
                    let value = value as u64 + (self.rng.random::<u64>() << 32);
                    let (v, b) = self.obf(
                        Operator::I64Const { value },
                        f,
                        b,
                        args,
                        &[Type::I64],
                        module,
                    )?;
                    return self.obf(Operator::I32WrapI64, f, b, &[v], types, module);
                }
                if value != 0 && self.rng.random_bool(0.1) {
                    let s = if self.rng.random_bool(0.8) {
                        self.rng.random_range(0..value)
                    } else {
                        self.rng.random()
                    };
                    let (tv, b) = self.obf(
                        Operator::I32Const {
                            value: value.wrapping_sub(s),
                        },
                        f,
                        b,
                        args,
                        types,
                        module,
                    )?;
                    let (sv, b) =
                        self.obf(Operator::I32Const { value: s }, f, b, args, types, module)?;
                    return self.obf(Operator::I32Add, f, b, &[tv, sv], types, module);
                }
                if self.rng.random_bool(0.1) {
                    let mut v: u32 = self.rng.random();
                    let i = loop {
                        match modinverse(v as u64, 0x100000000) {
                            None => {}
                            Some(i) => break i as u32,
                        };
                        v = self.rng.random();
                    };
                    let i = i.wrapping_mul(value);
                    let (sv, b) =
                        self.obf(Operator::I32Const { value: i }, f, b, args, types, module)?;
                    let (tv, b) =
                        self.obf(Operator::I32Const { value: v }, f, b, args, types, module)?;
                    return self.obf(Operator::I32Mul, f, b, &[tv, sv], types, module);
                }
            }
            if let Operator::I64Const { value } = o {
                for t in self
                    .locked_tables
                    .iter()
                    .filter(|t| module.tables[**t].table64)
                    .cloned()
                    .collect::<Vec<_>>()
                {
                    if self.rng.random_bool(0.1) {
                        let s = module.tables[t].func_elements.as_ref().unwrap().len();
                        let s = s as u64;
                        let sv = f.add_op(b, Operator::TableSize { table_index: t }, args, types);
                        let (tv, b) = self.obf(
                            Operator::I64Const {
                                value: value.wrapping_sub(s),
                            },
                            f,
                            b,
                            args,
                            types,
                            module,
                        )?;
                        return self.obf(Operator::I64Add, f, b, &[tv, sv], types, module);
                    }
                }
                if value == 0 {
                    for v in f.blocks[b]
                        .insts
                        .iter()
                        .cloned()
                        .chain(f.blocks[b].params.iter().map(|a| a.1))
                        .collect::<Vec<_>>()
                    {
                        if f.values[v].ty(&f.type_pool) == Some(Type::I64)
                            && self.rng.random_bool(0.1)
                        {
                            return self.obf(Operator::I64Sub, f, b, &[v, v], types, module);
                        }
                    }
                }
                if value & 0xffffffff == value && self.rng.random_bool(0.1) {
                    let value = value as u32;
                    let (v, b) = self.obf(
                        Operator::I32Const { value },
                        f,
                        b,
                        args,
                        &[Type::I32],
                        module,
                    )?;
                    return self.obf(Operator::I64ExtendI32U, f, b, &[v], types, module);
                }
                if value != 0 && self.rng.random_bool(0.1) {
                    let s = if self.rng.random_bool(0.8) {
                        self.rng.random_range(0..value)
                    } else {
                        self.rng.random()
                    };
                    let (tv, b) = self.obf(
                        Operator::I64Const {
                            value: value.wrapping_sub(s),
                        },
                        f,
                        b,
                        args,
                        types,
                        module,
                    )?;
                    let (sv, b) =
                        self.obf(Operator::I64Const { value: s }, f, b, args, types, module)?;
                    return self.obf(Operator::I64Add, f, b, &[tv, sv], types, module);
                }
                if self.rng.random_bool(0.1) {
                    let mut v: u64 = self.rng.random();
                    let i = loop {
                        match modinverse(v as u128, 0x10000000000000000) {
                            None => {}
                            Some(i) => break i as u64,
                        };
                        v = self.rng.random();
                    };
                    let i = i.wrapping_mul(value);
                    let (sv, b) =
                        self.obf(Operator::I64Const { value: i }, f, b, args, types, module)?;
                    let (tv, b) =
                        self.obf(Operator::I64Const { value: v }, f, b, args, types, module)?;
                    return self.obf(Operator::I64Mul, f, b, &[tv, sv], types, module);
                }
            }
            if let Operator::I32Add = o{
                if self.rng.random_bool(0.1){
                    let (z,b) = self.obf(Operator::I32Eqz, f, b, &[args[0]], &[Type::I32], module)?;
                    let (v,b) = self.obf(o, f, b, args, types, module)?;
                    let (v,b) = self.obf(Operator::Select, f, b, &[z,args[1],v], types, module)?;
                    return Ok((v,b));
                }
            }
            if let Operator::I64Add = o{
                if self.rng.random_bool(0.1){
                    let (z,b) = self.obf(Operator::I64Eqz, f, b, &[args[0]], &[Type::I32], module)?;
                    let (v,b) = self.obf(o, f, b, args, types, module)?;
                    let (v,b) = self.obf(Operator::Select, f, b, &[z,args[1],v], types, module)?;
                    return Ok((v,b));
                }
            }
            if let Some(memory) = waffle::op_traits::memory_arg(&o) {
                if self.rng.random_bool(0.1) {
                    let mut memory = memory.clone();
                    let a = self.rng.random_range(0..=memory.offset);
                    memory.offset = memory.offset.wrapping_sub(a);
                    if !module.memories[memory.memory].memory64 {
                        memory.offset &= 0xffffffff;
                    }
                    let mut o = o;
                    let mut args = args.to_owned();
                    o.update_memory_arg(|a| *a = memory.clone());
                    let (v, b) = self.obf(
                        Operator::I64Const { value: a },
                        f,
                        b,
                        &[],
                        &[Type::I64],
                        module,
                    )?;
                    let v = if module.memories[memory.memory].memory64 {
                        v
                    } else {
                        f.add_op(b, Operator::I32WrapI64, &[v], &[Type::I32])
                    };
                    let (v, b) = if module.memories[memory.memory].memory64 {
                        self.obf(Operator::I64Add, f, b, &[v, args[0]], &[Type::I64], module)?
                    } else {
                        self.obf(Operator::I32Add, f, b, &[v, args[0]], &[Type::I32], module)?
                    };
                    args[0] = v;
                    return self.obf(o, f, b, &args, types, module);
                }
            }
        }
    }
}
pub fn flippy(dst: &mut FunctionBody, rng: &mut impl Rng) {
    dst.convert_to_max_ssa(None);
    for k in dst.blocks.iter().collect::<Vec<_>>() {
        let mut t = take(&mut dst.blocks[k].terminator);
        if let Terminator::Br { target } = t {
            let target_fake = dst
                .blocks
                .iter()
                .collect::<Vec<_>>()
                .choose(rng)
                .cloned()
                .unwrap();
            let p = dst.blocks[target_fake]
                .params
                .iter()
                .map(|a| a.0)
                .collect::<Vec<_>>();
            let p = p
                .into_iter()
                .map(|q| {
                    if rng.random() {
                        let mut a = dst.blocks[k]
                            .insts
                            .iter()
                            .cloned()
                            .chain(dst.blocks[k].params.iter().map(|a| a.1))
                            .collect::<Vec<_>>();
                        a = a
                            .into_iter()
                            .filter_map(|v| {
                                let p = dst.values[v].ty(&dst.type_pool)?;
                                if p != q {
                                    None
                                } else {
                                    Some(v)
                                }
                            })
                            .collect();
                        let v = loop {
                            let Some(c) = a.choose(rng) else {
                                return random_val(q, dst, k, rng);
                            };
                            let Some(p) = dst.values[*c].ty(&dst.type_pool) else {
                                continue;
                            };
                            if p != q {
                                continue;
                            };
                            break *c;
                        };
                        v
                    } else {
                        random_val(q, dst, k, rng)
                    }
                })
                .collect();
            let target_fake = BlockTarget {
                block: target_fake,
                args: p,
            };
            let (a, if_true, if_false) = if rng.random() {
                (0u32, target_fake, target)
            } else {
                let mut i = rng.random();
                while i == 0 {
                    i = rng.random();
                }
                (i, target, target_fake)
            };
            let a = dst.add_op(k, Operator::I32Const { value: a }, &[], &[Type::I32]);
            t = Terminator::CondBr {
                cond: a,
                if_true: if_true,
                if_false: if_false,
            };
        }

        dst.set_terminator(k, t);
    }
}

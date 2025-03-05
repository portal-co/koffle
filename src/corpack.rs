pub mod serdes;
use std::collections::BTreeSet;

use waffle::{passes::tcore::results_ref_2, util::new_sig, Import, SignatureData};

use crate::*;
pub fn corpack(module: &mut Module, t: &TableMap, g: &GuardMap, s: &serdes::SerCache) {
    let Some(ift) = ift(module) else {
        return;
    };
    let Some(mem) = memory(module) else {
        return;
    };
    let nss = module
        .exports
        .iter()
        .filter_map(|x| {
            let ExportKind::Func(f) = &x.kind else {
                return None;
            };
            let SignatureData::Func {
                params,
                returns: results,
            } = &module.signatures[module.funcs[*f].sig()]
            else {
                return None;
            };
            if params.len() != 0 {
                return None;
            };
            if results.len() != 1 {
                return None;
            };
            if results[0] != Type::I64 {
                return None;
            };
            return Some((
                x.name.clone(),
                (
                    *f,
                    module
                        .custom_sections
                        .entry(x.name.clone())
                        .or_default()
                        .clone(),
                ),
            ));
        })
        .collect::<BTreeMap<_, _>>();
    for (ns, (i, s)) in nss.iter() {
        let i = *i;
        let s = s
            .split(|a| *a == 0xff)
            .filter(|a| a.len() != 0)
            .filter_map(|a| {
                let (a, b) = a.split_at_checked(8)?;
                let b = std::str::from_utf8(b).ok()?;
                let a: &[u8; 8] = a.try_into().ok()?;
                let a = u64::from_le_bytes(*a);
                Some((a, b))
            })
            .collect::<Vec<_>>();
        let t = s.iter().map(|a| a.0).collect::<BTreeSet<_>>();
        let t = t
            .into_iter()
            .map(|a| {
                let sig = new_sig(
                    module,
                    SignatureData::Func {
                        params: vec![],
                        returns: vec![Type::I32],
                    },
                );
                let mut dst = FunctionBody::new(module, sig);
                let av = dst.add_op(
                    dst.entry,
                    Operator::I64Const { value: a },
                    &[],
                    &[Type::I64],
                );
                let v = dst.add_op(
                    dst.entry,
                    Operator::Call { function_index: i },
                    &[],
                    &[Type::I64],
                );
                let v = dst.add_op(dst.entry, Operator::I64Eq, &[av, v], &[Type::I32]);
                dst.set_terminator(dst.entry, waffle::Terminator::Return { values: vec![v] });
                let v = module
                    .funcs
                    .push(FuncDecl::Body(sig, format!("~tester"), dst));
                (a, v)
            })
            .collect::<BTreeMap<_, _>>();
        let mut imps = BTreeMap::new();
        for mut i in take(&mut module.imports) {
            if i.module == *ns {
                imps.insert(i.name, i.kind);
                continue;
            }
            module.imports.push(i)
        }
        'a: for (i, k) in take(&mut imps) {
            for (x, y) in s.iter().cloned() {
                if let Some(y) = y.strip_prefix("i") {
                    if let Some((t, mut y)) = y.split_once(".") {
                        if t == i {
                            if let ImportKind::Func(f) = k {
                                let sig = module.funcs[f].sig();
                                let name = module.funcs[f].name().to_owned();
                                let mut dst = FunctionBody::new(module, sig);
                                let mut params = dst.blocks[dst.entry]
                                    .params
                                    .iter()
                                    .map(|a| a.1)
                                    .collect::<Vec<_>>();
                                let mut new = dst.entry;
                                loop {
                                    if let Some(z) = y.strip_prefix("c") {
                                        if let Some((z, n)) = z.split_once(";") {
                                            y = n;
                                            if let Some(ExportKind::Func(f)) =
                                                module.exports.iter().find_map(|a| {
                                                    if a.name == z {
                                                        Some(a.kind.clone())
                                                    } else {
                                                        None
                                                    }
                                                })
                                            {
                                                let SignatureData::Func {
                                                    params: p2,
                                                    returns,
                                                } = module.signatures[module.funcs[f].sig()]
                                                    .clone()
                                                else {
                                                    continue;
                                                };
                                                let mut p2 = p2
                                                    .iter()
                                                    .filter_map(|a| params.pop())
                                                    .collect::<Vec<_>>();
                                                p2.reverse();
                                                let fv = dst.add_op(
                                                    new,
                                                    Operator::Call { function_index: f },
                                                    &p2,
                                                    &returns,
                                                );
                                                let fv = results_ref_2(&mut dst, fv);
                                                params = fv
                                                    .into_iter()
                                                    .chain(params.into_iter())
                                                    .collect();
                                            }
                                            continue;
                                        }
                                    }
                                    if let Some(z) = y.strip_prefix("d") {
                                        if let Some((d, z)) = z.split_once(";") {
                                            y = z;
                                            for e in d
                                                .split(",")
                                                .filter_map(|a| usize::from_str_radix(a, 36).ok())
                                            {
                                                // if let Some(a) ={
                                                let a = params.remove(params.len() - 1 - e);
                                                params.push(a)
                                                // }
                                            }
                                            continue;
                                        }
                                    }
                                    break;
                                }

                                module.funcs[f] = FuncDecl::Body(sig, name, dst);
                            }
                            continue 'a;
                        }
                    }
                }
            }
            imps.insert(i, k);
        }
        for (i, k) in imps {
            module.imports.push(Import {
                module: ns.clone(),
                name: i,
                kind: k,
            });
        }
        for (x, y) in s.iter().cloned() {
            let Some(tester) = t.get(&x).cloned() else {
                continue;
            };
            if let Some(y) = y.strip_prefix("h") {
                if let Some((m, n)) = y.split_once(".") {
                    let a = format!("{ns}:{m}.{n}");
                    if let Some(ExportKind::Func(f)) = module.exports.iter().find_map(|x| {
                        if x.name == a {
                            Some(x.kind.clone())
                        } else {
                            None
                        }
                    }) {
                        if let Some(ImportKind::Func(h)) = module.imports.iter().find_map(|i| {
                            if i.name == n && i.module == m {
                                Some(i.kind.clone())
                            } else {
                                None
                            }
                        }) {
                            guard_fn(
                                module,
                                h,
                                f,
                                Some(Cond::Func {
                                    func: tester,
                                    pass_args: false,
                                }),
                            );
                        }
                    }
                }
            }
        }
    }
}

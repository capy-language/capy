// TODO: other kinds of aarch64 abis then apple

use cranelift::prelude::types::{I128, I16, I32, I64, I8};
use hir_ty::Ty;
use internment::Intern;
use tinyvec::ArrayVec;

use crate::{convert::GetFinalTy, layout::GetLayoutInfo};

use super::{FnAbi, PassMode};

/// "A Homogeneous Floating-point Aggregate (HFA) is a Homogeneous Aggregate with a Fundamental Data Type that is a Floating-Point type and at most four uniquely addressable members."
pub fn is_hfa(ty: Intern<Ty>) -> Option<PassMode> {
    if let Some(fields) = ty.as_struct() {
        let mut tys = ArrayVec::new();
        let ty = fields[0].1;
        if fields.len() > 4 {
            None
        } else {
            for (_, field_ty) in fields {
                if field_ty != ty || !field_ty.is_float() {
                    return None;
                }
                tys.push(field_ty.get_final_ty().into_real_type().unwrap());
            }
            Some(PassMode::cast(tys, ty))
        }
    } else if let Some((sz, subty)) = ty.as_array() {
        if subty.is_float() && sz <= 4 {
            let mut tys = ArrayVec::new();
            for _ in 0..sz {
                tys.push(subty.get_final_ty().into_real_type().unwrap());
            }
            Some(PassMode::cast(tys, ty))
        } else {
            None
        }
    } else {
        None
    }
}

fn classify_ret(ret: Intern<Ty>) -> Option<PassMode> {
    if ret.is_zero_sized() {
        return None;
    }
    if !ret.is_aggregate() {
        return Some(PassMode::direct(
            ret.get_final_ty().into_real_type().unwrap(),
        ));
    }
    if let Some(hfa) = is_hfa(ret) {
        Some(hfa)
    } else if ret.size() <= 16 {
        Some(PassMode::cast(
            ArrayVec::from_array_len([I64, I64, I64, I64], (ret.size() + 7) as usize / 8),
            ret,
        ))
    } else {
        Some(PassMode::indirect())
    }
}
fn classify_arg(arg: Intern<Ty>) -> Option<PassMode> {
    if arg.is_zero_sized() {
        return None;
    }
    if !arg.is_aggregate() {
        return Some(PassMode::direct(
            arg.get_final_ty().into_real_type().unwrap(),
        ));
    }
    if let Some(hfa) = is_hfa(arg) {
        Some(hfa)
    } else if arg.size() <= 16 {
        if arg.align() != 128 {
            // TODO: eight byte align the stack instead
            let eight_bytes = arg.stride() / 8;
            let mut tys = ArrayVec::from_array_len([I64, I64, I64, I64], eight_bytes as usize);
            let four_bytes = (arg.stride() - eight_bytes * 8) / 4;
            if four_bytes == 1 {
                tys.push(I32)
            }
            let two_bytes = (arg.stride() - eight_bytes * 8 - four_bytes * 4) / 2;
            if two_bytes == 1 {
                tys.push(I16)
            }
            let one_bytes = arg.stride() - eight_bytes * 8 - four_bytes * 4 - two_bytes * 2;
            if one_bytes == 1 {
                tys.push(I8)
            }
            Some(PassMode::cast(tys, arg))
        } else {
            Some(PassMode::cast(
                ArrayVec::from_array_len([I128, I128, I128, I128], (arg.size() + 15) as usize / 16),
                arg,
            ))
        }
    } else {
        Some(PassMode::indirect())
    }
}

pub fn fn_ty_to_abi((args, ret): (&[Intern<Ty>], Intern<Ty>)) -> FnAbi {
    let mut sig = FnAbi::new();
    sig.ret = classify_ret(ret);

    for (idx, arg) in args.iter().enumerate() {
        if let Some(arg) = classify_arg(*arg) {
            sig.args.push((arg, idx as u16))
        }
    }

    sig
}

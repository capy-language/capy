use cranelift::codegen::ir::Type;
use hir_ty::Ty;
use internment::Intern;

use crate::{convert::GetFinalTy, layout::GetLayoutInfo};

use super::{FnAbi, PassMode};

fn ty_to_passmode(ty: Intern<Ty>) -> Option<PassMode> {
    if ty.is_zero_sized() {
        None
    } else if ty.is_aggregate() {
        Some(match ty.size() {
            x if x < 8 => PassMode::cast((Type::int_with_byte_size(x as u16).unwrap(), None), ty),
            _ => PassMode::indirect(),
        })
    } else if ty.size() > 8 {
        Some(PassMode::direct(
            ty.get_final_ty().into_real_type().unwrap(),
        ))
    } else {
        Some(PassMode::indirect())
    }
    // TODO: vector types
}

pub fn fn_ty_to_abi((args, ret): (&Vec<Intern<Ty>>, Intern<Ty>)) -> FnAbi {
    let mut sig = FnAbi::new();
    sig.ret = ty_to_passmode(ret);

    for (idx, arg) in args.into_iter().enumerate() {
        if let Some(arg) = ty_to_passmode(*arg) {
            sig.args.push((arg, idx as u16))
        }
    }

    sig
}

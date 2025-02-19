use hir_ty::{ParamTy, Ty};
use internment::Intern;

use crate::convert::GetFinalTy;

use super::{FnAbi, PassMode};

fn ty_to_passmode(ty: Intern<Ty>) -> Option<PassMode> {
    if ty.is_zero_sized() {
        None
    } else if ty.is_aggregate() {
        Some(PassMode::indirect())
    } else {
        Some(PassMode::direct(
            ty.get_final_ty().into_real_type().unwrap(),
        ))
    }
    // TODO: vector types
}

pub fn fn_ty_to_abi((args, ret): (&[ParamTy], Intern<Ty>)) -> FnAbi {
    let mut sig = FnAbi::new();
    sig.ret = ty_to_passmode(ret);
    sig.simple_ret = true;

    for (idx, arg) in args.iter().enumerate() {
        if let Some(arg) = ty_to_passmode(arg.ty) {
            sig.args.push((arg, idx as u16))
        }
    }

    sig
}

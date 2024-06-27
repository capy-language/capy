use cranelift::codegen::ir::Type;
use hir_ty::Ty;
use internment::Intern;
use tinyvec::array_vec;

use crate::{convert::GetFinalTy, layout::GetLayoutInfo};

use super::{FnAbi, PassMode};

fn ty_to_passmode(ty: Intern<Ty>) -> Option<PassMode> {
    fn is_pow_of2(n: u32) -> bool {
        (n & (n - 1)) == 0
    }
    if ty.is_zero_sized() {
        None
    } else if ty.is_aggregate() {
        match ty.size() {
            x if x < 8 && is_pow_of2(x) => {
                let x = x as u16;
                Some(PassMode::cast(
                    array_vec![Type::int_with_byte_size(x).unwrap()],
                    ty,
                ))
            }
            _ => Some(PassMode::indirect()),
        }
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

    for (idx, arg) in args.iter().enumerate() {
        if let Some(arg) = ty_to_passmode(*arg) {
            sig.args.push((arg, idx as u16))
        }
    }

    sig
}

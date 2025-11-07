use cranelift::codegen::ir::{self, Type};
use hir::common::{ParamTy, Ty};
use internment::Intern;
use tinyvec::{ArrayVec, array_vec};

use crate::{convert::GetFinalTy, layout::GetLayoutInfo};

use super::{FnAbi, PassMode};

/// "Definitions We first define a number of classes to classify arguments. The
/// classes are corresponding to AMD64 register classes and defined as:"
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Class {
    /// "INTEGER This class consists of integral types that fit into one of the general
    /// purpose registers."
    Int,
    /// "SSE The class consists of types that fit into a vector register"
    Sse,
    /// "SSEUP The class consists of types that fit into a vector register and can be passed
    /// and returned in the upper bytes of it"
    SseUp,
    // TODO: X87?
    /// "NO_CLASS This class is used as initializer in the algorithms. It will be used for
    /// padding and empty structures and unions."
    #[allow(clippy::enum_variant_names)]
    NoClass,
    // MEMORY This class consists of types that will be passed and returned in memory via the stack.
    //Memory,
}

impl Class {
    fn merge_eigthbyte(self, other: Self) -> Self {
        use Class::*;
        match (self, other) {
            // (a) if both classes are equal, this is the resulting class
            (x, y) if x == y => x,
            // (b) if one of the classes is NO_CLASS, the resulting class is the other
            // class
            (class, NoClass) | (NoClass, class) => class,
            // (c) If one of the classes is MEMORY, the result is the MEMORY class.
            //(Memory, _) | (_, Memory) => Memory,
            // (d) If one of the classes is INTEGER, the result is the INTEGER.
            (Int, _) | (_, Int) => Int,
            // (f) Otherwise class SSE is used
            _ => Class::Sse,
        }
    }
}

fn classify_arg(ty: Intern<Ty>) -> Option<[Class; 8]> {
    fn classify_eight_byte(ty: Intern<Ty>, classes: &mut [Class; 8], offset: usize) {
        use Class::*;
        match (*ty).clone() {
            // "Arguments of types (signed and unsigned) _Bool, char, short, int,
            // long, long long, and pointers are in the INTEGER class."
            Ty::Type
            | Ty::String
            | Ty::Char
            | Ty::IInt(_)
            | Ty::UInt(_)
            | Ty::Bool
            | Ty::Pointer { .. }
            | Ty::RawPtr { .. }
            | Ty::ConcreteFunction { .. }
            | Ty::File(_) => {
                classes[offset / 8] = classes[offset / 8].merge_eigthbyte(Int);
                if ty.size() > 8 {
                    classes[offset / 8 + 1] = classes[offset / 8 + 1].merge_eigthbyte(Int);
                }
            }
            // "Arguments of types float, double, _Decimal32, _Decimal64 and
            // __m64 are in class SSE."
            Ty::Float(_) => classes[offset / 8] = classes[offset / 8].merge_eigthbyte(Sse),

            Ty::ConcreteArray { sub_ty, size, .. } | Ty::AnonArray { size, sub_ty } => {
                if size != 0 {
                    for idx in 0..size {
                        classify_eight_byte(
                            sub_ty,
                            classes,
                            offset + (idx * sub_ty.stride() as u64) as usize,
                        )
                    }
                }
            }
            Ty::Slice { .. } | Ty::RawSlice | Ty::Any => {
                classes[offset / 8] = classes[offset / 8].merge_eigthbyte(Int);
                classes[offset / 8 + 1] = classes[offset / 8 + 1].merge_eigthbyte(Int)
            }
            Ty::Distinct { sub_ty, .. } => classify_eight_byte(sub_ty, classes, offset),
            Ty::EnumVariant { sub_ty, .. } => classify_eight_byte(sub_ty, classes, offset),
            Ty::ConcreteStruct { members, .. } | Ty::AnonStruct { members } => {
                for (field, &field_off) in ty.struct_layout().unwrap().offsets().iter().enumerate()
                {
                    classify_eight_byte(members[field].ty, classes, offset + field_off as usize)
                }
            }
            // todo: what to do for enums?
            Ty::Enum { variants, .. } => {
                let enum_layout = ty.enum_layout().unwrap();
                for variant_ty in variants {
                    // todo: idk if doing this over the same offset will break anything
                    classify_eight_byte(variant_ty, classes, offset);
                }
                let discrim_offset = offset + enum_layout.discriminant_offset() as usize;
                classes[discrim_offset / 8] = classes[discrim_offset / 8].merge_eigthbyte(Int);
            }
            Ty::ErrorUnion {
                error_ty,
                payload_ty,
            } => {
                let enum_layout = ty.enum_layout().unwrap();
                classify_eight_byte(payload_ty, classes, offset);
                classify_eight_byte(error_ty, classes, offset);
                let discrim_offset = offset + enum_layout.discriminant_offset() as usize;
                classes[discrim_offset / 8] = classes[discrim_offset / 8].merge_eigthbyte(Int);
            }
            Ty::Optional { sub_ty } => {
                if let Some(enum_layout) = ty.enum_layout() {
                    classify_eight_byte(sub_ty, classes, offset);
                    let discrim_offset = offset + enum_layout.discriminant_offset() as usize;
                    classes[discrim_offset / 8] = classes[discrim_offset / 8].merge_eigthbyte(Int);
                } else {
                    classes[offset / 8] = classes[offset / 8].merge_eigthbyte(Int);
                    if ty.size() > 8 {
                        classes[offset / 8 + 1] = classes[offset / 8 + 1].merge_eigthbyte(Int);
                    }
                }
            }
            _ => {}
        };
    }

    // let n = ((ty.size() + 7) / 8) as usize;
    let n = ty.size().div_ceil(8) as usize;
    if n > 8 {
        return None;
    }

    let mut classes = [Class::NoClass; 8];
    classify_eight_byte(ty, &mut classes, 0);
    if n > 2 {
        #[allow(clippy::if_same_then_else)]
        if classes[0] != Class::Sse {
            None
        } else if classes[1..n].iter().any(|&class| class != Class::SseUp) {
            None
        } else {
            Some(classes)
        }
    } else {
        let mut i = 0;
        while i < n {
            if classes[i] == Class::SseUp {
                classes[i] = Class::Sse;
            } else if classes[i] == Class::Sse {
                i += 1;
                while i != n && classes[i] == Class::SseUp {
                    i += 1;
                }
            } else {
                i += 1;
            }
        }
        Some(classes)
    }
}

fn reg_component(cls: &[Class], i: &mut usize, size: usize) -> Option<ir::Type> {
    if *i >= cls.len() {
        println!("i > len");
        return None;
    }
    match cls[*i] {
        Class::NoClass => {
            println!("no class");
            None
        }
        Class::Int => {
            *i += 1;
            if size < 8 {
                ir::Type::int_with_byte_size((size as u16).next_power_of_two())
            } else {
                ir::Type::int_with_byte_size(8)
            }
        }
        Class::Sse => {
            let vec_len = 1 + cls[*i + 1..]
                .iter()
                .take_while(|&&c| c == Class::SseUp)
                .count();
            *i += vec_len;
            Some(if vec_len == 1 {
                match size {
                    4 => ir::types::F32,
                    _ => ir::types::F64,
                }
            } else {
                todo!("vector types")
            })
        }
        c => unreachable!("reg_component: unhandled class {:?}", c),
    }
}

pub fn split_aggregate(aggr: Intern<Ty>, cls: &[Class]) -> ArrayVec<[Type; 4]> {
    let mut i = 0;
    println!("split_aggregate - {aggr:?}");
    let lo = reg_component(cls, &mut i, aggr.size() as usize).unwrap();
    let off = i * 8;
    let mut tys = array_vec!();
    tys.push(lo);
    if aggr.size() as usize > off {
        if let Some(hi) = reg_component(cls, &mut i, aggr.size() as usize - off) {
            tys.push(hi);
        }
    }

    tys
}

pub fn fn_ty_to_abi((args, ret): (&[ParamTy], Intern<Ty>)) -> FnAbi {
    let mut sig = FnAbi::new();

    let push_direct = |arg: Intern<Ty>, cls: &[_], to: &mut Vec<_>, idx: u16| {
        if arg.is_aggregate() {
            to.push((PassMode::cast(split_aggregate(arg, cls), arg), idx));
        } else {
            // if arg.size() < 4 {
            //     // TODO: sign extend appropiatly
            //     //to.push((PassMode::direct(Type::int(32).unwrap()), idx));
            // } else {
            to.push((
                PassMode::direct(arg.get_final_ty().into_real_type().unwrap()),
                idx,
            ))
            //}
        }
    };

    let mut int_regs: usize = 6;
    let mut sse_regs: usize = 8;

    if !ret.is_zero_sized() {
        if let Some(cls) = classify_arg(ret) {
            if ret.is_aggregate() {
                sig.ret = Some(PassMode::cast(split_aggregate(ret, &cls), ret));
            } else {
                sig.ret = Some(PassMode::direct(
                    ret.get_final_ty().into_real_type().unwrap(),
                ))
            }
        } else {
            int_regs -= 1;
            sig.ret = Some(PassMode::indirect_by_val(ret.size() as usize));
        }
    }
    for (idx, arg) in args.iter().enumerate() {
        if arg.ty.is_zero_sized() {
            continue;
        }
        if let Some(classes) = classify_arg(arg.ty) {
            let mut needed_int = 0;
            let mut needed_sse = 0;
            for c in classes {
                match c {
                    Class::Int => needed_int += 1,
                    Class::Sse => needed_sse += 1,
                    _ => {}
                }
            }
            match (
                int_regs.checked_sub(needed_int),
                sse_regs.checked_sub(needed_sse),
            ) {
                (Some(left_int), Some(left_sse)) => {
                    int_regs = left_int;
                    sse_regs = left_sse;
                    // this line is to prevent the unused value lint
                    // this lint is wrong in this situation, as they are read when performing
                    // the `checked_sub` above
                    let (_, _) = (int_regs, sse_regs);
                    push_direct(arg.ty, &classes, &mut sig.args, idx.try_into().unwrap())
                }
                _ => {
                    if arg.ty.is_aggregate() {
                        sig.args.push((
                            PassMode::indirect_by_val(arg.ty.stride().next_multiple_of(8) as usize),
                            idx.try_into().unwrap(),
                        ))
                    } else {
                        sig.args.push((
                            PassMode::direct(arg.ty.get_final_ty().into_real_type().unwrap()),
                            idx.try_into().unwrap(),
                        ))
                    }
                }
            }
        } else {
            sig.args.push((
                PassMode::indirect_by_val(arg.ty.stride().next_multiple_of(8) as usize),
                idx.try_into().unwrap(),
            ))
        }
    }

    sig
}

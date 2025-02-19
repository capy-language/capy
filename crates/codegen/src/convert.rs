pub mod abi;
use std::{cell::OnceCell, sync::Mutex};

use cranelift::prelude::types;
use hir_ty::Ty;
use internment::Intern;
use rustc_hash::FxHashMap;

use crate::{compiler::MetaTyData, layout::GetLayoutInfo};

#[derive(Debug, Clone, Copy)]
pub(crate) enum FinalTy {
    Number(NumberType),
    Pointer(types::Type),
    Void,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct NumberType {
    pub(crate) ty: types::Type,
    pub(crate) float: bool,
    pub(crate) signed: bool,
}

impl NumberType {
    pub(crate) fn bit_width(&self) -> u8 {
        self.ty.bits() as u8
    }

    pub(crate) fn max(&self, other: NumberType) -> NumberType {
        let max_bit_width = self.bit_width().max(other.bit_width());

        let max_ty = match (self.float || other.float, max_bit_width) {
            (true, 32) => types::F32,
            (true, 64) => types::F64,
            (true, _) => unreachable!(),
            (false, 8) => types::I8,
            (false, 16) => types::I16,
            (false, 32) => types::I32,
            (false, 64) => types::I64,
            (false, 128) => types::I128,
            (false, _) => unreachable!(),
        };

        NumberType {
            ty: max_ty,
            float: self.float || other.float,
            signed: self.signed || other.signed,
        }
    }
}

impl FinalTy {
    #[allow(unused)]
    pub(crate) fn is_number_type(&self) -> bool {
        matches!(self, FinalTy::Number(_))
    }

    pub(crate) fn is_pointer_type(&self) -> bool {
        matches!(self, FinalTy::Pointer(_))
    }

    #[allow(unused)]
    pub(crate) fn is_void_type(&self) -> bool {
        matches!(self, FinalTy::Void)
    }

    pub(crate) fn into_real_type(self) -> Option<types::Type> {
        match self {
            FinalTy::Number(NumberType { ty, .. }) => Some(ty),
            FinalTy::Pointer(ty) => Some(ty),
            _ => None,
        }
    }

    pub(crate) fn into_number_type(self) -> Option<NumberType> {
        match self {
            FinalTy::Number(number_ty) => Some(number_ty),
            _ => None,
        }
    }
}

#[derive(Debug)]
struct FinalTys {
    ptr_bit_width: u32,
    finals: FxHashMap<Intern<Ty>, FinalTy>,
}

static FINAL_TYS: Mutex<OnceCell<FinalTys>> = Mutex::new(OnceCell::new());

pub(crate) trait GetFinalTy {
    fn get_final_ty(&self) -> FinalTy;
}

impl GetFinalTy for Intern<Ty> {
    fn get_final_ty(&self) -> FinalTy {
        FINAL_TYS.lock().unwrap().get().unwrap().finals[self]
    }
}

/// Calcuates size, alignment, stride, and field offsets of types.
///
/// If called multiple times, new types will be calculated without discarding old results
///
/// Old results will only be dropped if you try to calculate the layout using a different pointer
/// width.
pub(crate) fn calc_finals(tys: impl Iterator<Item = Intern<Ty>>, ptr_ty: types::Type) {
    let init = || FinalTys {
        ptr_bit_width: ptr_ty.bits(),
        finals: FxHashMap::default(),
    };

    {
        let layouts = FINAL_TYS.lock().unwrap();
        let layout = layouts.get_or_init(init);
        if layout.ptr_bit_width != ptr_ty.bits() {
            layouts.set(init()).unwrap();
        }
    }

    for ty in tys {
        calc_single(ty, ptr_ty);
    }

    {
        let mut finals = FINAL_TYS.lock().unwrap();
        let finals = finals.get_mut().unwrap();
        finals.finals.shrink_to_fit();
    }
}

fn calc_single(ty: Intern<Ty>, ptr_ty: types::Type) {
    {
        let finals = FINAL_TYS.lock().unwrap();
        let finals = finals.get().unwrap();
        if finals.finals.contains_key(&ty) {
            return;
        }
    }

    let finalize_int = |bit_width: u8, signed: bool| -> FinalTy {
        match bit_width {
            u8::MAX => FinalTy::Number(NumberType {
                ty: ptr_ty,
                float: false,
                signed,
            }),
            0 => FinalTy::Number(NumberType {
                ty: types::I32,
                float: false,
                signed: true,
            }),
            8 => FinalTy::Number(NumberType {
                ty: types::I8,
                float: false,
                signed,
            }),
            16 => FinalTy::Number(NumberType {
                ty: types::I16,
                float: false,
                signed,
            }),
            32 => FinalTy::Number(NumberType {
                ty: types::I32,
                float: false,
                signed,
            }),
            64 => FinalTy::Number(NumberType {
                ty: types::I64,
                float: false,
                signed,
            }),
            128 => FinalTy::Number(NumberType {
                ty: types::I128,
                float: false,
                signed,
            }),
            _ => unreachable!(),
        }
    };

    let final_ty = match ty.as_ref() {
        _ if ty.is_zero_sized() => FinalTy::Void,
        hir_ty::Ty::NotYetResolved | hir_ty::Ty::Unknown => FinalTy::Void,
        hir_ty::Ty::IInt(bit_width) => finalize_int(*bit_width, true),
        // {uint} => i32
        hir_ty::Ty::UInt(0) => finalize_int(0, true),
        hir_ty::Ty::UInt(bit_width) => finalize_int(*bit_width, false),
        hir_ty::Ty::Float(bit_width) => match bit_width {
            0 => FinalTy::Number(NumberType {
                ty: types::F32,
                float: true,
                signed: true,
            }),
            32 => FinalTy::Number(NumberType {
                ty: types::F32,
                float: true,
                signed: true,
            }),
            64 => FinalTy::Number(NumberType {
                ty: types::F64,
                float: true,
                signed: true,
            }),
            _ => unreachable!(),
        },
        hir_ty::Ty::Bool | hir_ty::Ty::Char => FinalTy::Number(NumberType {
            ty: types::I8,
            float: false,
            signed: false,
        }),
        hir_ty::Ty::String => FinalTy::Pointer(ptr_ty),
        hir_ty::Ty::Array { sub_ty, .. } => {
            calc_single(*sub_ty, ptr_ty);
            FinalTy::Pointer(ptr_ty)
        }
        hir_ty::Ty::Slice { sub_ty, .. } => {
            calc_single(*sub_ty, ptr_ty);
            FinalTy::Pointer(ptr_ty)
        }
        hir_ty::Ty::Pointer { sub_ty, .. } => {
            calc_single(*sub_ty, ptr_ty);
            FinalTy::Pointer(ptr_ty)
        }
        hir_ty::Ty::Distinct { sub_ty, .. } => {
            calc_single(*sub_ty, ptr_ty);
            sub_ty.get_final_ty()
        }
        hir_ty::Ty::Function {
            param_tys,
            return_ty,
        } => {
            for param in param_tys {
                calc_single(param.ty, ptr_ty);
            }
            calc_single(*return_ty, ptr_ty);
            FinalTy::Pointer(ptr_ty)
        }
        hir_ty::Ty::Struct { members, .. } => {
            for member in members {
                calc_single(member.ty, ptr_ty);
            }
            FinalTy::Pointer(ptr_ty)
        }
        hir_ty::Ty::Enum { variants, .. } => {
            for variant in variants {
                calc_single(*variant, ptr_ty);
            }
            FinalTy::Pointer(ptr_ty)
        }
        hir_ty::Ty::Variant { sub_ty, .. } => {
            calc_single(*sub_ty, ptr_ty);
            sub_ty.get_final_ty()
        }
        hir_ty::Ty::Type => FinalTy::Number(NumberType {
            ty: types::I32,
            float: false,
            signed: false,
        }),
        hir_ty::Ty::Any => FinalTy::Pointer(ptr_ty),
        hir_ty::Ty::RawPtr { .. } => FinalTy::Pointer(ptr_ty),
        hir_ty::Ty::RawSlice { .. } => FinalTy::Pointer(ptr_ty),
        hir_ty::Ty::Void => FinalTy::Void,
        hir_ty::Ty::NoEval => FinalTy::Void,
        hir_ty::Ty::File(_) => FinalTy::Void,
    };

    {
        let mut finals = FINAL_TYS.lock().unwrap();
        let finals = finals.get_mut().unwrap();
        finals.finals.insert(ty, final_ty);
    }
}

pub(crate) const VOID_DISCRIMINANT: u32 = 1;
pub(crate) const INT_DISCRIMINANT: u32 = 2;
pub(crate) const FLOAT_DISCRIMINANT: u32 = 3;
pub(crate) const BOOL_DISCRIMINANT: u32 = 4;
pub(crate) const STRING_DISCRIMINANT: u32 = 5;
pub(crate) const CHAR_DISCRIMINANT: u32 = 6;
pub(crate) const META_TYPE_DISCRIMINANT: u32 = 7;
pub(crate) const ANY_DISCRIMINANT: u32 = 8;
pub(crate) const FILE_DISCRIMINANT: u32 = 9;
pub(crate) const RAW_PTR_DISCRIMINANT: u32 = 10;
pub(crate) const RAW_SLICE_DISCRIMINANT: u32 = 11;

pub(crate) const STRUCT_DISCRIMINANT: u32 = 16;
pub(crate) const DISTINCT_DISCRIMINANT: u32 = 17;
pub(crate) const ARRAY_DISCRIMINANT: u32 = 18;
pub(crate) const SLICE_DISCRIMINANT: u32 = 19;
pub(crate) const POINTER_DISCRIMINANT: u32 = 20;
pub(crate) const FUNCTION_DISCRIMINANT: u32 = 21;
pub(crate) const ENUM_DISCRIMINANT: u32 = 22;
pub(crate) const VARIANT_DISCRIMINANT: u32 = 23;

fn simple_id(discriminant: u32, bit_width: u32, signed: bool) -> u32 {
    let size = bit_width / 8;
    let align = size.clamp(1, 8);

    simple_id_with_align(discriminant, bit_width / 8, align, signed)
}

// `size` and `align` are in bytes
fn simple_id_with_align(discriminant: u32, size: u32, align: u32, signed: bool) -> u32 {
    assert!(discriminant < 0b111111);
    assert!(size < 0b11111);
    assert!(align < 0b1111);

    // the last 6 bits are reserved for the discriminant
    let id = discriminant << 26;

    let align = align << 5;

    let sign = (signed as u32) << 9;

    id | sign | align | size
}

pub(crate) trait ToTyId {
    fn to_type_id(self, meta_tys: &mut MetaTyData, pointer_ty: types::Type) -> u32;
    fn to_previous_type_id(self, meta_tys: &MetaTyData) -> u32;
}

impl ToTyId for Intern<Ty> {
    fn to_type_id(self, meta_tys: &mut MetaTyData, pointer_ty: types::Type) -> u32 {
        if let Some(id) = meta_tys
            .type_ids
            .iter()
            .find(|(ty, _)| ty.is_equal_to(&self))
            .map(|(_, id)| *id)
        {
            assert!(meta_tys
                .tys_to_compile
                .iter()
                .any(|ty| ty.is_equal_to(&self)));
            return id;
        }

        println!("{self:?}");

        assert!(!meta_tys
            .tys_to_compile
            .iter()
            .any(|ty| ty.is_equal_to(&self)));

        let id = match self.as_ref() {
            Ty::NotYetResolved | Ty::Unknown => simple_id(VOID_DISCRIMINANT, 0, false),
            Ty::UInt(0) | Ty::IInt(0) => simple_id(INT_DISCRIMINANT, 32, true),
            Ty::IInt(bit_width) => simple_id(
                INT_DISCRIMINANT,
                match *bit_width {
                    u8::MAX => pointer_ty.bits(),
                    other => other as u32,
                },
                true,
            ),
            Ty::UInt(bit_width) => simple_id(
                INT_DISCRIMINANT,
                match *bit_width {
                    u8::MAX => pointer_ty.bits(),
                    other => other as u32,
                },
                false,
            ),
            Ty::Float(0) => simple_id(FLOAT_DISCRIMINANT, 32, false),
            Ty::Float(bit_width) => simple_id(FLOAT_DISCRIMINANT, *bit_width as u32, false),
            Ty::Bool => simple_id(BOOL_DISCRIMINANT, 8, false),
            Ty::String => simple_id(STRING_DISCRIMINANT, pointer_ty.bits(), false),
            Ty::Char => simple_id(CHAR_DISCRIMINANT, 8, false),
            Ty::Type => simple_id(META_TYPE_DISCRIMINANT, 32, false),
            Ty::Any => simple_id_with_align(ANY_DISCRIMINANT, self.size(), self.align(), false),
            Ty::RawPtr { mutable } => simple_id_with_align(
                RAW_PTR_DISCRIMINANT,
                pointer_ty.bytes(),
                pointer_ty.bytes().min(8),
                *mutable,
            ),
            Ty::RawSlice => simple_id_with_align(
                RAW_SLICE_DISCRIMINANT,
                pointer_ty.bytes() * 2,
                pointer_ty.bytes().min(8),
                false,
            ),
            Ty::File(_) => simple_id(FILE_DISCRIMINANT, 0, false),
            Ty::Void | Ty::NoEval => simple_id(VOID_DISCRIMINANT, 0, false),
            Ty::Array { sub_ty, .. } => {
                let id = ARRAY_DISCRIMINANT << 26;

                // make sure to compile the sub type too
                sub_ty.to_type_id(meta_tys, pointer_ty);

                let list_id = meta_tys.array_uid_gen.generate_unique_id();

                id | list_id
            }
            Ty::Slice { sub_ty } => {
                let id = SLICE_DISCRIMINANT << 26;

                // make sure to compile the sub type too
                sub_ty.to_type_id(meta_tys, pointer_ty);

                let list_id = meta_tys.slice_uid_gen.generate_unique_id();

                id | list_id
            }
            Ty::Pointer { sub_ty, .. } => {
                let id = POINTER_DISCRIMINANT << 26;

                // make sure to compile the sub type too
                sub_ty.to_type_id(meta_tys, pointer_ty);

                let list_id = meta_tys.pointer_uid_gen.generate_unique_id();

                id | list_id
            }
            Ty::Distinct { sub_ty, .. } => {
                let id = DISTINCT_DISCRIMINANT << 26;

                // make sure to compile the sub type too
                sub_ty.to_type_id(meta_tys, pointer_ty);

                let list_id = meta_tys.distinct_uid_gen.generate_unique_id();

                id | list_id
            }
            Ty::Function { .. } => {
                let id = FUNCTION_DISCRIMINANT << 26;

                let list_id = meta_tys.function_uid_gen.generate_unique_id();

                id | list_id
            }
            Ty::Struct { members, .. } => {
                let id = STRUCT_DISCRIMINANT << 26;

                // make sure to compile the member types too
                for member in members {
                    member.ty.to_type_id(meta_tys, pointer_ty);
                }

                let list_id = meta_tys.struct_uid_gen.generate_unique_id();

                id | list_id
            }
            Ty::Enum { variants, .. } => {
                let id = ENUM_DISCRIMINANT << 26;

                // make sure to compile the variants too
                for variant in variants {
                    variant.to_type_id(meta_tys, pointer_ty);
                }

                let list_id = meta_tys.enum_uid_gen.generate_unique_id();

                id | list_id
            }
            Ty::Variant { sub_ty, .. } => {
                let id = VARIANT_DISCRIMINANT << 26;

                // make sure to compile the sub type too
                sub_ty.to_type_id(meta_tys, pointer_ty);

                let list_id = meta_tys.variant_uid_gen.generate_unique_id();

                id | list_id
            }
        };

        meta_tys.type_ids.push((self, id));

        meta_tys.tys_to_compile.push(self);

        id
    }

    #[track_caller]
    fn to_previous_type_id(self, meta_tys: &MetaTyData) -> u32 {
        meta_tys
            .type_ids
            .iter()
            .find(|(ty, _)| ty.is_equal_to(&self))
            .map(|(_, id)| *id)
            .expect("to_previous_type_id can only be called on types that have already been compiled to id's")
    }
}

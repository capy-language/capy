use core::panic;

use hir_ty::ResolvedTy;
use inkwell::{
    types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType, VoidType},
    AddressSpace,
};

use crate::gen::CodeGen;

pub(crate) enum CompType<'a> {
    Basic(BasicTypeEnum<'a>),
    Void(VoidType<'a>),
}

impl<'a> CompType<'a> {
    #[allow(dead_code)]
    pub(crate) fn is_basic_type(&self) -> bool {
        matches!(self, CompType::Basic(_))
    }

    #[allow(dead_code)]
    pub(crate) fn is_void_type(&self) -> bool {
        matches!(self, CompType::Void(_))
    }

    pub(crate) fn into_basic_type(self) -> BasicTypeEnum<'a> {
        match self {
            CompType::Basic(ty) => ty,
            _ => panic!("Expected BasicTypeEnum and found VoidType"),
        }
    }

    #[allow(dead_code)]
    pub(crate) fn into_void_type(self) -> VoidType<'a> {
        match self {
            CompType::Void(ty) => ty,
            _ => panic!("Expected VoidType and found BasicTypeEnum"),
        }
    }

    pub(crate) fn fn_type(&self, param_types: &[BasicMetadataTypeEnum<'a>]) -> FunctionType<'a> {
        match self {
            CompType::Basic(ty) => ty.fn_type(param_types, false),
            CompType::Void(ty) => ty.fn_type(param_types, false),
        }
    }
}

pub(crate) trait ToCompType {
    fn to_comp_type<'ctx>(&self, gen: &CodeGen<'_, 'ctx>) -> CompType<'ctx>;
}

impl ToCompType for ResolvedTy {
    fn to_comp_type<'ctx>(&self, gen: &CodeGen<'_, 'ctx>) -> CompType<'ctx> {
        match self {
            hir_ty::ResolvedTy::NotYetResolved | hir_ty::ResolvedTy::Unknown => unreachable!(),
            hir_ty::ResolvedTy::IInt(bit_width) | hir_ty::ResolvedTy::UInt(bit_width) => {
                match *bit_width {
                    u32::MAX => CompType::Basic(
                        gen.context
                            .ptr_sized_int_type(
                                &gen.target_machine.get_target_data(),
                                Some(AddressSpace::default()),
                            )
                            .as_basic_type_enum(),
                    ),
                    0 => CompType::Basic(gen.context.i32_type().as_basic_type_enum()),
                    other_width => CompType::Basic(
                        gen.context
                            .custom_width_int_type(other_width)
                            .as_basic_type_enum(),
                    ),
                }
            }
            hir_ty::ResolvedTy::Bool => {
                CompType::Basic(gen.context.bool_type().as_basic_type_enum())
            }
            hir_ty::ResolvedTy::String => CompType::Basic(
                gen.context
                    .i8_type()
                    .ptr_type(AddressSpace::default())
                    .as_basic_type_enum(),
            ),
            hir_ty::ResolvedTy::Array { size, sub_ty, .. } => CompType::Basic(
                gen.resolved_arena[*sub_ty]
                    .to_comp_type(gen)
                    .into_basic_type()
                    .array_type(*size as u32)
                    .as_basic_type_enum(),
            ),
            hir_ty::ResolvedTy::Pointer { sub_ty } => CompType::Basic(
                gen.resolved_arena[*sub_ty]
                    .to_comp_type(gen)
                    .into_basic_type()
                    .ptr_type(AddressSpace::default())
                    .as_basic_type_enum(),
            ),
            hir_ty::ResolvedTy::Distinct { ty, .. } => gen.resolved_arena[*ty].to_comp_type(gen),
            hir_ty::ResolvedTy::Type => CompType::Void(gen.context.void_type()),
            hir_ty::ResolvedTy::Named(_) => todo!(),
            hir_ty::ResolvedTy::Void => CompType::Void(gen.context.void_type()),
        }
    }
}

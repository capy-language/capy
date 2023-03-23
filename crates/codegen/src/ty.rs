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
        match self {
            CompType::Basic(_) => true,
            _ => false,
        }
    }

    #[allow(dead_code)]
    pub(crate) fn is_void_type(&self) -> bool {
        match self {
            CompType::Void(_) => true,
            _ => false,
        }
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

impl ToCompType for hir::TyWithRange {
    fn to_comp_type<'ctx>(&self, gen: &CodeGen<'_, 'ctx>) -> CompType<'ctx> {
        match self {
            hir::TyWithRange::Unknown => unreachable!(),
            hir::TyWithRange::IInt { bit_width, .. } | hir::TyWithRange::UInt { bit_width, .. } => {
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
            hir::TyWithRange::Bool { .. } => {
                CompType::Basic(gen.context.bool_type().as_basic_type_enum())
            }
            hir::TyWithRange::String { .. } => CompType::Basic(
                gen.context
                    .i8_type()
                    .ptr_type(AddressSpace::default())
                    .as_basic_type_enum(),
            ),
            hir::TyWithRange::Array { size, sub_ty, .. } => CompType::Basic(
                sub_ty
                    .to_comp_type(gen)
                    .into_basic_type()
                    .array_type(*size as u32)
                    .as_basic_type_enum(),
            ),
            hir::TyWithRange::Named { .. } => todo!(),
            hir::TyWithRange::Void { .. } => CompType::Void(gen.context.void_type()),
        }
    }
}

impl ToCompType for ResolvedTy {
    fn to_comp_type<'ctx>(&self, gen: &CodeGen<'_, 'ctx>) -> CompType<'ctx> {
        match self {
            hir_ty::ResolvedTy::Unknown => unreachable!(),
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
                sub_ty
                    .to_comp_type(gen)
                    .into_basic_type()
                    .array_type(*size as u32)
                    .as_basic_type_enum(),
            ),
            hir_ty::ResolvedTy::Named(_) => todo!(),
            hir_ty::ResolvedTy::Void => CompType::Void(gen.context.void_type()),
        }
    }
}

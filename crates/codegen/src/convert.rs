use cranelift::prelude::{types, AbiParam};
use cranelift_module::Module;
use hir_ty::ResolvedTy;
use la_arena::Arena;
use rustc_hash::FxHashMap;

use crate::{CapyFnSignature, CraneliftSignature};

#[derive(Clone, Copy)]
pub(crate) enum CompType {
    Int(IntType),
    Pointer(types::Type),
    Void,
}

#[derive(Clone, Copy)]
pub(crate) struct IntType {
    pub(crate) ty: types::Type,
    pub(crate) bit_width: u8,
    pub(crate) signed: bool,
}

impl CompType {
    #[allow(unused)]
    pub(crate) fn is_int_type(&self) -> bool {
        matches!(self, CompType::Int(_))
    }

    pub(crate) fn is_pointer_type(&self) -> bool {
        matches!(self, CompType::Pointer(_))
    }

    #[allow(unused)]
    pub(crate) fn is_void_type(&self) -> bool {
        matches!(self, CompType::Void)
    }

    pub(crate) fn into_real_type(self) -> Option<types::Type> {
        match self {
            CompType::Int(IntType { ty, .. }) => Some(ty),
            CompType::Pointer(ty) => Some(ty),
            _ => None,
        }
    }

    pub(crate) fn into_int_type(self) -> Option<IntType> {
        match self {
            CompType::Int(int_ty) => Some(int_ty),
            _ => None,
        }
    }
}

pub(crate) trait ToCompType {
    fn to_comp_type(&self, module: &dyn Module, resolved_arena: &Arena<ResolvedTy>) -> CompType;
}

impl ToCompType for ResolvedTy {
    fn to_comp_type(&self, module: &dyn Module, resolved_arena: &Arena<ResolvedTy>) -> CompType {
        match self {
            hir_ty::ResolvedTy::NotYetResolved | hir_ty::ResolvedTy::Unknown => unreachable!(),
            hir_ty::ResolvedTy::IInt(bit_width) => match *bit_width {
                u32::MAX => CompType::Int(IntType {
                    ty: module.target_config().pointer_type(),
                    bit_width: module.target_config().pointer_width.bits(),
                    signed: true,
                }),
                0 => CompType::Int(IntType {
                    ty: types::I32,
                    bit_width: 32,
                    signed: true,
                }),
                8 => CompType::Int(IntType {
                    ty: types::I8,
                    bit_width: 8,
                    signed: true,
                }),
                16 => CompType::Int(IntType {
                    ty: types::I16,
                    bit_width: 16,
                    signed: true,
                }),
                32 => CompType::Int(IntType {
                    ty: types::I32,
                    bit_width: 32,
                    signed: true,
                }),
                64 => CompType::Int(IntType {
                    ty: types::I64,
                    bit_width: 64,
                    signed: true,
                }),
                128 => CompType::Int(IntType {
                    ty: types::I128,
                    bit_width: 128,
                    signed: true,
                }),
                _ => unreachable!(),
            },
            hir_ty::ResolvedTy::UInt(bit_width) => match *bit_width {
                u32::MAX => CompType::Int(IntType {
                    ty: module.target_config().pointer_type(),
                    bit_width: module.target_config().pointer_width.bits(),
                    signed: false,
                }),
                0 => CompType::Int(IntType {
                    ty: types::I32,
                    bit_width: 32,
                    signed: false,
                }),
                8 => CompType::Int(IntType {
                    ty: types::I8,
                    bit_width: 8,
                    signed: false,
                }),
                16 => CompType::Int(IntType {
                    ty: types::I16,
                    bit_width: 16,
                    signed: false,
                }),
                32 => CompType::Int(IntType {
                    ty: types::I32,
                    bit_width: 32,
                    signed: false,
                }),
                64 => CompType::Int(IntType {
                    ty: types::I64,
                    bit_width: 64,
                    signed: false,
                }),
                128 => CompType::Int(IntType {
                    ty: types::I128,
                    bit_width: 128,
                    signed: false,
                }),
                _ => unreachable!(),
            },
            hir_ty::ResolvedTy::Bool => CompType::Int(IntType {
                ty: types::I8,
                bit_width: 8,
                signed: false,
            }),
            hir_ty::ResolvedTy::String => CompType::Pointer(module.target_config().pointer_type()),
            hir_ty::ResolvedTy::Array { .. } => {
                CompType::Pointer(module.target_config().pointer_type())
            }
            hir_ty::ResolvedTy::Pointer { .. } => {
                CompType::Pointer(module.target_config().pointer_type())
            }
            hir_ty::ResolvedTy::Distinct { ty, .. } => {
                resolved_arena[*ty].to_comp_type(module, resolved_arena)
            }
            hir_ty::ResolvedTy::Type => CompType::Void,
            hir_ty::ResolvedTy::Named(_) => todo!(),
            hir_ty::ResolvedTy::Void => CompType::Void,
        }
    }
}

pub(crate) trait ToCraneliftSignature {
    fn to_cranelift_signature(
        &self,
        module: &dyn Module,
        resolved_arena: &Arena<ResolvedTy>,
    ) -> (CraneliftSignature, FxHashMap<u64, u64>);
}

impl ToCraneliftSignature for CapyFnSignature {
    fn to_cranelift_signature(
        &self,
        module: &dyn Module,
        resolved_arena: &Arena<ResolvedTy>,
    ) -> (CraneliftSignature, FxHashMap<u64, u64>) {
        let mut real_ty_count = 0;

        let mut new_idx_to_old_idx = FxHashMap::default();

        let mut param_types = self
            .param_tys
            .iter()
            .enumerate()
            .filter_map(|(idx, param_ty)| {
                let param_ty = match param_ty {
                    hir_ty::ResolvedTy::Void { .. } => None,
                    other_ty => Some(AbiParam::new(
                        other_ty
                            .to_comp_type(module, resolved_arena)
                            .into_real_type()
                            .unwrap(),
                    )),
                };
                if param_ty.is_some() {
                    new_idx_to_old_idx.insert(real_ty_count, idx as u64);
                    real_ty_count += 1;
                }
                param_ty
            })
            .collect::<Vec<_>>();

        if self.return_ty.is_array(resolved_arena) {
            // if the callee is expected to return an array,
            // the caller function must supply a memory address
            // to store it in
            param_types.push(AbiParam::new(module.target_config().pointer_type()));
        }

        (
            CraneliftSignature {
                params: param_types,
                returns: self
                    .return_ty
                    .to_comp_type(module, resolved_arena)
                    .into_real_type()
                    .map(|ty| vec![AbiParam::new(ty)])
                    .unwrap_or_default(),
                call_conv: module.target_config().default_call_conv,
            },
            new_idx_to_old_idx,
        )
    }
}

pub(crate) trait ToCompSize {
    fn get_size_in_bytes(&self, module: &dyn Module, resolved_arena: &Arena<ResolvedTy>) -> u32;
}

impl ToCompSize for ResolvedTy {
    fn get_size_in_bytes(&self, module: &dyn Module, resolved_arena: &Arena<ResolvedTy>) -> u32 {
        match self {
            ResolvedTy::NotYetResolved | ResolvedTy::Unknown => unreachable!(),
            ResolvedTy::IInt(u32::MAX) | ResolvedTy::UInt(u32::MAX) => {
                module.target_config().pointer_bytes() as u32
            }
            ResolvedTy::IInt(0) | ResolvedTy::UInt(0) => 32 / 8,
            ResolvedTy::IInt(bit_width) | ResolvedTy::UInt(bit_width) => bit_width / 8,
            ResolvedTy::Bool => 8, // bools are a u8
            ResolvedTy::String => module.target_config().pointer_bytes() as u32,
            ResolvedTy::Array { size, sub_ty } => {
                resolved_arena[*sub_ty].get_size_in_bytes(module, resolved_arena) * *size as u32
            }
            ResolvedTy::Pointer { .. } => module.target_config().pointer_bytes() as u32,
            ResolvedTy::Distinct { ty, .. } => {
                resolved_arena[*ty].get_size_in_bytes(module, resolved_arena)
            }
            ResolvedTy::Type => 0,
            ResolvedTy::Named(_) => todo!(),
            ResolvedTy::Void => 0,
        }
    }
}

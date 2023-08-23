use cranelift::prelude::{types, AbiParam};
use cranelift_module::Module;
use hir_ty::ResolvedTy;
use la_arena::Arena;
use rustc_hash::FxHashMap;

use crate::{CapyFnSignature, CraneliftSignature};

#[derive(Clone, Copy)]
pub(crate) enum CompType {
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

impl CompType {
    #[allow(unused)]
    pub(crate) fn is_number_type(&self) -> bool {
        matches!(self, CompType::Number(_))
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
            CompType::Number(NumberType { ty, .. }) => Some(ty),
            CompType::Pointer(ty) => Some(ty),
            _ => None,
        }
    }

    pub(crate) fn into_number_type(self) -> Option<NumberType> {
        match self {
            CompType::Number(number_ty) => Some(number_ty),
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
            hir_ty::ResolvedTy::IInt(bit_width) | hir_ty::ResolvedTy::UInt(bit_width) => {
                let signed = matches!(self, hir_ty::ResolvedTy::IInt(_));

                match *bit_width {
                    u32::MAX => CompType::Number(NumberType {
                        ty: module.target_config().pointer_type(),
                        float: false,
                        signed,
                    }),
                    0 => CompType::Number(NumberType {
                        ty: types::I32,
                        float: false,
                        signed,
                    }),
                    8 => CompType::Number(NumberType {
                        ty: types::I8,
                        float: false,
                        signed,
                    }),
                    16 => CompType::Number(NumberType {
                        ty: types::I16,
                        float: false,
                        signed,
                    }),
                    32 => CompType::Number(NumberType {
                        ty: types::I32,
                        float: false,
                        signed,
                    }),
                    64 => CompType::Number(NumberType {
                        ty: types::I64,
                        float: false,
                        signed,
                    }),
                    128 => CompType::Number(NumberType {
                        ty: types::I128,
                        float: false,
                        signed,
                    }),
                    _ => unreachable!(),
                }
            }
            hir_ty::ResolvedTy::Float(bit_width) => match bit_width {
                0 => CompType::Number(NumberType {
                    ty: types::F32,
                    float: true,
                    signed: true,
                }),
                32 => CompType::Number(NumberType {
                    ty: types::F32,
                    float: true,
                    signed: true,
                }),
                64 => CompType::Number(NumberType {
                    ty: types::F32,
                    float: true,
                    signed: true,
                }),
                _ => unreachable!(),
            },
            hir_ty::ResolvedTy::Bool => CompType::Number(NumberType {
                ty: types::I8,
                float: false,
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
            ResolvedTy::Float(0) => 32 / 8,
            ResolvedTy::Float(bit_width) => bit_width / 8,
            ResolvedTy::Bool => 8, // bools are u8's
            ResolvedTy::String => module.target_config().pointer_bytes() as u32,
            ResolvedTy::Array { size, sub_ty } => {
                resolved_arena[*sub_ty].get_size_in_bytes(module, resolved_arena) * *size as u32
            }
            ResolvedTy::Pointer { .. } => module.target_config().pointer_bytes() as u32,
            ResolvedTy::Distinct { ty, .. } => {
                resolved_arena[*ty].get_size_in_bytes(module, resolved_arena)
            }
            ResolvedTy::Type => 0,
            ResolvedTy::Void => 0,
        }
    }
}

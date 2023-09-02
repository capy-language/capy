use cranelift::prelude::{types, AbiParam};
use cranelift_module::Module;
use hir_ty::ResolvedTy;
use internment::Intern;
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
    fn to_comp_type(&self, module: &dyn Module) -> CompType;
}

impl ToCompType for ResolvedTy {
    fn to_comp_type(&self, module: &dyn Module) -> CompType {
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
            hir_ty::ResolvedTy::Distinct { ty, .. } => ty.to_comp_type(module),
            hir_ty::ResolvedTy::Function { .. } => {
                CompType::Pointer(module.target_config().pointer_type())
            }
            hir_ty::ResolvedTy::Struct { .. } => {
                CompType::Pointer(module.target_config().pointer_type())
            }
            hir_ty::ResolvedTy::Type => CompType::Void,
            hir_ty::ResolvedTy::Void => CompType::Void,
            hir_ty::ResolvedTy::Module(_) => CompType::Void,
        }
    }
}

pub(crate) trait ToCraneliftSignature {
    fn to_cranelift_signature(
        &self,
        module: &dyn Module,
    ) -> (CraneliftSignature, FxHashMap<u64, u64>);
}

impl ToCraneliftSignature for CapyFnSignature {
    fn to_cranelift_signature(
        &self,
        module: &dyn Module,
    ) -> (CraneliftSignature, FxHashMap<u64, u64>) {
        (self.param_tys.clone(), self.return_ty).to_cranelift_signature(module)
    }
}

impl ToCraneliftSignature for (Vec<Intern<ResolvedTy>>, Intern<ResolvedTy>) {
    fn to_cranelift_signature(
        &self,
        module: &dyn Module,
    ) -> (CraneliftSignature, FxHashMap<u64, u64>) {
        let (param_tys, return_ty) = self;

        let mut real_ty_count = 0;

        let mut new_idx_to_old_idx = FxHashMap::default();

        let mut param_types = param_tys
            .iter()
            .enumerate()
            .filter_map(|(idx, param_ty)| {
                let param_ty = match param_ty.as_ref() {
                    hir_ty::ResolvedTy::Void { .. } => None,
                    other_ty => Some(AbiParam::new(
                        other_ty.to_comp_type(module).into_real_type().unwrap(),
                    )),
                };
                if param_ty.is_some() {
                    new_idx_to_old_idx.insert(real_ty_count, idx as u64);
                    real_ty_count += 1;
                }
                param_ty
            })
            .collect::<Vec<_>>();

        if return_ty.is_aggregate() {
            // if the callee is expected to return an array,
            // the caller function must supply a memory address
            // to store it in
            param_types.push(AbiParam::new(module.target_config().pointer_type()));
        }

        (
            CraneliftSignature {
                params: param_types,
                returns: return_ty
                    .to_comp_type(module)
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
    fn get_size_in_bytes(&self, module: &dyn Module) -> u32;

    /// Most types must appear in addresses that are a mutliple of a certain "alignment".
    /// This is a restriction of the underlying architechture.
    ///
    /// For example, the alignment of `i16` is `2`
    ///
    /// If the alignment is `2` and the address is not an even number,
    /// padding will be added to accomidate the `i16`.
    ///
    /// An alignment of `1` is accepted in all
    /// memory locations
    fn get_align_in_bytes(&self, module: &dyn Module) -> u32;
}

impl ToCompSize for ResolvedTy {
    fn get_size_in_bytes(&self, module: &dyn Module) -> u32 {
        match self {
            ResolvedTy::NotYetResolved | ResolvedTy::Unknown => unreachable!(),
            ResolvedTy::IInt(u32::MAX) | ResolvedTy::UInt(u32::MAX) => {
                module.target_config().pointer_bytes() as u32
            }
            ResolvedTy::IInt(0) | ResolvedTy::UInt(0) => 32 / 8,
            ResolvedTy::IInt(bit_width) | ResolvedTy::UInt(bit_width) => bit_width / 8,
            ResolvedTy::Float(0) => 32 / 8,
            ResolvedTy::Float(bit_width) => bit_width / 8,
            ResolvedTy::Bool => 1, // bools are u8's
            ResolvedTy::String => module.target_config().pointer_bytes() as u32,
            ResolvedTy::Array { size, sub_ty } => sub_ty.get_size_in_bytes(module) * *size as u32,
            ResolvedTy::Pointer { .. } => module.target_config().pointer_bytes() as u32,
            ResolvedTy::Distinct { ty, .. } => ty.get_size_in_bytes(module),
            ResolvedTy::Function { .. } => module.target_config().pointer_bytes() as u32,
            ResolvedTy::Struct { fields, .. } => {
                let fields = fields.iter().map(|(_, ty)| ty).copied().collect();
                StructMemory::new(fields, module).size
            }
            ResolvedTy::Type => 0,
            ResolvedTy::Void => 0,
            ResolvedTy::Module(_) => 0,
        }
    }

    fn get_align_in_bytes(&self, module: &dyn Module) -> u32 {
        match self {
            ResolvedTy::NotYetResolved | ResolvedTy::Unknown => unreachable!(),
            ResolvedTy::IInt(_) | ResolvedTy::UInt(_) | ResolvedTy::Float(_) => {
                self.get_size_in_bytes(module).min(8)
            }
            ResolvedTy::Bool => 1, // bools are u8's
            ResolvedTy::String
            | ResolvedTy::Array { .. }
            | ResolvedTy::Pointer { .. }
            | ResolvedTy::Distinct { .. }
            | ResolvedTy::Function { .. } => self.get_size_in_bytes(module),
            ResolvedTy::Struct { fields, .. } => fields
                .iter()
                .map(|(_, ty)| ty.get_align_in_bytes(module))
                .max()
                .unwrap_or(1), // the struct may be empty, in which case it should have an alignment of 1
            ResolvedTy::Type => 1,
            ResolvedTy::Void => 1,
            ResolvedTy::Module(_) => 1,
        }
    }
}

pub(crate) struct StructMemory {
    size: u32,
    offsets: Vec<u32>,
}

impl StructMemory {
    /// checks if the offset is a multiple of the alignment
    ///
    /// if not, returns the amount of bytes needed
    /// to make it a valid offset
    fn padding_needed_for(offset: u32, align: u32) -> u32 {
        let misalign = offset % align;
        if misalign > 0 {
            // the amount needed to round up to the next proper offset
            align - misalign
        } else {
            0
        }
    }

    pub(crate) fn new(fields: Vec<Intern<ResolvedTy>>, module: &dyn Module) -> Self {
        let mut offsets = Vec::with_capacity(fields.len());
        let mut max_align = 1;
        let mut current_offset = 0;

        for field in fields {
            let field_align = field.get_align_in_bytes(module);
            if field_align > max_align {
                max_align = field_align;
            }

            current_offset += Self::padding_needed_for(current_offset, field_align);

            offsets.push(current_offset);

            current_offset += field.get_size_in_bytes(module);
        }

        Self {
            size: current_offset + Self::padding_needed_for(current_offset, max_align),
            offsets,
        }
    }

    pub(crate) fn size(&self) -> u32 {
        self.size
    }

    pub(crate) fn offsets(&self) -> &Vec<u32> {
        &self.offsets
    }
}

use cranelift::prelude::{types, AbiParam};
use cranelift_module::Module;
use hir_ty::Ty;
use internment::Intern;
use rustc_hash::FxHashMap;

use crate::CraneliftSignature;

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
    fn to_comp_type(&self, pointer_ty: types::Type) -> CompType;
}

impl ToCompType for Ty {
    fn to_comp_type(&self, pointer_ty: types::Type) -> CompType {
        match self {
            hir_ty::Ty::NotYetResolved | hir_ty::Ty::Unknown => unreachable!(),
            hir_ty::Ty::IInt(bit_width) | hir_ty::Ty::UInt(bit_width) => {
                let signed = matches!(self, hir_ty::Ty::IInt(_));

                match *bit_width {
                    u32::MAX => CompType::Number(NumberType {
                        ty: pointer_ty,
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
            hir_ty::Ty::Float(bit_width) => match bit_width {
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
                    ty: types::F64,
                    float: true,
                    signed: true,
                }),
                _ => unreachable!(),
            },
            hir_ty::Ty::Bool | hir_ty::Ty::Char => CompType::Number(NumberType {
                ty: types::I8,
                float: false,
                signed: false,
            }),
            hir_ty::Ty::String => CompType::Pointer(pointer_ty),
            hir_ty::Ty::Array { .. } => CompType::Pointer(pointer_ty),
            hir_ty::Ty::Pointer { .. } => CompType::Pointer(pointer_ty),
            hir_ty::Ty::Distinct { ty, .. } => ty.to_comp_type(pointer_ty),
            hir_ty::Ty::Function { .. } => CompType::Pointer(pointer_ty),
            hir_ty::Ty::Struct { .. } => CompType::Pointer(pointer_ty),
            hir_ty::Ty::Type => CompType::Void,
            // you should never be able to get an any value
            hir_ty::Ty::Any => CompType::Void,
            hir_ty::Ty::Void => CompType::Void,
            hir_ty::Ty::File(_) => CompType::Void,
        }
    }
}

pub(crate) trait ToCraneliftSignature {
    fn to_cranelift_signature(
        &self,
        module: &dyn Module,
        pointer_ty: types::Type,
    ) -> (CraneliftSignature, FxHashMap<u64, u64>);
}

impl ToCraneliftSignature for (&Vec<Intern<Ty>>, Intern<Ty>) {
    fn to_cranelift_signature(
        &self,
        module: &dyn Module,
        pointer_ty: types::Type,
    ) -> (CraneliftSignature, FxHashMap<u64, u64>) {
        let (param_tys, return_ty) = self;

        let mut real_ty_count = 0;

        let mut new_idx_to_old_idx = FxHashMap::default();

        let mut param_types = param_tys
            .iter()
            .enumerate()
            .filter_map(|(idx, param_ty)| {
                let param_ty = match param_ty.as_ref() {
                    hir_ty::Ty::Void { .. } => None,
                    other_ty => Some(AbiParam::new(
                        other_ty.to_comp_type(pointer_ty).into_real_type().unwrap(),
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
            param_types.push(AbiParam::new(pointer_ty));
        }

        (
            CraneliftSignature {
                params: param_types,
                returns: return_ty
                    .to_comp_type(pointer_ty)
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
    fn get_size_in_bytes(&self, pointer_ty: types::Type) -> u32;

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
    fn get_align_in_bytes(&self, pointer_ty: types::Type) -> u32;
}

impl ToCompSize for Ty {
    fn get_size_in_bytes(&self, pointer_ty: types::Type) -> u32 {
        match self {
            Ty::NotYetResolved | Ty::Unknown => unreachable!(),
            Ty::IInt(u32::MAX) | Ty::UInt(u32::MAX) => pointer_ty.bytes(),
            Ty::IInt(0) | Ty::UInt(0) => 32 / 8,
            Ty::IInt(bit_width) | Ty::UInt(bit_width) => bit_width / 8,
            Ty::Float(0) => 32 / 8,
            Ty::Float(bit_width) => bit_width / 8,
            Ty::Bool | Ty::Char => 1, // bools and chars are u8's
            Ty::String => pointer_ty.bytes(),
            Ty::Array { size, sub_ty } => sub_ty.get_size_in_bytes(pointer_ty) * *size as u32,
            Ty::Pointer { .. } => pointer_ty.bytes(),
            Ty::Distinct { ty, .. } => ty.get_size_in_bytes(pointer_ty),
            Ty::Function { .. } => pointer_ty.bytes(),
            Ty::Struct { fields, .. } => {
                let fields = fields.iter().map(|(_, ty)| ty).copied().collect();
                StructMemory::new(fields, pointer_ty).size
            }
            Ty::Type => 0,
            Ty::Any => 0,
            Ty::Void => 0,
            Ty::File(_) => 0,
        }
    }

    fn get_align_in_bytes(&self, pointer_ty: types::Type) -> u32 {
        match self {
            Ty::NotYetResolved | Ty::Unknown => unreachable!(),
            Ty::IInt(_) | Ty::UInt(_) | Ty::Float(_) => self.get_size_in_bytes(pointer_ty).min(8),
            Ty::Bool | Ty::Char => 1, // bools and chars are u8's
            Ty::String | Ty::Pointer { .. } | Ty::Function { .. } => pointer_ty.bytes(),
            Ty::Array { sub_ty, .. } => sub_ty.get_align_in_bytes(pointer_ty),
            Ty::Distinct { ty, .. } => ty.get_align_in_bytes(pointer_ty),
            Ty::Struct { fields, .. } => fields
                .iter()
                .map(|(_, ty)| ty.get_align_in_bytes(pointer_ty))
                .max()
                .unwrap_or(1), // the struct may be empty, in which case it should have an alignment of 1
            Ty::Type => 1,
            Ty::Any => 1,
            Ty::Void => 1,
            Ty::File(_) => 1,
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

    pub(crate) fn new(fields: Vec<Intern<Ty>>, pointer_ty: types::Type) -> Self {
        let mut offsets = Vec::with_capacity(fields.len());
        let mut max_align = 1;
        let mut current_offset = 0;

        for field in fields {
            let field_align = field.get_align_in_bytes(pointer_ty);
            if field_align > max_align {
                max_align = field_align;
            }

            current_offset += Self::padding_needed_for(current_offset, field_align);

            offsets.push(current_offset);

            current_offset += field.get_size_in_bytes(pointer_ty);
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

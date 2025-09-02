use cranelift::prelude::{types, AbiParam};
use cranelift_module::{FuncId, Linkage, Module};
use hir_ty::BuiltinKind;
use interner::Interner;

use crate::{mangle::Mangle, FinalSignature};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum BuiltinGlobal {
    /// type layout (size/align) arrays
    ArrayLayouts,
    DistinctLayouts,
    StructLayouts,
    EnumLayouts,
    VariantLayouts,
    OptionalLayouts,
    ErrorUnionLayouts,

    /// a single slice for the size/align of usize
    PointerLayout,

    /// type info arrays
    ArrayInfos,
    SliceInfos,
    PointerInfos,
    DistinctInfos,
    StructInfos,
    EnumInfos,
    VariantInfos,
    OptionalInfos,
    ErrorUnionInfos,

    /// misc.
    CommandlineArgs,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum BuiltinFunction {
    PtrBitcast,
    ConcreteBitcast(types::Type),
}

impl BuiltinFunction {
    pub(crate) fn to_sig_and_func_id(
        self,
        module: &mut dyn Module,
        ptr_ty: types::Type,
        mod_dir: &std::path::Path,
        interner: &Interner,
    ) -> (String, FinalSignature, FuncId) {
        let ftc = match self {
            BuiltinFunction::PtrBitcast => FinalSignature {
                params: vec![AbiParam::new(ptr_ty)],
                returns: vec![AbiParam::new(ptr_ty)],
                call_conv: module.target_config().default_call_conv,
            },
            BuiltinFunction::ConcreteBitcast(ty) => FinalSignature {
                params: vec![AbiParam::new(ty)],
                returns: vec![AbiParam::new(ty)],
                call_conv: module.target_config().default_call_conv,
            },
        };
        let mangled = self.to_mangled_name(mod_dir, interner);
        let func_id = module
            .declare_function(&mangled, Linkage::Export, &ftc)
            .unwrap();

        (mangled, ftc, func_id)
    }
}

impl From<hir_ty::BuiltinKind> for BuiltinGlobal {
    fn from(value: hir_ty::BuiltinKind) -> Self {
        match value {
            hir_ty::BuiltinKind::LayoutSlice {
                sub_kind: hir_ty::BuiltinSubKind::Array,
            } => BuiltinGlobal::ArrayLayouts,
            hir_ty::BuiltinKind::LayoutSlice {
                sub_kind: hir_ty::BuiltinSubKind::Distinct,
            } => BuiltinGlobal::DistinctLayouts,
            hir_ty::BuiltinKind::LayoutSlice {
                sub_kind: hir_ty::BuiltinSubKind::Struct,
            } => BuiltinGlobal::StructLayouts,
            hir_ty::BuiltinKind::LayoutSlice {
                sub_kind: hir_ty::BuiltinSubKind::Enum,
            } => BuiltinGlobal::EnumLayouts,
            hir_ty::BuiltinKind::LayoutSlice {
                sub_kind: hir_ty::BuiltinSubKind::Variant,
            } => BuiltinGlobal::VariantLayouts,
            hir_ty::BuiltinKind::LayoutSlice {
                sub_kind: hir_ty::BuiltinSubKind::Optional,
            } => BuiltinGlobal::OptionalLayouts,
            hir_ty::BuiltinKind::LayoutSlice {
                sub_kind: hir_ty::BuiltinSubKind::ErrorUnion,
            } => BuiltinGlobal::ErrorUnionLayouts,
            hir_ty::BuiltinKind::LayoutSlice { .. } => unimplemented!(),

            hir_ty::BuiltinKind::SingleLayout {
                sub_kind: hir_ty::BuiltinSubKind::Pointer,
            } => BuiltinGlobal::PointerLayout,
            hir_ty::BuiltinKind::SingleLayout { .. } => unimplemented!(),

            hir_ty::BuiltinKind::InfoSlice {
                sub_kind: hir_ty::BuiltinSubKind::Array,
            } => BuiltinGlobal::ArrayInfos,
            hir_ty::BuiltinKind::InfoSlice {
                sub_kind: hir_ty::BuiltinSubKind::Slice,
            } => BuiltinGlobal::SliceInfos,
            hir_ty::BuiltinKind::InfoSlice {
                sub_kind: hir_ty::BuiltinSubKind::Pointer,
            } => BuiltinGlobal::PointerInfos,
            hir_ty::BuiltinKind::InfoSlice {
                sub_kind: hir_ty::BuiltinSubKind::Distinct,
            } => BuiltinGlobal::DistinctInfos,
            hir_ty::BuiltinKind::InfoSlice {
                sub_kind: hir_ty::BuiltinSubKind::Struct,
            } => BuiltinGlobal::StructInfos,
            hir_ty::BuiltinKind::InfoSlice {
                sub_kind: hir_ty::BuiltinSubKind::Enum,
            } => BuiltinGlobal::EnumInfos,
            hir_ty::BuiltinKind::InfoSlice {
                sub_kind: hir_ty::BuiltinSubKind::Variant,
            } => BuiltinGlobal::VariantInfos,
            hir_ty::BuiltinKind::InfoSlice {
                sub_kind: hir_ty::BuiltinSubKind::Optional,
            } => BuiltinGlobal::OptionalInfos,
            hir_ty::BuiltinKind::InfoSlice {
                sub_kind: hir_ty::BuiltinSubKind::ErrorUnion,
            } => BuiltinGlobal::ErrorUnionInfos,

            hir_ty::BuiltinKind::CommandlineArgs => BuiltinGlobal::CommandlineArgs,

            _ => unreachable!("none of the other builtin kinds are globals"),
        }
    }
}

impl From<BuiltinKind> for BuiltinFunction {
    fn from(value: BuiltinKind) -> Self {
        match value {
            // we can ignore the `opt` field because opt pointers are the same size are regular
            // pointers
            hir_ty::BuiltinKind::PtrToRaw { .. } => BuiltinFunction::PtrBitcast,
            hir_ty::BuiltinKind::PtrFromRaw { .. } => BuiltinFunction::PtrBitcast,
            hir_ty::BuiltinKind::MetaToRaw => BuiltinFunction::ConcreteBitcast(types::I32),
            _ => unreachable!("none of the other builtins are functions"),
        }
    }
}

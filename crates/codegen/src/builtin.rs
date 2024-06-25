use std::path::Path;

use cranelift::prelude::{types, AbiParam};
use cranelift_module::{FuncId, Linkage, Module};
use interner::Interner;

use crate::{compiler::FunctionToCompile, mangle::Mangle, FinalSignature};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum BuiltinGlobal {
    /// type layout (size/align) arrays
    ArrayLayouts,
    DistinctLayouts,
    StructLayouts,

    /// a single slice for the size/align of usize
    PointerLayout,

    /// type info arrays
    ArrayInfo,
    SliceInfo,
    PointerInfo,
    DistinctInfo,
    StructInfo,

    /// misc.
    CommandlineArgs,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum BuiltinFunction {
    PtrBitcast,
    I32Bitcast,
}

impl BuiltinFunction {
    pub(crate) fn to_sig_and_func_id(
        self,
        module: &mut dyn Module,
        pointer_ty: types::Type,
        mod_dir: &std::path::Path,
        interner: &Interner,
    ) -> (String, FinalSignature, FuncId) {
        let ftc = match self {
            BuiltinFunction::PtrBitcast => FinalSignature {
                params: vec![AbiParam::new(pointer_ty)],
                returns: vec![AbiParam::new(pointer_ty)],
                call_conv: module.target_config().default_call_conv,
            },
            BuiltinFunction::I32Bitcast => FinalSignature {
                params: vec![AbiParam::new(types::I32)],
                returns: vec![AbiParam::new(types::I32)],
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

pub(crate) fn as_compiler_defined_global(
    fqn: hir::Fqn,
    mod_dir: &Path,
    interner: &Interner,
) -> Option<BuiltinGlobal> {
    let is_core = fqn
        .file
        .get_mod_name(mod_dir, interner)
        .map_or(false, |n| n == "core");

    if !is_core {
        return None;
    }

    let file_name = Path::new(interner.lookup(fqn.file.0))
        .file_name()
        .unwrap_or_default()
        .to_string_lossy();

    let function_name = interner.lookup(fqn.name.0);

    Some(match (file_name.as_ref(), function_name) {
        ("meta.capy", "array_layouts") => BuiltinGlobal::ArrayLayouts,
        ("meta.capy", "distinct_layouts") => BuiltinGlobal::DistinctLayouts,
        ("meta.capy", "struct_layouts") => BuiltinGlobal::StructLayouts,
        ("meta.capy", "pointer_layout") => BuiltinGlobal::PointerLayout,
        ("meta.capy", "array_infos") => BuiltinGlobal::ArrayInfo,
        ("meta.capy", "slice_infos") => BuiltinGlobal::SliceInfo,
        ("meta.capy", "pointer_infos") => BuiltinGlobal::PointerInfo,
        ("meta.capy", "distinct_infos") => BuiltinGlobal::DistinctInfo,
        ("meta.capy", "struct_infos") => BuiltinGlobal::StructInfo,
        ("mod.capy", "args") => BuiltinGlobal::CommandlineArgs,
        _ => return None,
    })
}

pub(crate) fn as_compiler_defined_func(
    is_extern: bool,
    ftc: &FunctionToCompile,
    mod_dir: &Path,
    interner: &Interner,
) -> Option<BuiltinFunction> {
    if !is_extern {
        return None;
    }

    let fqn = if let Some(name) = ftc.function_name {
        hir::Fqn {
            file: ftc.file_name,
            name,
        }
    } else {
        return None;
    };

    let is_core = fqn
        .file
        .get_mod_name(mod_dir, interner)
        .map_or(false, |n| n == "core");

    if !is_core {
        return None;
    }

    let file_name = Path::new(interner.lookup(fqn.file.0))
        .file_name()
        .unwrap_or_default()
        .to_string_lossy();

    let function_name = interner.lookup(fqn.name.0);

    Some(match (file_name.as_ref(), function_name) {
        ("ptr.capy", "to_raw") => BuiltinFunction::PtrBitcast,
        ("ptr.capy", "const_from_raw") => BuiltinFunction::PtrBitcast,
        ("ptr.capy", "mut_from_raw") => BuiltinFunction::PtrBitcast,
        ("meta.capy", "meta_to_raw") => BuiltinFunction::I32Bitcast,
        _ => return None,
    })
}

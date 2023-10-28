use std::path::Path;

use cranelift::prelude::{types, AbiParam};
use cranelift_module::{FuncId, Linkage, Module};
use hir_ty::Ty;
use interner::Interner;

use crate::{compiler::FunctionToCompile, convert, mangle::Mangle, CraneliftSignature};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum BuiltinFunction {
    PtrBitcast,
    SizeOf,
    AlignOf,
    IsMetaOfType(u32),
    GetMetaInfo(u32),
}

impl BuiltinFunction {
    pub(crate) fn to_sig_and_func_id(
        self,
        module: &mut dyn Module,
        pointer_ty: types::Type,
        mod_dir: &std::path::Path,
        interner: &Interner,
    ) -> (String, CraneliftSignature, FuncId) {
        let ftc = match self {
            BuiltinFunction::PtrBitcast => CraneliftSignature {
                params: vec![AbiParam::new(pointer_ty)],
                returns: vec![AbiParam::new(pointer_ty)],
                call_conv: module.target_config().default_call_conv,
            },
            BuiltinFunction::SizeOf | BuiltinFunction::AlignOf => CraneliftSignature {
                params: vec![AbiParam::new(types::I32)],
                returns: vec![AbiParam::new(pointer_ty)],
                call_conv: module.target_config().default_call_conv,
            },
            BuiltinFunction::IsMetaOfType(_) => CraneliftSignature {
                params: vec![AbiParam::new(types::I32)],
                returns: vec![AbiParam::new(types::I8)],
                call_conv: module.target_config().default_call_conv,
            },
            BuiltinFunction::GetMetaInfo(..) => CraneliftSignature {
                params: vec![AbiParam::new(types::I32), AbiParam::new(pointer_ty)],
                returns: vec![AbiParam::new(pointer_ty)],
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

pub(crate) fn as_compiler_defined(
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
        ("ptr.capy", "to_raw") => ptr_to_usize(ftc),
        ("ptr.capy", "const_from_raw") => usize_to_ptr(ftc, false),
        ("ptr.capy", "mut_from_raw") => usize_to_ptr(ftc, true),
        ("meta.capy", "size_of") => meta_to_uint(ftc, true),
        ("meta.capy", "align_of") => meta_to_uint(ftc, false),
        ("meta.capy", "is_int") => meta_to_bool(ftc, convert::INT_DISCRIMINANT),
        ("meta.capy", "is_float") => meta_to_bool(ftc, convert::FLOAT_DISCRIMINANT),
        ("meta.capy", "is_bool") => meta_to_bool(ftc, convert::BOOL_DISCRIMINANT),
        ("meta.capy", "is_string") => meta_to_bool(ftc, convert::STRING_DISCRIMINANT),
        ("meta.capy", "is_char") => meta_to_bool(ftc, convert::CHAR_DISCRIMINANT),
        ("meta.capy", "is_array") => meta_to_bool(ftc, convert::ARRAY_DISCRIMINANT),
        ("meta.capy", "is_pointer") => meta_to_bool(ftc, convert::POINTER_DISCRIMINANT),
        ("meta.capy", "is_distinct") => meta_to_bool(ftc, convert::DISTINCT_DISCRIMINANT),
        ("meta.capy", "is_meta_type") => meta_to_bool(ftc, convert::META_TYPE_DISCRIMINANT),
        ("meta.capy", "is_any") => meta_to_bool(ftc, convert::ANY_DISCRIMINANT),
        ("meta.capy", "is_file") => meta_to_bool(ftc, convert::FILE_DISCRIMINANT),
        ("meta.capy", "is_function") => meta_to_bool(ftc, convert::FUNCTION_DISCRIMINANT),
        ("meta.capy", "is_struct") => meta_to_bool(ftc, convert::STRUCT_DISCRIMINANT),
        ("meta.capy", "is_void") => meta_to_bool(ftc, convert::VOID_DISCRIMINANT),
        ("meta.capy", "get_int_info") => meta_to_info(ftc, convert::INT_DISCRIMINANT),
        ("meta.capy", "get_float_info") => meta_to_info(ftc, convert::FLOAT_DISCRIMINANT),
        ("meta.capy", "get_array_info") => meta_to_info(ftc, convert::ARRAY_DISCRIMINANT),
        ("meta.capy", "get_pointer_info") => meta_to_info(ftc, convert::POINTER_DISCRIMINANT),
        ("meta.capy", "get_distinct_info") => meta_to_info(ftc, convert::DISTINCT_DISCRIMINANT),
        _ => return None,
    })
}

fn ptr_to_usize(ftc: &FunctionToCompile) -> BuiltinFunction {
    let mut params = ftc.param_tys.iter();

    let first = params.next().unwrap();
    debug_assert!(first
        .as_pointer()
        .map(|(mutable, sub_ty)| !mutable && *sub_ty == hir_ty::Ty::Any)
        .unwrap_or(false));
    debug_assert!(params.next().is_none());

    debug_assert_eq!(*ftc.return_ty, Ty::UInt(u32::MAX));

    BuiltinFunction::PtrBitcast
}

fn usize_to_ptr(ftc: &FunctionToCompile, mutable: bool) -> BuiltinFunction {
    let mut params = ftc.param_tys.iter();

    let first = params.next().unwrap();
    debug_assert_eq!(**first, Ty::UInt(u32::MAX));
    debug_assert!(params.next().is_none());

    debug_assert!(ftc
        .return_ty
        .as_pointer()
        .map(|(ptr_mut, sub_ty)| ptr_mut == mutable && *sub_ty == hir_ty::Ty::Any)
        .unwrap_or(false));

    BuiltinFunction::PtrBitcast
}

/// size = false, will output a CompilerDefinedFunction::AlignOf
fn meta_to_uint(ftc: &FunctionToCompile, size: bool) -> BuiltinFunction {
    let mut params = ftc.param_tys.iter();

    let first = params.next().unwrap();
    debug_assert_eq!(**first, Ty::Type);
    debug_assert!(params.next().is_none());

    debug_assert_eq!(*ftc.return_ty, Ty::UInt(u32::MAX));

    if size {
        BuiltinFunction::SizeOf
    } else {
        BuiltinFunction::AlignOf
    }
}

fn meta_to_bool(ftc: &FunctionToCompile, discriminant: u32) -> BuiltinFunction {
    let mut params = ftc.param_tys.iter();

    let first = params.next().unwrap();
    debug_assert_eq!(**first, Ty::Type);
    debug_assert!(params.next().is_none());

    debug_assert_eq!(*ftc.return_ty, Ty::Bool);

    BuiltinFunction::IsMetaOfType(discriminant)
}

fn meta_to_info(ftc: &FunctionToCompile, discriminant: u32) -> BuiltinFunction {
    let mut params = ftc.param_tys.iter();

    let first = params.next().unwrap();
    debug_assert_eq!(**first, Ty::Type);
    debug_assert!(params.next().is_none());

    debug_assert!(ftc.return_ty.is_struct());

    BuiltinFunction::GetMetaInfo(discriminant)
}

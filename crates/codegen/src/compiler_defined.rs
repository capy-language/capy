use std::path::Path;

use cranelift::prelude::{types, AbiParam};
use cranelift_module::{FuncId, Linkage, Module};
use hir_ty::Ty;
use interner::Interner;

use crate::{compiler::FunctionToCompile, mangle::Mangle, CraneliftSignature};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum CompilerDefinedFunction {
    PtrBitcast,
    SizeOf,
    AlignOf,
}

impl CompilerDefinedFunction {
    pub(crate) fn to_sig_and_func_id(
        self,
        module: &mut dyn Module,
        pointer_ty: types::Type,
        mod_dir: &std::path::Path,
        interner: &Interner,
    ) -> (String, CraneliftSignature, FuncId) {
        let ftc = match self {
            CompilerDefinedFunction::PtrBitcast => CraneliftSignature {
                params: vec![AbiParam::new(pointer_ty)],
                returns: vec![AbiParam::new(pointer_ty)],
                call_conv: module.target_config().default_call_conv,
            },
            CompilerDefinedFunction::SizeOf | CompilerDefinedFunction::AlignOf => {
                CraneliftSignature {
                    params: vec![AbiParam::new(types::I32)],
                    returns: vec![AbiParam::new(pointer_ty)],
                    call_conv: module.target_config().default_call_conv,
                }
            }
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
) -> Option<CompilerDefinedFunction> {
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

    match (file_name.as_ref(), function_name) {
        ("ptr.capy", "to_raw") => as_ptr_to_usize(ftc),
        ("ptr.capy", "const_from_raw") => as_usize_to_ptr(ftc, false),
        ("ptr.capy", "mut_from_raw") => as_usize_to_ptr(ftc, true),
        ("meta.capy", "size_of") => as_meta_to_uint(ftc, true),
        ("meta.capy", "align_of") => as_meta_to_uint(ftc, false),
        _ => None,
    }
}

fn as_ptr_to_usize(ftc: &FunctionToCompile) -> Option<CompilerDefinedFunction> {
    let mut params = ftc.param_tys.iter();

    let first = params.next()?;
    if !first
        .as_pointer()
        .map(|(mutable, sub_ty)| !mutable && *sub_ty == hir_ty::Ty::Any)
        .unwrap_or(false)
    {
        return None;
    }

    if params.next().is_some() {
        return None;
    }

    if *ftc.return_ty != Ty::UInt(u32::MAX) {
        return None;
    }

    Some(CompilerDefinedFunction::PtrBitcast)
}

fn as_usize_to_ptr(ftc: &FunctionToCompile, mutable: bool) -> Option<CompilerDefinedFunction> {
    let mut params = ftc.param_tys.iter();

    let first = params.next()?;
    if **first != Ty::UInt(u32::MAX) {
        return None;
    }

    if params.next().is_some() {
        return None;
    }

    if !ftc
        .return_ty
        .as_pointer()
        .map(|(ptr_mut, sub_ty)| ptr_mut == mutable && *sub_ty == hir_ty::Ty::Any)
        .unwrap_or(false)
    {
        return None;
    }

    Some(CompilerDefinedFunction::PtrBitcast)
}

/// size = false, will output a CompilerDefinedFunction::AlignOf
fn as_meta_to_uint(ftc: &FunctionToCompile, size: bool) -> Option<CompilerDefinedFunction> {
    let mut params = ftc.param_tys.iter();

    let first = params.next()?;
    if **first != Ty::Type {
        return None;
    }

    if params.next().is_some() {
        return None;
    }

    if *ftc.return_ty != Ty::UInt(u32::MAX) {
        return None;
    }

    if size {
        Some(CompilerDefinedFunction::SizeOf)
    } else {
        Some(CompilerDefinedFunction::AlignOf)
    }
}

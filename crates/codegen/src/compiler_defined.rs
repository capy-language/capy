use cranelift::prelude::{types, AbiParam};
use cranelift_module::{FuncId, Linkage, Module};
use interner::Interner;

use crate::{mangle::Mangle, CapyFnSignature, CraneliftSignature};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum CompilerDefinedFunction {
    PtrOffset,
}

impl CompilerDefinedFunction {
    pub(crate) fn to_sig_and_func_id(
        self,
        module: &mut dyn Module,
        pointer_ty: types::Type,
        project_root: &std::path::Path,
        interner: &Interner,
    ) -> (String, CraneliftSignature, FuncId) {
        match self {
            CompilerDefinedFunction::PtrOffset => {
                let sig = CraneliftSignature {
                    params: vec![AbiParam::new(pointer_ty), AbiParam::new(pointer_ty)],
                    returns: vec![AbiParam::new(pointer_ty)],
                    call_conv: module.target_config().default_call_conv,
                };
                let mangled = self.to_mangled_name(project_root, interner);
                let func_id = module
                    .declare_function(&mangled, Linkage::Export, &sig)
                    .unwrap();

                (mangled, sig, func_id)
            }
        }
    }
}

pub(crate) fn as_compiler_defined(
    sig: &CapyFnSignature,
    fqn: hir::Fqn,
    interner: &Interner,
) -> Option<CompilerDefinedFunction> {
    if !sig.is_extern {
        return None;
    }

    let module = interner.lookup(fqn.module.0);
    let module = std::path::Path::new(module);

    let is_std = module
        .parent()
        .and_then(|p| p.file_name())
        .map(|n| n == "std")
        .unwrap_or(false);
    if !is_std {
        return None;
    }

    let filename = module.file_name().unwrap_or_default().to_string_lossy();

    let function_name = interner.lookup(fqn.name.0);

    match filename.as_ref() {
        "ptr.capy" => match function_name {
            "ptr_offset" | "mut_ptr_offset" => as_ptr_offset(sig),
            _ => None,
        },
        _ => None,
    }
}

fn as_ptr_offset(sig: &CapyFnSignature) -> Option<CompilerDefinedFunction> {
    let mut params = sig.param_tys.iter();

    let first = params.next()?;
    if !first
        .as_pointer()
        .map(|(_, sub_ty)| *sub_ty == hir_ty::ResolvedTy::Any)
        .unwrap_or(false)
    {
        return None;
    }

    let second = params.next()?;
    if **second != hir_ty::ResolvedTy::UInt(u32::MAX) {
        return None;
    }

    if params.next().is_some() {
        return None;
    }

    if !sig
        .return_ty
        .as_pointer()
        .map(|(_, sub_ty)| *sub_ty == hir_ty::ResolvedTy::Any)
        .unwrap_or(false)
    {
        return None;
    }

    Some(CompilerDefinedFunction::PtrOffset)
}

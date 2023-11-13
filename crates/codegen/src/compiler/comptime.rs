//! This module is for JIT'ing all the code needed to calculate the value of comptime blocks
use cranelift::prelude::{settings, types, Configurable, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, Module};
use interner::Interner;
use la_arena::Idx;
use num_traits::ToBytes;
use rustc_hash::FxHashMap;
use std::{alloc::Layout, collections::VecDeque, mem};
use uid_gen::UIDGenerator;

use crate::{
    compiler::MetaTyData,
    convert::{FinalTy, GetFinalTy},
    layout::GetLayoutInfo,
    mangle::Mangle,
    Verbosity,
};

use super::Compiler;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct ComptimeToCompile {
    pub file_name: hir::FileName,
    pub comptime: Idx<hir::Comptime>,
}

#[derive(Debug, Clone)]
pub enum ComptimeResult {
    Integer { num: u64, bytes: Box<[u8]> },
    Float { num: f64, bytes: Box<[u8]> },
    Data(Box<[u8]>),
    Void,
}

impl ComptimeResult {
    pub(crate) fn into_bytes(self) -> Option<Box<[u8]>> {
        match self {
            ComptimeResult::Integer { bytes, .. } => Some(bytes),
            ComptimeResult::Float { bytes, .. } => Some(bytes),
            ComptimeResult::Data(bytes) => Some(bytes),
            ComptimeResult::Void => None,
        }
    }
}

pub fn eval_comptime_blocks<'a>(
    verbosity: Verbosity,
    mut comptime_blocks: Vec<ComptimeToCompile>,
    mod_dir: &'a std::path::Path,
    interner: &'a Interner,
    bodies_map: &'a FxHashMap<hir::FileName, hir::Bodies>,
    tys: &'a hir_ty::InferenceResult,
    target_pointer_bit_width: u8,
) -> FxHashMap<ComptimeToCompile, ComptimeResult> {
    if comptime_blocks.is_empty() {
        return FxHashMap::default();
    }

    let mut flag_builder = settings::builder();
    flag_builder.set("use_colocated_libcalls", "false").unwrap();
    flag_builder.set("is_pic", "false").unwrap();
    let isa_builder = cranelift_native::builder().unwrap_or_else(|msg| {
        panic!("host machine is not supported: {}", msg);
    });
    let isa = isa_builder
        .finish(settings::Flags::new(flag_builder))
        .unwrap();
    let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());

    let mut module = JITModule::new(builder);

    let mut compiler = Compiler {
        verbosity,
        mod_dir,
        interner,
        bodies_map,
        tys,
        builder_context: FunctionBuilderContext::new(),
        ctx: module.make_context(),
        data_description: DataDescription::new(),
        module: &mut module,
        functions_to_compile: VecDeque::new(),
        meta_tys: MetaTyData::default(),
        functions: FxHashMap::default(),
        compiler_defined_functions: FxHashMap::default(),
        data: FxHashMap::default(),
        str_id_gen: UIDGenerator::default(),
        comptime_results: &FxHashMap::default(),
        pointer_ty: match target_pointer_bit_width {
            8 => types::I8,
            16 => types::I16,
            32 => types::I32,
            64 => types::I64,
            _ => unreachable!(),
        },
    };

    compiler.finalize_tys();

    let mut comptime_funcs = Vec::new();

    while let Some(ctc) = comptime_blocks.pop() {
        let hir::Comptime { body } = compiler.bodies_map[&ctc.file_name][ctc.comptime];
        let return_ty = tys[ctc.file_name][body];

        let func_id = compiler.compile_real_function(
            &format!(
                "{}.comptime#{}",
                ctc.file_name.to_string(compiler.mod_dir, compiler.interner),
                ctc.comptime.into_raw()
            ),
            &ctc.to_mangled_name(compiler.mod_dir, compiler.interner),
            ctc.file_name,
            body,
            vec![],
            return_ty,
        );

        comptime_funcs.push((ctc, func_id, return_ty.get_final_ty(), return_ty.size()));
    }

    compiler.compile_queued();

    // Finalize the functions which were defined, which resolves any
    // outstanding relocations (patching in addresses, now that they're
    // available).
    // This also prepares the code for JIT execution
    module.finalize_definitions().unwrap();

    fn run_comptime_float<T: ToBytes + Into<f64> + Copy>(code_ptr: *const u8) -> ComptimeResult {
        let comptime = unsafe { mem::transmute::<_, fn() -> T>(code_ptr) };
        let result = comptime();

        ComptimeResult::Float {
            num: result.into(),
            bytes: result.to_ne_bytes().as_ref().to_vec().into_boxed_slice(),
        }
    }

    fn run_comptime_int<T: ToBytes + Into<u64> + Copy>(code_ptr: *const u8) -> ComptimeResult {
        let comptime = unsafe { mem::transmute::<_, fn() -> T>(code_ptr) };
        let result = comptime();

        ComptimeResult::Integer {
            num: result.into(),
            bytes: result.to_ne_bytes().as_ref().to_vec().into_boxed_slice(),
        }
    }

    let mut results = FxHashMap::default();

    while let Some((ctc, func_id, return_ty, size)) = comptime_funcs.pop() {
        let code_ptr = module.get_finalized_function(func_id);

        match return_ty {
            FinalTy::Number(number_ty) => {
                let result = match number_ty.ty {
                    types::F32 => run_comptime_float::<f32>(code_ptr),
                    types::F64 => run_comptime_float::<f64>(code_ptr),
                    types::I8 => run_comptime_int::<u8>(code_ptr),
                    types::I16 => run_comptime_int::<u16>(code_ptr),
                    types::I32 => run_comptime_int::<u32>(code_ptr),
                    types::I64 => run_comptime_int::<u64>(code_ptr),
                    types::I128 => {
                        let comptime = unsafe { mem::transmute::<_, fn() -> u128>(code_ptr) };
                        let result = comptime();

                        ComptimeResult::Data(result.to_ne_bytes().to_vec().into_boxed_slice())
                    }
                    _ => unreachable!(),
                };

                results.insert(ctc, result);
            }
            FinalTy::Pointer(_) => {
                let layout = Layout::from_size_align(size as usize, std::mem::align_of::<u8>())
                    .expect("Invalid layout");
                let raw = unsafe { std::alloc::alloc(layout) };

                let comptime = unsafe { mem::transmute::<_, fn(*const u8) -> *const u8>(code_ptr) };

                comptime(raw);

                let bytes = unsafe {
                    let slice = std::ptr::slice_from_raw_parts(raw, size as usize) as *mut [u8];

                    Box::from_raw(slice)
                };

                results.insert(ctc, ComptimeResult::Data(bytes));
            }
            FinalTy::Void => {
                let comptime = unsafe { mem::transmute::<_, fn()>(code_ptr) };
                comptime();
                results.insert(ctc, ComptimeResult::Void);
            }
        }
    }

    results.shrink_to_fit();

    results
}

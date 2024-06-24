//! This module is for JIT'ing all the code needed to calculate the value of comptime blocks
use cranelift::{
    codegen::ir::Endianness,
    prelude::{settings, types, Configurable, FunctionBuilderContext},
};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, Module};
use hir::FQComptime;
use hir_ty::ComptimeResult;
use interner::Interner;
use num_traits::ToBytes;
use rustc_hash::{FxHashMap, FxHashSet};
use std::{
    alloc::Layout,
    collections::VecDeque,
    mem::{self, size_of},
};
use uid_gen::UIDGenerator;

use crate::{
    compiler::{MetaTyData, MetaTyInfoArrays},
    convert::{FinalTy, GetFinalTy, ToTyId},
    layout::GetLayoutInfo,
    mangle::Mangle,
    Verbosity,
};

use super::Compiler;

pub(crate) trait ComptimeBytes {
    fn into_bytes(
        self,
        meta_tys: &mut MetaTyData,
        endianness: Endianness,
        ptr_ty: types::Type,
    ) -> Option<Box<[u8]>>;
}

impl ComptimeBytes for ComptimeResult {
    fn into_bytes(
        self,
        meta_tys: &mut MetaTyData,
        endianness: Endianness,
        ptr_ty: types::Type,
    ) -> Option<Box<[u8]>> {
        match self {
            ComptimeResult::Type(ty) => {
                Some(Box::new(ty.to_type_id(meta_tys, ptr_ty).to_ne_bytes()))
            }
            ComptimeResult::Integer { num, bit_width } => {
                Some(num.into_bytes(endianness, bit_width).into_boxed_slice())
            }
            ComptimeResult::Float { num, bit_width } => {
                Some(num.into_bytes(endianness, bit_width).into_boxed_slice())
            }
            ComptimeResult::Data(bytes) => Some(bytes),
            ComptimeResult::Void => None,
        }
    }
}

pub(crate) trait IntBytes {
    fn into_bytes(self, endianness: Endianness, target_bitwidth: u8) -> Vec<u8>;
}

impl IntBytes for u64 {
    fn into_bytes(self, endianness: Endianness, target_bitwidth: u8) -> Vec<u8> {
        match endianness {
            Endianness::Big => match target_bitwidth {
                8 => (self as u8).to_be_bytes().into(),
                16 => (self as u16).to_be_bytes().into(),
                32 => (self as u32).to_be_bytes().into(),
                #[allow(clippy::unnecessary_cast)]
                64 => (self as u64).to_be_bytes().into(),
                128 => (self as u128).to_be_bytes().into(),
                _ => unreachable!(),
            },
            Endianness::Little => match target_bitwidth {
                8 => (self as u8).to_le_bytes().into(),
                16 => (self as u16).to_le_bytes().into(),
                32 => (self as u32).to_le_bytes().into(),
                #[allow(clippy::unnecessary_cast)]
                64 => (self as u64).to_le_bytes().into(),
                128 => (self as u128).to_le_bytes().into(),
                _ => unreachable!(),
            },
        }
    }
}

impl IntBytes for f64 {
    fn into_bytes(self, endianness: Endianness, target_bitwidth: u8) -> Vec<u8> {
        match endianness {
            Endianness::Big => match target_bitwidth {
                32 => (self as f32).to_be_bytes().into(),
                #[allow(clippy::unnecessary_cast)]
                64 => (self as f64).to_be_bytes().into(),
                _ => unreachable!(),
            },
            Endianness::Little => match target_bitwidth {
                32 => (self as f32).to_le_bytes().into(),
                #[allow(clippy::unnecessary_cast)]
                64 => (self as f64).to_le_bytes().into(),
                _ => unreachable!(),
            },
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub fn eval_comptime_blocks<'a>(
    verbosity: Verbosity,
    mut to_eval: Vec<FQComptime>,
    results: &'a mut FxHashMap<FQComptime, ComptimeResult>,
    mod_dir: &'a std::path::Path,
    interner: &'a Interner,
    world_bodies: &'a hir::WorldBodies,
    tys: &'a hir_ty::ProjectInference,
    target_pointer_bit_width: u8,
) {
    if to_eval.is_empty() {
        return;
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
        final_binary: false,
        verbosity,
        mod_dir,
        interner,
        world_bodies,
        tys,
        builder_context: FunctionBuilderContext::new(),
        ctx: module.make_context(),
        data_desc: DataDescription::new(),
        module: &mut module,
        functions_to_compile: VecDeque::new(),
        meta_tys: MetaTyData::default(),
        cmd_args_slice: None,
        functions: FxHashMap::default(),
        compiler_defined_functions: FxHashMap::default(),
        data: FxHashMap::default(),
        str_id_gen: UIDGenerator::default(),
        i128_id_gen: UIDGenerator::default(),
        comptime_results: results,
        comptime_data: FxHashMap::default(),
        ptr_ty: match target_pointer_bit_width {
            8 => types::I8,
            16 => types::I16,
            32 => types::I32,
            64 => types::I64,
            _ => unreachable!(),
        },
    };

    compiler.finalize_tys();

    let mut already_done: FxHashSet<_> = to_eval
        .iter()
        .cloned()
        .chain(results.keys().cloned())
        .collect();

    let mut comptime_funcs = Vec::new();

    while let Some(ctc) = to_eval.pop() {
        let hir::Comptime { body } = compiler.world_bodies[ctc.file][ctc.comptime];
        let return_ty = tys[ctc.file][body];

        let func_id = compiler.compile_real_function(
            &format!(
                "{}.comptime#{}",
                ctc.file.to_string(compiler.mod_dir, compiler.interner),
                ctc.comptime.into_raw()
            ),
            &ctc.to_mangled_name(compiler.mod_dir, compiler.interner),
            ctc.file,
            ctc.expr,
            vec![],
            return_ty,
        );

        let extra: Vec<_> = compiler
            .comptime_data
            .keys()
            .filter(|ctc| !already_done.contains(ctc))
            .copied()
            .collect();

        already_done.extend(extra.clone());
        to_eval.extend(extra);

        comptime_funcs.push((
            ctc,
            func_id,
            return_ty.get_final_ty(),
            return_ty.size(),
            *return_ty == hir_ty::Ty::Type,
        ));
    }

    // Initializing this will force the compiler to create type info data
    compiler.meta_tys.info_arrays = Some(MetaTyInfoArrays::new(compiler.module));

    compiler.compile_queued();
    compiler.compile_builtins();

    let meta_tys: FxHashMap<_, _> = compiler
        .meta_tys
        .tys_to_compile
        .iter()
        .map(|ty| {
            (
                ty.to_previous_type_id(&compiler.meta_tys, compiler.ptr_ty),
                ty,
            )
        })
        .collect();

    // Finalize the functions which were defined, which resolves any
    // outstanding relocations (patching in addresses, now that they're
    // available).
    // This also prepares the code for JIT execution
    module.finalize_definitions().unwrap();

    fn run_comptime_float<T: ToBytes + Into<f64> + Copy>(code_ptr: *const u8) -> ComptimeResult {
        let comptime = unsafe { mem::transmute::<*const u8, fn() -> T>(code_ptr) };
        let result = comptime();

        ComptimeResult::Float {
            num: result.into(),
            bit_width: (size_of::<T>() * 8) as u8,
        }
    }

    fn run_comptime_int<T: ToBytes + Into<u64> + Copy>(code_ptr: *const u8) -> ComptimeResult {
        let comptime = unsafe { mem::transmute::<*const u8, fn() -> T>(code_ptr) };
        let result = comptime();

        ComptimeResult::Integer {
            num: result.into(),
            bit_width: (size_of::<T>() * 8) as u8,
        }
    }

    while let Some((ctc, func_id, return_ty, size, is_type)) = comptime_funcs.pop() {
        let code_ptr = module.get_finalized_function(func_id);

        if is_type {
            let comptime = unsafe { mem::transmute::<*const u8, fn() -> u32>(code_ptr) };
            let ty = comptime();

            let ty = meta_tys.get(&ty).unwrap();

            results.insert(ctc, ComptimeResult::Type(**ty));
            continue;
        }

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
                        let comptime =
                            unsafe { mem::transmute::<*const u8, fn() -> u128>(code_ptr) };
                        let result = comptime();

                        ComptimeResult::Data(Box::new(result.to_ne_bytes()))
                    }
                    _ => unreachable!(),
                };

                results.insert(ctc, result);
            }
            FinalTy::Pointer(_) => {
                let layout = Layout::from_size_align(size as usize, std::mem::align_of::<u8>())
                    .expect("Invalid layout");
                let raw = unsafe { std::alloc::alloc(layout) };

                let comptime =
                    unsafe { mem::transmute::<*const u8, fn(*const u8) -> *const u8>(code_ptr) };

                comptime(raw);

                let bytes = unsafe {
                    let slice = std::ptr::slice_from_raw_parts(raw, size as usize) as *mut [u8];

                    Box::from_raw(slice)
                };

                results.insert(ctc, ComptimeResult::Data(bytes));
            }
            FinalTy::Void => {
                let comptime = unsafe { mem::transmute::<*const u8, fn()>(code_ptr) };
                comptime();
                results.insert(ctc, ComptimeResult::Void);
            }
        }
    }

    // todo: don't do this, and instead reuse previously compiled function pointers and data
    unsafe { module.free_memory() };
}

//! This module is for building the final executable of a capy program

use cranelift::{
    codegen::ir::MemFlags,
    prelude::{AbiParam, FunctionBuilder, FunctionBuilderContext, InstBuilder, Signature},
};
use cranelift_module::{DataDescription, FuncId, Linkage, Module};
use hir::FQComptime;
use hir_ty::ComptimeResult;
use interner::Interner;
use rustc_hash::FxHashMap;
use std::collections::VecDeque;
use uid_gen::UIDGenerator;

use crate::Verbosity;

use super::{ cast_ty_to_cranelift, Compiler, FunctionToCompile, MetaTyData};

#[allow(clippy::too_many_arguments)]
pub(crate) fn compile_program<'a>(
    verbosity: Verbosity,
    entry_point: hir::Fqn,
    mod_dir: &'a std::path::Path,
    interner: &'a Interner,
    world_bodies: &'a hir::WorldBodies,
    tys: &'a hir_ty::ProjectInference,
    module: &'a mut dyn Module,
    comptime_results: &'a FxHashMap<FQComptime, ComptimeResult>,
) -> FuncId {
    let entry_point_ftc = {
        let (param_tys, return_ty) = tys[entry_point]
            .0
            .as_function()
            .expect("tried to compile non-function as entry point");

        let global_body = world_bodies.body(entry_point);

        let lambda = match world_bodies[entry_point.file][global_body] {
            hir::Expr::Lambda(lambda) => lambda,
            _ => todo!("entry point does not have a lambda as it's body"),
        };

        FunctionToCompile {
            file_name: entry_point.file,
            function_name: Some(entry_point.name),
            lambda,
            param_tys: param_tys.clone(),
            return_ty,
        }
    };

    let default_abi = module.target_config().into();

    let mut compiler = Compiler {
        final_binary: true,
        verbosity,
        mod_dir,
        interner,
        world_bodies,
        tys,
        builder_context: FunctionBuilderContext::new(),
        ctx: module.make_context(),
        ptr_ty: module.target_config().pointer_type(),
        module,
        data_desc: DataDescription::new(),
        functions_to_compile: VecDeque::from([entry_point_ftc]),
        meta_tys: MetaTyData::default(),
        cmd_args_slice: None,
        functions: FxHashMap::default(),
        compiler_defined_functions: FxHashMap::default(),
        data: FxHashMap::default(),
        str_id_gen: UIDGenerator::default(),
        i128_id_gen: UIDGenerator::default(),
        comptime_results,
        comptime_data: FxHashMap::default(),
        default_abi,
    };

    compiler.finalize_tys();
    compiler.compile_queued();
    compiler.compile_builtins();

    generate_main_function(compiler, entry_point)
}

fn generate_main_function(mut compiler: Compiler, entry_point: hir::Fqn) -> FuncId {
    let entry_point_func = compiler.get_func_id(entry_point);

    let cmain_sig = Signature {
        params: vec![
            AbiParam::new(compiler.ptr_ty),
            AbiParam::new(compiler.ptr_ty),
        ],
        returns: vec![AbiParam::new(compiler.ptr_ty /*isize*/)],
        call_conv: compiler.module.target_config().default_call_conv,
    };
    let cmain_id = compiler
        .module
        .declare_function("main", Linkage::Export, &cmain_sig)
        .unwrap();

    compiler.ctx.func.signature = cmain_sig;

    // Create the builder to build a function.
    let mut builder = FunctionBuilder::new(&mut compiler.ctx.func, &mut compiler.builder_context);

    // Create the entry block, to start emitting code in.
    let entry_block = builder.create_block();

    builder.switch_to_block(entry_block);
    // tell the builder that the block will have no further predecessors
    builder.seal_block(entry_block);

    let arg_argc = builder.append_block_param(entry_block, compiler.ptr_ty);
    let arg_argv = builder.append_block_param(entry_block, compiler.ptr_ty);

    if let Some(cmd_args_slice) = compiler.cmd_args_slice {
        let local_id = compiler
            .module
            .declare_data_in_func(cmd_args_slice, builder.func);

        let global_addr = builder.ins().symbol_value(compiler.ptr_ty, local_id);

        builder
            .ins()
            .store(MemFlags::trusted(), arg_argc, global_addr, 0);
        builder.ins().store(
            MemFlags::trusted(),
            arg_argv,
            global_addr,
            compiler.ptr_ty.bytes() as i32,
        );
    }

    let local_entry_point = compiler
        .module
        .declare_func_in_func(entry_point_func, builder.func);

    let call = builder.ins().call(local_entry_point, &[]);

    let (_, entry_return_ty) = compiler.tys[entry_point].0.as_function().unwrap();

    let exit_code = if entry_return_ty.is_void() {
        builder.ins().iconst(compiler.ptr_ty, 0)
    } else {
        let exit_code = builder.inst_results(call)[0];

        // cast the exit code from the entry point into a usize
        cast_ty_to_cranelift(&mut builder, exit_code, entry_return_ty, compiler.ptr_ty)
    };

    builder.ins().return_(&[exit_code]);

    builder.seal_all_blocks();
    builder.finalize();

    if compiler.verbosity == Verbosity::AllFunctions {
        println!("main \x1B[90mmain\x1B[0m:\n{}", compiler.ctx.func);
    }

    compiler
        .module
        .define_function(cmain_id, &mut compiler.ctx)
        .expect("error defining function");

    compiler.module.clear_context(&mut compiler.ctx);

    cmain_id
}

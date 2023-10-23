//! This module is for building the final executable of a capy program

use cranelift::prelude::{
    AbiParam, EntityRef, FunctionBuilder, FunctionBuilderContext, InstBuilder, Signature, Variable,
};
use cranelift_module::{DataDescription, FuncId, Linkage, Module};
use interner::Interner;
use rustc_hash::FxHashMap;
use std::collections::VecDeque;
use uid_gen::UIDGenerator;

use crate::{convert::*, ComptimeToCompile};

use super::{cast, comptime::ComptimeResult, Compiler, FunctionToCompile, MetaTyData};

#[allow(clippy::too_many_arguments)]
pub(crate) fn compile_program<'a>(
    verbose: bool,
    entry_point: hir::Fqn,
    mod_dir: &'a std::path::Path,
    interner: &'a Interner,
    bodies_map: &'a FxHashMap<hir::FileName, hir::Bodies>,
    tys: &'a hir_ty::InferenceResult,
    module: &'a mut dyn Module,
    comptime_results: &'a FxHashMap<ComptimeToCompile, ComptimeResult>,
) -> FuncId {
    let entry_point_ftc = {
        let (param_tys, return_ty) = tys[entry_point]
            .0
            .as_function()
            .expect("tried to compile non-function as entry point");

        let global_body = bodies_map[&entry_point.file].global_body(entry_point.name);

        let lambda = match bodies_map[&entry_point.file][global_body] {
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

    let mut compiler = Compiler {
        verbose,
        mod_dir,
        interner,
        bodies_map,
        tys,
        builder_context: FunctionBuilderContext::new(),
        ctx: module.make_context(),
        pointer_ty: module.target_config().pointer_type(),
        module,
        data_description: DataDescription::new(),
        functions_to_compile: VecDeque::from([entry_point_ftc]),
        meta_tys: MetaTyData::default(),
        functions: FxHashMap::default(),
        compiler_defined_functions: FxHashMap::default(),
        data: FxHashMap::default(),
        str_id_gen: UIDGenerator::default(),
        comptime_results,
    };

    compiler.compile_queued();

    generate_main_function(compiler, entry_point)
}

fn generate_main_function(mut compiler: Compiler, entry_point: hir::Fqn) -> FuncId {
    let entry_point_func = compiler.get_func_id(entry_point);

    let cmain_sig = Signature {
        params: vec![
            AbiParam::new(compiler.pointer_ty),
            AbiParam::new(compiler.pointer_ty),
        ],
        returns: vec![AbiParam::new(compiler.pointer_ty /*isize*/)],
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

    let arg_argc = builder.append_block_param(entry_block, compiler.pointer_ty);
    let arg_argv = builder.append_block_param(entry_block, compiler.pointer_ty);

    let var_argc = Variable::new(0);
    builder.declare_var(var_argc, compiler.pointer_ty);
    builder.def_var(var_argc, arg_argc);

    let var_argv = Variable::new(1);
    builder.declare_var(var_argv, compiler.pointer_ty);
    builder.def_var(var_argv, arg_argv);

    let local_entry_point = compiler
        .module
        .declare_func_in_func(entry_point_func, builder.func);

    let call = builder.ins().call(local_entry_point, &[]);

    let (_, entry_return_ty) = compiler.tys[entry_point].0.as_function().unwrap();

    let exit_code = match entry_return_ty
        .to_comp_type(compiler.pointer_ty)
        .into_number_type()
    {
        Some(found_return_ty) => {
            let exit_code = builder.inst_results(call)[0];

            // cast the exit code from the entry point into a usize
            cast(
                &mut builder,
                exit_code,
                found_return_ty,
                NumberType {
                    ty: compiler.pointer_ty,
                    float: false,
                    signed: false,
                },
            )
        }
        _ => builder.ins().iconst(compiler.pointer_ty, 0),
    };

    builder.ins().return_(&[exit_code]);

    builder.seal_all_blocks();
    builder.finalize();

    if compiler.verbose {
        println!("main \x1B[90mmain\x1B[0m:\n{}", compiler.ctx.func);
    }

    compiler
        .module
        .define_function(cmain_id, &mut compiler.ctx)
        .expect("error defining function");

    compiler.module.clear_context(&mut compiler.ctx);

    cmain_id
}

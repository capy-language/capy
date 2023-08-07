mod gen;
mod mangle;
mod ty;

use hir_ty::ResolvedTy;
use inkwell::context::Context;
use inkwell::OptimizationLevel;

use gen::CodeGen;
use inkwell::targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetMachine};
use interner::Interner;
use la_arena::Arena;
use rustc_hash::FxHashMap;
use std::path::PathBuf;
use std::process::Command;

#[allow(clippy::too_many_arguments)]
pub fn compile(
    source_file_name: &str,
    verbose: bool,
    entry_point: hir::Fqn,
    resolved_arena: &Arena<ResolvedTy>,
    interner: &Interner,
    bodies_map: &FxHashMap<hir::Name, hir::Bodies>,
    types_map: &FxHashMap<hir::Name, hir_ty::InferenceResult>,
    world_index: &hir::WorldIndex,
) -> Result<Vec<u8>, String> {
    let context = Context::create();

    let module = context.create_module(interner.lookup(entry_point.module.0));

    Target::initialize_native(&InitializationConfig::default())
        .expect("Failed to initialize native target");

    module.set_source_file_name(source_file_name);

    let triple = TargetMachine::get_default_triple();
    module.set_triple(&triple);
    let cpu = TargetMachine::get_host_cpu_name().to_string();
    let cpu_features = TargetMachine::get_host_cpu_features().to_string();
    let target = Target::from_triple(&triple).unwrap();
    let target_machine = target
        .create_target_machine(
            &triple,
            &cpu,
            &cpu_features,
            OptimizationLevel::Aggressive,
            RelocMode::PIC,
            CodeModel::Default,
        )
        .unwrap();
    module.set_data_layout(&target_machine.get_target_data().get_data_layout());

    let code_gen = CodeGen {
        resolved_arena,
        interner,
        bodies_map,
        types_map,
        world_index,
        context: &context,
        module: &module,
        builder_stack: Vec::new(),
        entry_point,
        functions_to_compile: vec![entry_point],
        functions: FxHashMap::default(),
        globals: FxHashMap::default(),
        locals: FxHashMap::default(),
        function_stack: Vec::new(),
        param_stack_map: Vec::new(),
        target_machine: &target_machine,
    };
    code_gen.finish(source_file_name, verbose)
}

pub fn link_to_exec(path: &PathBuf) -> PathBuf {
    let exe_path = path.parent().unwrap().join(path.file_stem().unwrap());
    let success = Command::new("gcc")
        .arg(path)
        .arg("-o")
        .arg(&exe_path)
        .status()
        .unwrap()
        .success();
    assert!(success);
    exe_path
}

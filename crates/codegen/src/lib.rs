mod codegen;

use inkwell::context::Context;

use codegen::CodeGen;
use interner::Interner;
use rustc_hash::FxHashMap;
use std::path::PathBuf;
use std::process::Command;

pub fn compile(
    entry_point: hir::Fqn,
    interner: &Interner,
    bodies_map: FxHashMap<hir::Name, hir::Bodies>,
    types_map: FxHashMap<hir::Name, hir_types::InferenceResult>,
    world_index: &hir::WorldIndex,
) -> Result<Vec<u8>, String> {
    let context = Context::create();
    let context_b = &context;
    let x = CodeGen {
        context: context_b,
        module: &context.create_module(interner.lookup(entry_point.module.0)),
        current_builders: Vec::new(),
        functions_to_compile: vec![entry_point],
        interner,
        bodies_map,
        types_map,
        world_index,
        functions: FxHashMap::default(),
        variables: FxHashMap::default(),
        current_functions: Vec::new(),
    }.finish(); x
}

pub fn link_and_exec(path: &PathBuf) -> i32 {
    let exe_path = path.parent().unwrap().join(path.file_stem().unwrap());
    let success = Command::new("gcc")
        .arg(&path)
        .arg("-o")
        .arg(&exe_path)
        .status()
        .unwrap()
        .success();
    assert!(success);

    Command::new(exe_path).status().unwrap().code().unwrap_or_else(|| {
        println!("\nEarly exit");
        1
    })
}
mod codegen;

use inkwell::context::Context;

use codegen::CodeGen;
use interner::Interner;
use rustc_hash::FxHashMap;

pub fn compile(
    entry_point: hir::Fqn,
    interner: &Interner,
    bodies_map: FxHashMap<hir::Name, hir::Bodies>,
    types_map: FxHashMap<hir::Name, hir_types::InferenceResult>,
    world_index: &hir::WorldIndex,
) -> Vec<u8> {
    let context = Context::create();
    let context_b = &context;
    let x = CodeGen {
        context: context_b,
        module: &context.create_module(interner.lookup(entry_point.module.0)),
        builders: Vec::new(),
        functions_to_compile: vec![entry_point],
        interner,
        bodies_map,
        types_map,
        world_index,
        functions: FxHashMap::default(),
        variables: FxHashMap::default(),
        current_function: Vec::new(),
    }.finish(); x
}
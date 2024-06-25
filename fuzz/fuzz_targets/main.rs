#![no_main]

extern crate ast;
extern crate codegen;
extern crate hir_ty;
extern crate libfuzzer_sys;
extern crate rustc_hash;
extern crate target_lexicon;

use std::path::Path;

use ast::AstNode;
use codegen::Verbosity;
use hir_ty::{InferenceCtx, InferenceResult};
use libfuzzer_sys::fuzz_target;
use rustc_hash::FxHashMap;
use target_lexicon::Triple;

fuzz_target!(|s: &str| {
    let mut interner = interner::Interner::default();
    let mut world_index = hir::WorldIndex::default();

    let mut uid_gen = uid_gen::UIDGenerator::default();
    let mut world_bodies = hir::WorldBodies::default();

    // `s` is the source code being tested
    let tokens = &lexer::lex(s);
    let parse = parser::parse_source_file(tokens, s);

    let tree = parse.syntax_tree();
    let root = ast::Root::cast(tree.root(), tree).unwrap();
    let _diagnostics = ast::validation::validate(root, tree);

    let (index, _indexing_diagnostics) = hir::index(root, tree, &mut interner);

    let (bodies, _lowering_diagnostics) = hir::lower(
        root,
        tree,
        Path::new("main.capy"),
        &index,
        &mut uid_gen,
        &mut interner,
        Path::new(""),
        true,
    );

    let file = hir::FileName(interner.intern("main.capy"));

    world_index.add_file(file, index);
    world_bodies.add_file(file, bodies);

    let mut comptime_results = FxHashMap::default();

    let InferenceResult {
        tys: _tys,
        diagnostics: _type_diagnostics,
        any_were_unsafe_to_compile: _any_unsafe,
    } = InferenceCtx::new(&world_index, &world_bodies, &interner, |comptime, tys| {
        // todo: this might make the fuzzer a lot slower, would it be beneficial to make a separate
        // fuzzer for codegen stuff?
        codegen::eval_comptime_blocks(
            Verbosity::LocalFunctions,
            vec![comptime],
            &mut comptime_results,
            Path::new(""),
            &interner,
            &world_bodies,
            tys,
            Triple::host().pointer_width().unwrap().bits(),
        );

        comptime_results[&comptime].clone()
    })
    .finish(None, true);

    // frontend finally finished!
    // presumably you would use `codegen::compile_obj` now
});

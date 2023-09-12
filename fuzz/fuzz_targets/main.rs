#![no_main]

extern crate ast;
extern crate libfuzzer_sys;

use ast::AstNode;
use libfuzzer_sys::fuzz_target;
use std::cell::RefCell;
use std::rc::Rc;

fuzz_target!(|s: &str| {
    let mut interner = interner::Interner::default();
    let world_index = hir::WorldIndex::default();

    let mut interner = interner::Interner::default();
    let bodies_map = rustc_hash::FxHashMap::default();
    let uid_gen = uid_gen::UIDGenerator::default();
    let twr_arena = la_arena::Arena::new();

    let tokens = &lexer::lex(s);
    let parse = parser::parse_source_file(tokens, s);

    let tree = parse.syntax_tree();
    let root = ast::Root::cast(tree.root(), tree).unwrap();
    let _diagnostics = ast::validation::validate(root, tree);

    let module = hir::FileName(interner.intern(&"fuzz_file"));

    // let (index, _diagnostics) = hir::index(root, tree, &mut interner);
    // let (bodies, _diagnostics) = hir::lower(root, tree, &index, &world_index, &mut interner);
    // let (_inference, _diagnostics) = hir_ty::infer_all(&bodies, &index, &world_index);
    let (inference, ty_diagnostics) =
        hir_ty::InferenceCtx::new(&bodies_map, &world_index, &twr_arena).finish();
});

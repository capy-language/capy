#![no_main]

extern crate ast;
extern crate libfuzzer_sys;

use ast::AstNode;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|s: &str| {
    let mut interner = interner::Interner::default();
    let world_index = hir::WorldIndex::default();

    let bodies_map = rustc_hash::FxHashMap::default();
    let mut twr_arena = la_arena::Arena::new();
    let mut uid_gen = uid_gen::UIDGenerator::default();

    let tokens = &lexer::lex(s);
    let parse = parser::parse_source_file(tokens, s);

    let tree = parse.syntax_tree();
    let root = ast::Root::cast(tree.root(), tree).unwrap();
    let _diagnostics = ast::validation::validate(root, tree);

    let (index, _indexing_diagnostics) =
        hir::index(root, tree, &mut uid_gen, &mut twr_arena, &mut interner);

    let _hir = hir::lower(
        root,
        tree,
        &std::path::PathBuf::from("main.capy"),
        &index,
        &mut uid_gen,
        &mut twr_arena,
        &mut interner,
        true,
    ); // let (index, _diagnostics) = hir::index(root, tree, &mut interner);
       // let (bodies, _diagnostics) = hir::lower(root, tree, &index, &world_index, &mut interner);
       // let (_inference, _diagnostics) = hir_ty::infer_all(&bodies, &index, &world_index);
    let (_inference, _ty_diagnostics) =
        hir_ty::InferenceCtx::new(&bodies_map, &world_index, &twr_arena).finish();
});

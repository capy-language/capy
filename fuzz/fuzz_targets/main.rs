#![no_main]

extern crate ast;
extern crate libfuzzer_sys;

use ast::AstNode;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|s: &str| {
    let mut interner = interner::Interner::default();
    let mut world_index = hir::WorldIndex::default();

    let mut bodies_map = rustc_hash::FxHashMap::default();
    let mut twr_arena = la_arena::Arena::new();
    let mut uid_gen = uid_gen::UIDGenerator::default();

    let tokens = &lexer::lex(s);
    let parse = parser::parse_source_file(tokens, s);

    let tree = parse.syntax_tree();
    let root = ast::Root::cast(tree.root(), tree).unwrap();
    let _diagnostics = ast::validation::validate(root, tree);

    let (index, _indexing_diagnostics) =
        hir::index(root, tree, &mut uid_gen, &mut twr_arena, &mut interner);

    let (bodies, _lowering_diagnostics) = hir::lower(
        root,
        tree,
        &std::path::PathBuf::from("main.capy"),
        &index,
        &mut uid_gen,
        &mut twr_arena,
        &mut interner,
        true,
    );

    let module = hir::FileName(interner.intern("main.capy"));
    
    world_index.add_module(module, index);
    bodies_map.insert(module, bodies);

    let (_inference, _ty_diagnostics) =
        hir_ty::InferenceCtx::new(&bodies_map, &world_index, &twr_arena).finish();
});

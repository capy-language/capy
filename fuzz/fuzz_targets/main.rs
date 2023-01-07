#![no_main]

extern crate ast;
extern crate libfuzzer_sys;

use ast::AstNode;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|s: &str| {
    let mut interner = interner::Interner::default();
    let world_index = hir::WorldIndex::default();
    
    let tokens = &lexer::lex(s);
    let parse = parser::parse_repl_line(tokens, s);

    let tree = parse.syntax_tree();
    let root = ast::Root::cast(tree.root(), tree).unwrap();
    let _diagnostics = ast::validation::validate(root, tree);
    let (index, _diagnostics) = hir::index(root, tree, &mut interner);
    let (bodies, _diagnostics) = hir::lower(root, tree, &index, &world_index, &mut interner);
});

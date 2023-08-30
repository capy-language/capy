use std::{cell::RefCell, rc::Rc};

use ast::{AstNode, Root};
use diagnostics::{Diagnostic, Severity};
use hir::Name;
use interner::Interner;
use la_arena::Arena;
use line_index::LineIndex;
use parser::Parse;
use rustc_hash::FxHashMap;
use std::path::Path;

pub(crate) struct SourceFile {
    pub(crate) file_name: String,
    pub(crate) contents: String,
    pub(crate) module: Name,
    parse: Parse,
    root: Root,
    diagnostics: Vec<Diagnostic>,
    uid_gen: Rc<RefCell<hir::UIDGenerator>>,
    twr_arena: Rc<RefCell<Arena<hir::TyWithRange>>>,
    resolved_arena: Rc<RefCell<Arena<hir_ty::ResolvedTy>>>,
    interner: Rc<RefCell<Interner>>,
    bodies_map: Rc<RefCell<FxHashMap<hir::Name, hir::Bodies>>>,
    world_index: Rc<RefCell<hir::WorldIndex>>,
    verbose: u8,
}

impl SourceFile {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn parse(
        file_name: String,
        contents: String,
        uid_gen: Rc<RefCell<hir::UIDGenerator>>,
        twr_arena: Rc<RefCell<Arena<hir::TyWithRange>>>,
        resolved_arena: Rc<RefCell<Arena<hir_ty::ResolvedTy>>>,
        interner: Rc<RefCell<Interner>>,
        bodies_map: Rc<RefCell<FxHashMap<hir::Name, hir::Bodies>>>,
        world_index: Rc<RefCell<hir::WorldIndex>>,
        verbose: u8,
    ) -> SourceFile {
        let module_name = Path::new(&file_name).file_stem().unwrap().to_str().unwrap();
        if verbose >= 1 {
            println!("{} => {}", file_name, module_name);
        }

        let parse = parser::parse_source_file(&lexer::lex(&contents), &contents);
        if verbose >= 2 {
            println!("{:?}", parse);
        }

        let tree = parse.syntax_tree();
        let root = ast::Root::cast(tree.root(), tree).unwrap();

        let validation_diagnostics = ast::validation::validate(root, tree);

        let module = hir::Name(interner.borrow_mut().intern(module_name));
        let (index, indexing_diagnostics) = hir::index(
            root,
            tree,
            &mut uid_gen.borrow_mut(),
            &mut twr_arena.borrow_mut(),
            &mut interner.borrow_mut(),
        );
        world_index.borrow_mut().add_module(module, index);

        if verbose >= 3 {
            let world_index = world_index.borrow();
            let index = world_index.get_module(module).unwrap();

            for name in index.definition_names() {
                println!(
                    "{} = {:?}",
                    interner.borrow().lookup(name.0),
                    index.get_definition(name)
                );
            }
            if index.definition_names().next().is_some() {
                println!();
            }
        }

        let mut res = Self {
            file_name,
            contents,
            module,
            parse,
            root,
            diagnostics: Vec::new(),
            uid_gen,
            twr_arena,
            resolved_arena,
            interner,
            bodies_map,
            world_index,
            verbose,
        };

        res.diagnostics.extend(
            res.parse
                .errors()
                .iter()
                .cloned()
                .map(diagnostics::Diagnostic::from_syntax)
                .chain(
                    validation_diagnostics
                        .iter()
                        .cloned()
                        .map(diagnostics::Diagnostic::from_validation),
                )
                .chain(
                    indexing_diagnostics
                        .iter()
                        .cloned()
                        .map(diagnostics::Diagnostic::from_indexing),
                ),
        );

        res
    }

    pub(crate) fn build_bodies(&mut self) {
        let tree = self.parse.syntax_tree();

        let (bodies, lowering_diagnostics) = hir::lower(
            self.root,
            tree,
            self.module,
            &self.world_index.borrow(),
            &mut self.uid_gen.borrow_mut(),
            &mut self.twr_arena.borrow_mut(),
            &mut self.interner.borrow_mut(),
        );
        if self.verbose >= 1 {
            let interner = self.interner.borrow();
            let debug = bodies.debug(
                interner.lookup(self.module.0),
                &self.twr_arena.borrow(),
                &interner,
                self.verbose >= 2,
            );
            println!("{}", debug);
        }
        self.bodies_map.borrow_mut().insert(self.module, bodies);
        self.diagnostics.extend(
            lowering_diagnostics
                .iter()
                .cloned()
                .map(diagnostics::Diagnostic::from_lowering),
        );
    }

    pub(crate) fn has_fn_of_name(&self, name: Name) -> bool {
        self.world_index
            .borrow()
            .get_module(self.module)
            .unwrap()
            .function_names()
            .any(|fn_name| fn_name == name)
    }

    pub(crate) fn print_diagnostics(&self, with_color: bool) {
        let line_index = LineIndex::new(&self.contents);
        for diagnostic in &self.diagnostics {
            println!(
                "{}",
                diagnostic
                    .display(
                        &self.file_name,
                        &self.contents,
                        &self.resolved_arena.borrow(),
                        &self.interner.borrow(),
                        &line_index,
                        with_color
                    )
                    .join("\n")
            );
        }
    }

    pub(crate) fn has_errors(&self) -> bool {
        self.diagnostics
            .iter()
            .any(|diag| matches!(diag.severity(), Severity::Error))
    }
}

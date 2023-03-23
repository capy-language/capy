use std::{cell::RefCell, rc::Rc};

use ast::{AstNode, Root};
use diagnostics::{Diagnostic, Severity};
use hir::Name;
use interner::Interner;
use line_index::LineIndex;
use parser::Parse;
use rustc_hash::FxHashMap;
use std::path::Path;

pub(crate) struct SourceFile {
    pub(crate) file_name: String,
    contents: String,
    pub(crate) module: Name,
    parse: Parse,
    root: Root,
    diagnostics: Vec<Diagnostic>,
    interner: Rc<RefCell<Interner>>,
    bodies_map: Rc<RefCell<FxHashMap<hir::Name, hir::Bodies>>>,
    tys_map: Rc<RefCell<FxHashMap<hir::Name, hir_ty::InferenceResult>>>,
    world_index: Rc<RefCell<hir::WorldIndex>>,
    verbose: u8,
}

impl SourceFile {
    pub(crate) fn parse(
        file_name: String,
        contents: String,
        interner: Rc<RefCell<Interner>>,
        bodies_map: Rc<RefCell<FxHashMap<hir::Name, hir::Bodies>>>,
        tys_map: Rc<RefCell<FxHashMap<hir::Name, hir_ty::InferenceResult>>>,
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
        let (index, indexing_diagnostics) = hir::index(root, tree, &mut interner.borrow_mut());
        world_index.borrow_mut().add_module(module, index);

        if verbose >= 3 {
            let world_index = world_index.borrow_mut();
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
            interner,
            bodies_map,
            tys_map,
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
            &self.world_index.borrow_mut(),
            &mut self.interner.borrow_mut(),
        );
        if self.verbose >= 1 {
            let interner = self.interner.borrow_mut();
            let debug = bodies.debug(interner.lookup(self.module.0), &interner);
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

    pub(crate) fn build_tys(&mut self) {
        let (inference, ty_diagnostics) = hir_ty::infer_all(
            self.bodies_map
                .borrow_mut()
                .get(&self.module)
                .expect("this module should've been compiled"),
            self.module,
            &self.world_index.borrow_mut(),
        );
        if self.verbose >= 2 {
            let debug = inference.debug(&self.interner.borrow_mut());
            println!("{}", debug);
            if !debug.is_empty() {
                println!();
            }
        }
        self.tys_map.borrow_mut().insert(self.module, inference);
        self.diagnostics.extend(
            ty_diagnostics
                .iter()
                .cloned()
                .map(diagnostics::Diagnostic::from_ty),
        );
    }

    pub(crate) fn has_main(&self) -> bool {
        self.world_index
            .borrow_mut()
            .get_module(self.module)
            .unwrap()
            .function_names()
            .any(|name| self.interner.borrow_mut().lookup(name.0) == "main")
    }

    pub(crate) fn print_diagnostics(&self) {
        let line_index = LineIndex::new(&self.contents);
        for diagnostic in &self.diagnostics {
            println!(
                "{}",
                diagnostic
                    .display(
                        &self.file_name,
                        &self.contents,
                        &self.interner.borrow_mut(),
                        &line_index
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

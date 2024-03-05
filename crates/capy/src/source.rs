use std::{cell::RefCell, path::PathBuf, rc::Rc};

use ast::{AstNode, Root};
use diagnostics::{Diagnostic, Severity};
use hir::{FileName, Name};
use interner::Interner;
use line_index::LineIndex;
use parser::Parse;
use rustc_hash::FxHashSet;
use uid_gen::UIDGenerator;

pub(crate) struct SourceFile {
    pub(crate) file_name: PathBuf,
    pub(crate) contents: String,
    pub(crate) module: FileName,
    parse: Parse,
    root: Root,
    diagnostics: Vec<Diagnostic>,
    uid_gen: Rc<RefCell<UIDGenerator>>,
    interner: Rc<RefCell<Interner>>,
    world_index: Rc<RefCell<hir::WorldIndex>>,
    world_bodies: Rc<RefCell<hir::WorldBodies>>,
    index: hir::Index,
    verbose: u8,
}

impl SourceFile {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn parse(
        file_name: PathBuf,
        contents: String,
        uid_gen: Rc<RefCell<UIDGenerator>>,
        interner: Rc<RefCell<Interner>>,
        world_index: Rc<RefCell<hir::WorldIndex>>,
        world_bodies: Rc<RefCell<hir::WorldBodies>>,
        mod_dir: &std::path::Path,
        verbose: u8,
    ) -> SourceFile {
        let module = hir::FileName(interner.borrow_mut().intern(&file_name.to_string_lossy()));

        let is_mod = module.is_mod(mod_dir, &interner.borrow());

        if (!is_mod && verbose >= 1) || (is_mod && verbose >= 3) {
            println!("=== {} ===\n", file_name.display());
        }

        let parse = parser::parse_source_file(&lexer::lex(&contents), &contents);
        if verbose >= 4 {
            println!("{:?}\n", parse);
        }

        let tree = parse.syntax_tree();
        let root = ast::Root::cast(tree.root(), tree).unwrap();

        let validation_diagnostics = ast::validation::validate(root, tree);

        let (index, indexing_diagnostics) = hir::index(root, tree, &mut interner.borrow_mut());

        let mut res = Self {
            file_name,
            contents,
            module,
            parse,
            root,
            diagnostics: Vec::new(),
            uid_gen,
            interner,
            world_bodies,
            index,
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

    pub(crate) fn build_bodies(&mut self, mod_dir: &std::path::Path) -> FxHashSet<FileName> {
        let tree = self.parse.syntax_tree();

        let (bodies, lowering_diagnostics) = hir::lower(
            self.root,
            tree,
            self.file_name.as_path(),
            &self.index,
            &mut self.uid_gen.borrow_mut(),
            &mut self.interner.borrow_mut(),
            mod_dir,
            false,
        );

        self.world_index
            .borrow_mut()
            .add_file(self.module, self.index.clone());

        if (!self.module.is_mod(mod_dir, &self.interner.borrow()) && self.verbose >= 1)
            || self.verbose >= 3
        {
            let interner = self.interner.borrow();
            let debug = bodies.debug(self.module, mod_dir, &interner, self.verbose >= 2);
            if !debug.is_empty() {
                println!("{}", debug);
            }
        }

        let imports = bodies.imports().clone();

        self.world_bodies.borrow_mut().add_file(self.module, bodies);
        self.diagnostics.extend(
            lowering_diagnostics
                .iter()
                .cloned()
                .map(diagnostics::Diagnostic::from_lowering),
        );

        imports
    }

    pub(crate) fn has_fn_of_name(&self, name: Name) -> bool {
        self.world_bodies.borrow()[self.module].global_exists(name)
    }

    pub(crate) fn print_diagnostics(&self, mod_dir: &std::path::Path, with_color: bool) {
        let line_index = LineIndex::new(&self.contents);
        for diagnostic in &self.diagnostics {
            println!(
                "{}",
                diagnostic
                    .display(
                        &self.file_name.to_string_lossy(),
                        &self.contents,
                        mod_dir,
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

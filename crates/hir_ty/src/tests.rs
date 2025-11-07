mod arrays;
mod arrays_anon;
mod assignment;
mod assignment_quick;
mod binary;
mod cast;
mod char_and_str;
mod compiler_directives;
mod comptime;
mod default_values;
mod defers;
mod distincts;
mod entry_point;
mod enums;
mod error_unions;
mod r#extern;
mod functions;
mod generics;
mod globals;
mod if_else;
mod inference;
mod ints;
mod jumps;
mod lambda;
mod locals;
mod optionals;
mod paren;
mod pointers;
mod raw_types;
mod recursion;
mod simple;
mod slices;
mod structs;
mod structs_anon;
mod types;
mod unary;

use std::{path::Path, vec};

use super::*;
use ast::AstNode;
use codegen::Verbosity;
use expect_test::Expect;
use interner::Interner;
use line_index::LineIndex;
use target_lexicon::Triple;
use uid_gen::UIDGenerator;

#[track_caller]
fn check<const N: usize>(
    input: &str,
    expect: Expect,
    expected_diagnostics: impl Fn(
        &mut Interner,
    ) -> [(
        TyDiagnosticKind,
        std::ops::Range<u32>,
        Option<(TyDiagnosticHelpKind, std::ops::Range<u32>)>,
    ); N],
) {
    check_impl(input, expect, expected_diagnostics, None)
}

#[track_caller]
fn check_impl<const N: usize>(
    input: &str,
    expect: Expect,
    expected_diagnostics: impl Fn(
        &mut Interner,
    ) -> [(
        TyDiagnosticKind,
        std::ops::Range<u32>,
        Option<(TyDiagnosticHelpKind, std::ops::Range<u32>)>,
    ); N],
    entry_point: Option<&str>,
) {
    let modules = test_utils::split_multi_module_test_data(input);
    let mut interner = Interner::default();
    let mut world_index = hir::WorldIndex::default();

    let mut uid_gen = UIDGenerator::default();
    let mut world_bodies = hir::WorldBodies::default();

    let mut parse_diags = Vec::<parser::SyntaxError>::new();
    let mut index_diags = Vec::new();
    let mut lowering_diags = Vec::new();

    for (name, text) in &modules {
        if *name == "main.capy" {
            continue;
        }

        let tokens = lexer::lex(text);
        let parse = parser::parse_source_file(&tokens, text);
        parse_diags.extend(parse.errors());
        let tree = parse.into_syntax_tree();

        let root = ast::Root::cast(tree.root(), &tree).unwrap();
        let (index, _) = hir::index(root, &tree, &mut interner);

        let module = FileName(interner.intern(name));

        let (bodies, _) = hir::lower(
            root,
            &tree,
            Path::new(name),
            &index,
            &mut uid_gen,
            &mut interner,
            Path::new(""),
            true,
        );
        let debug = bodies.debug(module, std::path::Path::new(""), &interner, true, true);
        if !debug.is_empty() {
            println!("{}", debug);
        }
        world_index.add_file(module, index);
        world_bodies.add_file(module, bodies);
    }

    let text = &modules["main.capy"];
    let module = FileName(interner.intern("main.capy"));
    let tokens = lexer::lex(text);
    let parse = parser::parse_source_file(&tokens, text);
    parse_diags.extend(parse.errors());

    let tree = parse.into_syntax_tree();
    let root = ast::Root::cast(tree.root(), &tree).unwrap();

    let (index, d) = hir::index(root, &tree, &mut interner);
    index_diags.extend(d);

    let (bodies, d) = hir::lower(
        root,
        &tree,
        Path::new("main"),
        &index,
        &mut uid_gen,
        &mut interner,
        Path::new(""),
        true,
    );
    let debug = bodies.debug(module, std::path::Path::new(""), &interner, true, true);
    if !debug.is_empty() {
        println!("{}", debug);
    }
    lowering_diags.extend(d);
    world_index.add_file(module, index);
    world_bodies.add_file(module, bodies);

    // print errors just in case it's useful
    if !parse_diags.is_empty() {
        println!("parse errors: {:#?}", parse_diags);
    }
    if !index_diags.is_empty() {
        println!("index errors: {:#?}", index_diags);
    }
    if !lowering_diags.is_empty() {
        println!("lowering errors: {:#?}", lowering_diags);
    }

    let entry_point = entry_point.map(|entry_point| Fqn {
        file: module,
        name: Name(interner.intern(entry_point)),
    });

    let mut comptime_results = ComptimeResultMap::default();

    let mut generic_values = Arena::new();

    let InferenceResult {
        tys,
        diagnostics: actual_diagnostics,
        any_were_unsafe_to_compile,
    } = InferenceCtx::new(
        &world_index,
        &world_bodies,
        &interner,
        &mut generic_values,
        |comptime, tys| {
            codegen::eval_comptime_blocks(
                Verbosity::AllFunctions {
                    include_disasm: true,
                },
                &mut std::iter::once(unsafe { std::mem::transmute(comptime) }),
                unsafe { std::mem::transmute(&mut comptime_results) },
                Path::new(""),
                &interner,
                &world_bodies,
                // transmute to get past cyclic dependencies
                #[allow(clippy::missing_transmute_annotations)]
                unsafe {
                    std::mem::transmute(tys)
                },
                Triple::host().pointer_width().unwrap().bits(),
            );

            unsafe { std::mem::transmute(comptime_results[comptime].clone()) }
        },
    )
    .finish(entry_point, true);

    let tys_debug = tys.debug(Path::new(""), &interner, true, false);
    expect.assert_eq(&tys_debug);

    // print tys_debug so we can see it in case something fails with the diagnostics
    println!("{tys_debug}");

    let expected_diagnostics: Vec<_> = expected_diagnostics(&mut interner)
        .into_iter()
        .map(|(kind, range, help)| TyDiagnostic {
            kind,
            file: module,
            expr: None,
            range: TextRange::new(range.start.into(), range.end.into()),
            help: help.map(|(kind, range)| TyDiagnosticHelp {
                kind,
                range: TextRange::new(range.start.into(), range.end.into()),
            }),
        })
        .collect();

    // this is so unbelievably jank
    //
    // since we're in a cyclic dependency with diagnostics,
    // diagnostics's version of the hir_ty crate doesn't
    // have a value for the thread local ENUM_MAP.
    //
    // so here, we're giving the second copy of hir_ty our enum map
    //
    // I'm actually ashamed to have programmed something this awful
    //
    // todo: make better choices
    let our_map = ENUM_MAP.with_borrow(|map| map.clone());
    #[allow(clippy::missing_transmute_annotations)]
    diagnostics::hir::common::ENUM_MAP.set(unsafe { std::mem::transmute(our_map) });

    let our_map = TYPE_NAMES.with_borrow(|map| map.clone());
    #[allow(clippy::missing_transmute_annotations)]
    diagnostics::hir::common::TYPE_NAMES.set(unsafe { std::mem::transmute(our_map) });

    // I display the diagnostics here so if there's a mismatch one can visually see it

    let line_index = LineIndex::new(text);
    println!("EXPECTED DIAGNOSTICS:");
    if expected_diagnostics.is_empty() {
        println!("(no expected diagnostics)");
    }
    let res = std::panic::catch_unwind(|| {
        for d in &expected_diagnostics {
            println!(
                "{}",
                diagnostics::Diagnostic::from_ty(unsafe {
                    // transmute is needed to get around cyclic dependencies
                    #[allow(clippy::missing_transmute_annotations)]
                    std::mem::transmute(d.clone())
                })
                .display(
                    "main.capy",
                    text,
                    Path::new(""),
                    &interner,
                    &line_index,
                    true,
                )
                .join("\n")
            );
        }
    });
    if res.is_err() {
        println!("(panic while printing diagnostics)");
    }
    println!("ACTUAL DIAGNOSTICS:");
    if actual_diagnostics.is_empty() {
        println!("(no actual diagnostics)");
    }
    for d in &actual_diagnostics {
        println!(
            "{}",
            diagnostics::Diagnostic::from_ty(unsafe {
                // transmute is needed to get around cyclic dependencies
                #[allow(clippy::missing_transmute_annotations)]
                std::mem::transmute(d.clone())
            })
            .display(
                "main.capy",
                text,
                Path::new(""),
                &interner,
                &line_index,
                true,
            )
            .join("\n")
        );
    }

    dbg!(expected_diagnostics == actual_diagnostics);
    pretty_assertions::assert_eq!(expected_diagnostics, actual_diagnostics);

    let actual_diagnostics = actual_diagnostics
        .into_iter()
        .filter(|d| d.expr.is_some() && d.is_error())
        .collect_vec();

    let any_errs = !parse_diags.is_empty()
        || !index_diags.is_empty()
        || !lowering_diags.is_empty()
        || !actual_diagnostics.is_empty();

    if any_errs != any_were_unsafe_to_compile {
        if !any_errs {
            println!("no errors");
        }

        println!("anything was unsafe: {}", any_were_unsafe_to_compile);

        if !any_errs {
            panic!("no errors but unsafe to compile");
        } else {
            panic!("errors but safe to compile");
        }
    }
    assert_eq!(any_errs, any_were_unsafe_to_compile);
}

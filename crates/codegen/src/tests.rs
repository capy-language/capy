use core::panic;
use std::{collections::HashMap, env, fs, path::Path};

use ast::AstNode;
use expect_test::{Expect, expect};
use hir::common::{FileName, Fqn, Name};
use hir_ty::{InferenceCtx, InferenceResult, WorldTys};
use la_arena::Arena;
use line_index::LineIndex;
use path_clean::PathClean;
use rustc_hash::FxHashMap;
use target_lexicon::HOST;
use uid_gen::UIDGenerator;

use super::*;

#[track_caller]
fn check_files(
    main_file: &str,
    other_files: &[&str],
    entry_point: &str,
    stdout_expect: Expect,
    expected_status: i32,
) {
    println!("testing {main_file}");

    let current_dir = env!("CARGO_MANIFEST_DIR");
    env::set_current_dir(current_dir).unwrap();

    let mut modules = FxHashMap::default();

    let core_deps: Vec<_> = glob::glob("../../core/src/**/*.capy")
        .unwrap()
        .map(|path| path.unwrap().into_os_string().into_string().unwrap())
        .collect();

    for file in other_files
        .iter()
        .copied()
        .chain(core_deps.iter().map(|f| f.as_str()))
    {
        let file = file.replace('/', std::path::MAIN_SEPARATOR_STR);
        let file = Path::new(current_dir).join(file).clean();
        let text = fs::read_to_string(&file).unwrap();

        modules.insert(file.to_string_lossy().to_string(), text);
    }

    let main_file = main_file.replace('/', std::path::MAIN_SEPARATOR_STR);
    let main_file = Path::new(current_dir).join(main_file).clean();
    let text = fs::read_to_string(&main_file).unwrap();
    modules.insert(main_file.to_string_lossy().to_string(), text);

    let binary_name = main_file.file_stem().unwrap().to_string_lossy();

    check_impl(
        modules
            .iter()
            .map(|(k, v)| (k.as_str(), v.as_str()))
            .collect(),
        &main_file.to_string_lossy(),
        entry_point,
        false,
        &[],
        &binary_name,
        stdout_expect,
        expected_status,
    )
}

#[track_caller]
fn check_raw(
    input: &str,
    entry_point: &str,
    include_core: bool,
    stdout_expect: Expect,
    expected_status: i32,
) {
    check_raw_with_args(
        input,
        entry_point,
        include_core,
        &[],
        stdout_expect,
        expected_status,
    )
}

#[track_caller]
fn check_raw_with_args(
    input: &str,
    entry_point: &str,
    include_core: bool,
    args: &[&str],
    stdout_expect: Expect,
    expected_status: i32,
) {
    let modules = test_utils::split_multi_module_test_data(input);

    let hash = sha256::digest(modules["main.capy"]);
    let hash = &hash[..7];

    if include_core {
        let current_dir = env!("CARGO_MANIFEST_DIR");
        env::set_current_dir(current_dir).unwrap();

        let core_deps: Vec<_> = glob::glob("../../core/src/**/*.capy")
            .unwrap()
            .map(|path| path.unwrap().into_os_string().into_string().unwrap())
            .collect();

        let mut modules: HashMap<_, _> = modules
            .into_iter()
            .map(|(k, v)| {
                (
                    format!("{current_dir}{}{k}", std::path::MAIN_SEPARATOR),
                    v.to_string(),
                )
            })
            .collect();

        println!("{:#?}", modules);

        for file in core_deps {
            let file = Path::new(current_dir).join(file).clean();
            let text = fs::read_to_string(&file).unwrap();

            modules.insert(file.to_string_lossy().to_string(), text);
        }

        check_impl(
            modules
                .iter()
                .map(|(k, v)| (k.as_str(), v.as_str()))
                .collect(),
            &format!("{current_dir}{}main.capy", std::path::MAIN_SEPARATOR),
            entry_point,
            false,
            args,
            hash,
            stdout_expect,
            expected_status,
        )
    } else {
        check_impl(
            modules,
            "main.capy",
            entry_point,
            true,
            args,
            hash,
            stdout_expect,
            expected_status,
        )
    }
}

#[track_caller]
fn check_impl(
    modules: FxHashMap<&str, &str>,
    main_file: &str,
    entry_point: &str,
    fake_file_system: bool,
    args: &[&str],
    binary_name: &str,
    stdout_expect: Expect,
    expected_status: i32,
) {
    let mod_dir = if fake_file_system {
        std::path::PathBuf::new()
    } else {
        env::current_dir().unwrap().join("../../").clean()
    };

    let mut interner = Interner::default();
    let mut world_index = hir::WorldIndex::default();

    let mut uid_gen = UIDGenerator::default();
    let mut world_bodies = hir::WorldBodies::default();

    let mut line_indicies = FxHashMap::default();

    for (file, text) in &modules {
        if *file == main_file {
            continue;
        }

        let tokens = lexer::lex(text);
        let parse = parser::parse_source_file(&tokens, text);

        let module = FileName(interner.intern(file));
        line_indicies.insert(module, LineIndex::new(text));
        let line_index = &line_indicies[&module];

        let no_diagnostics = parse.errors().is_empty();
        for d in parse.errors() {
            println!(
                "{}",
                diagnostics::Diagnostic::from_syntax(*d)
                    .display(*file, text, &mod_dir, &interner, &line_index, true,)
                    .join("\n")
            );
        }
        assert!(no_diagnostics);

        let tree = parse.into_syntax_tree();
        let root = ast::Root::cast(tree.root(), &tree).unwrap();
        let (index, diagnostics) = hir::index(root, &tree, &mut interner);

        let no_diagnostics = diagnostics.is_empty();
        for d in diagnostics {
            println!(
                "{}",
                diagnostics::Diagnostic::from_indexing(d)
                    .display(*file, text, &mod_dir, &interner, &line_index, true,)
                    .join("\n")
            );
        }
        assert!(no_diagnostics);

        let (bodies, diagnostics) = hir::lower(
            root,
            &tree,
            std::path::Path::new(*file),
            &index,
            &mut uid_gen,
            &mut interner,
            &mod_dir,
            fake_file_system,
        );
        let debug = bodies.debug(module, &mod_dir, &interner, true, true);
        if !debug.is_empty() {
            println!("{}", debug);
        }

        let no_diagnostics = diagnostics.is_empty();
        for d in diagnostics {
            println!(
                "{}",
                diagnostics::Diagnostic::from_lowering(d)
                    .display(*file, text, &mod_dir, &interner, &line_index, true,)
                    .join("\n")
            );
        }
        assert!(no_diagnostics);

        world_index.add_file(module, index);
        world_bodies.add_file(module, bodies);
    }

    let text = &modules[main_file];

    let file = FileName(interner.intern(main_file));
    line_indicies.insert(file, LineIndex::new(text));
    let line_index = &line_indicies[&file];

    let tokens = lexer::lex(text);
    let parse = parser::parse_source_file(&tokens, text);

    let no_diagnostics = parse.errors().is_empty();
    for d in parse.errors() {
        println!(
            "{}",
            diagnostics::Diagnostic::from_syntax(*d)
                .display(main_file, text, &mod_dir, &interner, line_index, true,)
                .join("\n")
        );
    }
    assert!(no_diagnostics);

    let tree = parse.into_syntax_tree();
    let root = ast::Root::cast(tree.root(), &tree).unwrap();
    let (index, diagnostics) = hir::index(root, &tree, &mut interner);

    let no_diagnostics = diagnostics.is_empty();
    for d in diagnostics {
        println!(
            "{}",
            diagnostics::Diagnostic::from_indexing(d)
                .display(main_file, text, &mod_dir, &interner, line_index, true,)
                .join("\n")
        );
    }
    assert!(no_diagnostics);

    let (bodies, diagnostics) = hir::lower(
        root,
        &tree,
        std::path::Path::new(main_file),
        &index,
        &mut uid_gen,
        &mut interner,
        &mod_dir,
        fake_file_system,
    );
    let debug = bodies.debug(file, &mod_dir, &interner, true, true);
    if !debug.is_empty() {
        println!("{}", debug);
    }

    let no_diagnostics = diagnostics.is_empty();
    for d in diagnostics {
        println!(
            "{}",
            diagnostics::Diagnostic::from_lowering(d)
                .display(main_file, text, &mod_dir, &interner, line_index, true,)
                .join("\n")
        );
    }
    assert!(no_diagnostics);
    world_index.add_file(file, index);
    world_bodies.add_file(file, bodies);

    let entry_point = Fqn {
        file,
        name: Name(interner.intern(entry_point)),
    }
    .make_concrete(None);

    let mut comptime_results = ComptimeResultMap::default();

    let mut generic_vals = Arena::new();

    let InferenceResult {
        tys, diagnostics, ..
    } = InferenceCtx::new(
        &world_index,
        &world_bodies,
        &interner,
        &mut generic_vals,
        |comptime, tys| {
            eval_comptime_blocks(
                Verbosity::AllFunctions {
                    include_disasm: true,
                },
                &mut std::iter::once(comptime),
                &mut comptime_results,
                &mod_dir,
                &interner,
                &world_bodies,
                tys,
                HOST.pointer_width().unwrap().bits(),
            );

            comptime_results[comptime].clone()
        },
    )
    .finish(Some(entry_point.to_naive()), false);

    println!("{}", tys.debug(&mod_dir, &interner, true, true));

    let no_diagnostics = diagnostics.is_empty();
    for d in diagnostics {
        let file = d.file;
        let file_name = interner.lookup(file.0);
        println!(
            "{}",
            diagnostics::Diagnostic::from_ty(d)
                .display(
                    file_name,
                    modules[file_name],
                    Path::new(""),
                    &interner,
                    &line_indicies[&file],
                    true,
                )
                .join("\n")
        );
    }
    assert!(no_diagnostics);

    println!("comptime:");

    // evaluate any comptimes that haven't been ran yet
    eval_comptime_blocks(
        Verbosity::AllFunctions {
            include_disasm: true,
        },
        &mut world_bodies.find_comptimes(),
        &mut comptime_results,
        &mod_dir,
        &interner,
        &world_bodies,
        &tys,
        HOST.pointer_width().unwrap().bits(),
    );

    println!("actual program:");

    let bytes = compile_obj(
        Verbosity::AllFunctions {
            include_disasm: true,
        },
        entry_point,
        if fake_file_system {
            Path::new("")
        } else {
            &mod_dir
        },
        &interner,
        &world_bodies,
        &tys,
        &comptime_results,
        HOST,
    )
    .unwrap();

    let output_folder = PathBuf::from("test-temp");

    let _ = fs::create_dir(&output_folder);

    let file = output_folder.join(format!("{}.o", binary_name));
    fs::write(&file, bytes.as_slice()).unwrap_or_else(|why| {
        panic!("{}: {why}", file.display());
    });

    let exec = link_to_exec(&file, &HOST, &[]).unwrap();

    let output = std::process::Command::new(&exec)
        .args(args)
        .output()
        .unwrap_or_else(|_| panic!("{} did not run successfully", exec.display()));

    println!("test exited with {}", output.status);

    let stdout = std::str::from_utf8(&output.stdout)
        .unwrap()
        .replace('\r', "");
    let stdout = format!("{}\n", stdout);

    println!("stdout: {:?}", stdout);

    dbg!(&stdout_expect.data());
    println!("expected: {:?}", trim_indent(stdout_expect.data()));
    stdout_expect.assert_eq(&stdout);

    assert_eq!(output.status.code().unwrap(), expected_status);
}

/// since `trim_indent` is a private function in `expect_test`,
/// the function has been recreated here so that better debugging can be done
fn trim_indent(mut text: &str) -> String {
    if text.starts_with('\n') {
        text = &text[1..];
    }
    let indent = text
        .lines()
        .filter(|it| !it.trim().is_empty())
        .map(|it| it.len() - it.trim_start().len())
        .min()
        .unwrap_or(0);

    lines_with_ends(text)
        .map(|line| {
            if line.len() <= indent {
                line.trim_start_matches(' ')
            } else {
                &line[indent..]
            }
        })
        .collect()
}

fn lines_with_ends(text: &str) -> LinesWithEnds {
    LinesWithEnds { text }
}

struct LinesWithEnds<'a> {
    text: &'a str,
}

impl<'a> Iterator for LinesWithEnds<'a> {
    type Item = &'a str;
    fn next(&mut self) -> Option<&'a str> {
        if self.text.is_empty() {
            return None;
        }
        let idx = self.text.find('\n').map_or(self.text.len(), |it| it + 1);
        let (res, next) = self.text.split_at(idx);
        self.text = next;
        Some(res)
    }
}

#[test]
fn hello_world() {
    check_files(
        "../../examples/hello_world.capy",
        &[],
        "main",
        expect![[r#"
        Hello, World!

        "#]],
        0,
    )
}

#[test]
fn vectors() {
    check_files(
        "../../examples/vectors.capy",
        &[],
        "main",
        expect![[r#"
        my_point: (1, 2, 3)

        "#]],
        0,
    )
}

#[test]
fn fib() {
    check_files(
        "../../examples/fib.capy",
        &["../../examples/io.capy"],
        "main",
        expect![[r#"
        Running Fibonacci #28
        Ready... Go!
        Fibonacci number #28 = 317811

        "#]],
        0,
    )
}

#[test]
fn drink() {
    check_files(
        "../../examples/drink.capy",
        &[],
        "main",
        expect![[r#"
        you can drink

        "#]],
        0,
    )
}

#[test]
fn arrays() {
    check_files(
        "../../examples/arrays.capy",
        &[],
        "main",
        expect![[r#"
        4
        8
        15
        16
        23
        42

        "#]],
        0,
    )
}

#[test]
fn arrays_of_arrays() {
    check_files(
        "../../examples/arrays_of_arrays.capy",
        &["../../examples/io.capy"],
        "main",
        expect![[r#"
            my_array[0][0][0] = 2
            my_array[0][0][1] = 4
            my_array[0][0][2] = 6
            my_array[0][1][0] = 2
            my_array[0][1][1] = 4
            my_array[0][1][2] = 6
            my_array[0][2][0] = 2
            my_array[0][2][1] = 4
            my_array[0][2][2] = 6
            my_array[1][0][0] = 2
            my_array[1][0][1] = 4
            my_array[1][0][2] = 6
            my_array[1][1][0] = 127
            my_array[1][1][1] = 0
            my_array[1][1][2] = 42
            my_array[1][2][0] = 2
            my_array[1][2][1] = 4
            my_array[1][2][2] = 6
            my_array[2][0][0] = 2
            my_array[2][0][1] = 4
            my_array[2][0][2] = 6
            my_array[2][1][0] = 2
            my_array[2][1][1] = 4
            my_array[2][1][2] = 6
            my_array[2][2][0] = 2
            my_array[2][2][1] = 4
            my_array[2][2][2] = 6

            global[0][0][0] = 105
            global[0][0][1] = 115
            global[0][0][2] = 125
            global[0][1][0] = 105
            global[0][1][1] = 115
            global[0][1][2] = 125
            global[0][2][0] = 105
            global[0][2][1] = 115
            global[0][2][2] = 125
            global[1][0][0] = 105
            global[1][0][1] = 115
            global[1][0][2] = 125
            global[1][1][0] = 105
            global[1][1][1] = 115
            global[1][1][2] = 125
            global[1][2][0] = 105
            global[1][2][1] = 115
            global[1][2][2] = 125
            global[2][0][0] = 105
            global[2][0][1] = 115
            global[2][0][2] = 125
            global[2][1][0] = 105
            global[2][1][1] = 115
            global[2][1][2] = 125
            global[2][2][0] = 105
            global[2][2][1] = 115
            global[2][2][2] = 125

        "#]],
        0,
    )
}

#[test]
fn slices() {
    check_files(
        "../../examples/slices.capy",
        &[],
        "main",
        expect![[r#"
        [ 4, 8, 15, 16, 23, 42 ]
        [ 1, 2, 3 ]
        [ 4, 5, 6, 7, 8 ]
        [ 4, 8, 15, 16, 23, 42 ]

        "#]],
        0,
    )
}

#[test]
fn files() {
    check_files(
        "../../examples/file_system.capy",
        &[],
        "main",
        expect![[r#"
        writing to hello.txt
        reading from hello.txt
        Hello, World!

        "#]],
        0,
    )
}

#[test]
fn ptr_assign() {
    check_files(
        "../../examples/ptr_assign.capy",
        &[],
        "main",
        expect![[r#"
        x = 5
        x = 25

        x = { 1, 2, 3 }
        x = { 1, 42, 3 }

        "#]],
        0,
    )
}

#[test]
fn pretty() {
    check_files(
        "../../examples/pretty.capy",
        &[],
        "main",
        expect![["
            \u{1b}[32mHello!\u{b}\u{1b}[34mWorld\u{1b}[0m

            Joe\u{8}\u{8}\u{8}P
            ALERT!\u{7}
            \u{c}And
            \tnow..
            \u{1b}[1;90mC\u{1b}[91mO\u{1b}[92mL\u{1b}[93m\u{1b}[94mO\u{1b}[95mR\u{1b}[96mS\u{1b}[97m!\u{1b}[0m

        "]],
        0,
    )
}

#[test]
fn float_to_string() {
    check_files(
        "../../examples/float_to_string.capy",
        &[],
        "main",
        expect![[r#"
        3.141

        ln 10 = 2.302
        ln 50 = 3.912
        ln 100 = 4.605
        ln 500 = 6.214
        log 10 = 1.000
        log 50 = 1.698
        log 100 = 1.999
        log 500 = 2.698
         1 / 0 = +Inf
        -1 / 0 = -Inf
         0 / 0 = NaN

        "#]],
        0,
    )
}

#[test]
fn first_class_functions() {
    check_files(
        "../../examples/first_class_functions.capy",
        &["../../examples/io.capy"],
        "main",
        expect![[r#"
        apply add to  1 and 2 ... 3
        apply sub to  5 and 3 ... 2
        apply mul to  3 and 2 ... 6
        apply div to 10 and 2 ... 5
        apply pow to  2 and 3 ... 8

        "#]],
        50,
    )
}

#[test]
fn structs() {
    check_files(
        "../../examples/structs.capy",
        &[],
        "main",
        expect![[r#"
        people:
        Bob is 3 years old
        Terry is 48 years old
        Walter is 52 years old

        some_guy:
        Terry is 1000 years old

        "#]],
        0,
    )
}

#[test]
fn comptime() {
    check_files(
        "../../examples/comptime.capy",
        &["../../examples/io.capy"],
        "main",
        expect![[r#"
        Hello at runtime!
        that global was equal to 10
        2^0 = 1
        2^1 = 2
        2^2 = 4
        2^3 = 8
        2^4 = 16
        2^5 = 32

        "#]],
        0,
    )
}

// comptime_types.capy cannot be tested as it gets user input

#[test]
fn strings() {
    check_files(
        "../../examples/strings.capy",
        &[],
        "main",
        expect![[r#"
        Hello World!

        "#]],
        0,
    )
}

#[test]
fn auto_deref() {
    check_files(
        "../../examples/auto_deref.capy",
        &["../../examples/io.capy"],
        "main",
        expect![[r#"
        struct auto deref:
        my_foo.b   8
        ptr^^^^.b  8
        ptr^^^.b   8
        ptr^^.b    8
        ptr^.b     8
        ptr.b      8
          give:
        ptr^^.b    8
        ptr^.b     8
        ptr.b      8

        array auto deref:
        ptr^[0] 4
        ptr[0]  4
        ptr^[1] 8
        ptr[1]  8
        ptr^[2] 15
        ptr[2]  15
        ptr_ptr^^[3] 16
        ptr_ptr^[3]  16
        ptr_ptr[3]   16
        ptr_ptr^^[4] 23
        ptr_ptr^[4]  23
        ptr_ptr[4]   23
        ptr_ptr^^[5] 42
        ptr_ptr^[5]  42
        ptr_ptr[5]   42
          give:
        ptr_ptr^^[0] 4
        ptr_ptr^[0]  4
        ptr_ptr[0]   4
        ptr_ptr^^[1] 8
        ptr_ptr^[1]  8
        ptr_ptr[1]   8
        ptr_ptr^^[2] 15
        ptr_ptr^[2]  15
        ptr_ptr[2]   15
        ptr_ptr^^[3] 16
        ptr_ptr^[3]  16
        ptr_ptr[3]   16
        ptr_ptr^^[4] 23
        ptr_ptr^[4]  23
        ptr_ptr[4]   23
        ptr_ptr^^[5] 42
        ptr_ptr^[5]  42
        ptr_ptr[5]   42

        "#]],
        0,
    )
}

#[test]
fn reflection() {
    check_files(
        "../../examples/reflection.capy",
        &["../../examples/io.capy"],
        "main",
        expect![[r#"
            Reflection!

            i32                (0x8000284) : size = 4, align = 4, stride = 4
            i64                (0x8000308) : size = 8, align = 8, stride = 8
            u64                (0x8000108) : size = 8, align = 8, stride = 8
            i8                 (0x8000221) : size = 1, align = 1, stride = 1
            u128               (0x8000110) : size = 16, align = 8, stride = 16
            usize              (0x8000108) : size = 8, align = 8, stride = 8
            f32                (0xc000084) : size = 4, align = 4, stride = 4
            void               (0x4000020) : size = 0, align = 1, stride = 0
            any                (0x20000110) : size = 16, align = 8, stride = 16
            rawptr             (0x28000108) : size = 8, align = 8, stride = 8
            rawslice           (0x2c000110) : size = 16, align = 8, stride = 16
            str                (0x14000108) : size = 8, align = 8, stride = 8
            bool               (0x10000021) : size = 1, align = 1, stride = 1
            char               (0x18000021) : size = 1, align = 1, stride = 1
            type               (0x1c000084) : size = 4, align = 4, stride = 4
            Person             (0x40000000) : size = 12, align = 8, stride = 16
            Foo                (0x40000001) : size = 1, align = 1, stride = 1
            [6] Person         (0x48000000) : size = 96, align = 8, stride = 96
            [ ] Person         (0x4c000000) : size = 16, align = 8, stride = 16
             ^  Person         (0x50000000) : size = 8, align = 8, stride = 8
            distinct Person    (0x44000000) : size = 12, align = 8, stride = 16
            Dessert            (0x58000000) : size = 17, align = 8, stride = 24
            Dessert.Brownie    (0x5c000004) : size = 0, align = 1, stride = 0
            Dessert.Apple_Pie  (0x5c000002) : size = 16, align = 8, stride = 16
            Dessert.Milkshake  (0x5c000007) : size = 1, align = 1, stride = 1
            Farm_Animal        (0x58000001) : size = 1, align = 1, stride = 1
            Farm_Animal.Sheep  (0x5c000009) : size = 0, align = 1, stride = 0
            ()       -> void   (0x54000000) : size = 8, align = 8, stride = 8
            (x: i32) -> f32    (0x54000001) : size = 8, align = 8, stride = 8
            ?i32               (0x60000000) : size = 5, align = 4, stride = 8
            ?^i32              (0x60000001) : size = 8, align = 8, stride = 8

            i32 == i16 : false
            i32 == u32 : false
            i32 == i32 : true
            Foo == Person : false
            Person == Person : true
            [5] Person == [6] Person : false
            [5] Foo == [5] Person : false
            [6] Person == [6] Person : true
            ^Person == ^Foo : false
            ^Person == ^Person : true
            Person == distinct 'a Person : false
            distinct 'a Person == distinct 'b Person : false
            distinct 'b Person == distinct 'b Person : true
            Dessert == Farm_Animal : false
            Dessert == Dessert : true
            type.(Dessert.Apple_Pie) == type.(Dessert.Cheesecake) : false
            type.(Dessert.Cheesecake) == type.(Dessert.Cheesecake) : true
            type.(Dessert.Ice_Cream) == type.(Dessert.Cheesecake) : false
            type.(Farm_Animal.Cow) == type.(Dessert.Ice_Cream) : false
            type.(Farm_Animal.Cow) == type.(Farm_Animal.Cow) : true
            type.(Farm_Animal.Cow) == type.(Farm_Animal.Sheep) : false
            Dessert.Apple_Pie == Dessert.Cheesecake : false
            Dessert.Cheesecake == Dessert.Cheesecake : true
            Dessert.Ice_Cream == Dessert.Cheesecake : false
            Farm_Animal.Cow == Farm_Animal.Cow : true
            Farm_Animal.Cow == Farm_Animal.Sheep : false
            () -> void == (x : i32) -> f32 : false
            () -> void == () -> void : true
            ?u64 == ?u64 : true
            ?u64 == ?bool : false

            INT
            bit_width = 32
            signed    = true

            INT
            bit_width = 8
            signed    = false

            INT
            bit_width = 128
            signed    = false

            INT
            bit_width = 64
            signed    = true

            FLOAT
            bit_width = 32

            FLOAT
            bit_width = 64

            ARRAY
            len = 5
            ty =
             INT
             bit_width = 32
             signed    = true

            ARRAY
            len = 1000
            ty =
             ARRAY
             len = 3
             ty =
              FLOAT
              bit_width = 64

            SLICE
            ty =
             INT
             bit_width = 32
             signed    = true

            POINTER
            ty =
             INT
             bit_width = 32
             signed    = true

            POINTER
            ty =
             POINTER
             ty =
              POINTER
              ty =
               INT
               bit_width = 128
               signed    = true

            DISTINCT
            ty =
             INT
             bit_width = 32
             signed    = true

            DISTINCT
            ty =
             ARRAY
             len = 2
             ty =
              DISTINCT
              ty =
               INT
               bit_width = 8
               signed    = true

            STRUCT
            members =
             name = a
             offset = 0
             ty =
              BOOL

            STRUCT
            members =
             name = text
             offset = 0
             ty =
              STRING
             name = flag
             offset = 8
             ty =
              BOOL
             name = array
             offset = 10
             ty =
              ARRAY
              len = 3
              ty =
               INT
               bit_width = 16
               signed    = true

            STRUCT
            members =
             name = name
             offset = 0
             ty =
              STRING
             name = age
             offset = 8
             ty =
              INT
              bit_width = 32
              signed    = true

            ANY

            DISTINCT
            ty =
             STRUCT
             members =
              name = a
              offset = 0
              ty =
               BOOL

            DISTINCT
            ty =
             ENUM
             discriminant_offset = 0
             variants =
              VARIANT
              discriminant = 0
              ty =
               VOID
              VARIANT
              discriminant = 1
              ty =
               VOID
              VARIANT
              discriminant = 2
              ty =
               VOID
              VARIANT
              discriminant = 3
              ty =
               VOID

            ENUM
            discriminant_offset = 16
            variants =
             VARIANT
             discriminant = 0
             ty =
              VOID
             VARIANT
             discriminant = 2
             ty =
              VOID
             VARIANT
             discriminant = 10
             ty =
              STRUCT
              members =
               name = warm
               offset = 0
               ty =
                BOOL
               name = crumble
               offset = 1
               ty =
                BOOL
               name = crust_thickness
               offset = 8
               ty =
                FLOAT
                bit_width = 64
             VARIANT
             discriminant = 11
             ty =
              FLOAT
              bit_width = 32
             VARIANT
             discriminant = 12
             ty =
              VOID
             VARIANT
             discriminant = 42
             ty =
              VOID
             VARIANT
             discriminant = 45
             ty =
              VOID
             VARIANT
             discriminant = 46
             ty =
              STRUCT
              members =
               name = malt
               offset = 0
               ty =
                BOOL

            VARIANT
            discriminant = 0
            ty =
             VOID

            VARIANT
            discriminant = 10
            ty =
             STRUCT
             members =
              name = warm
              offset = 0
              ty =
               BOOL
              name = crumble
              offset = 1
              ty =
               BOOL
              name = crust_thickness
              offset = 8
              ty =
               FLOAT
               bit_width = 64

            VARIANT
            discriminant = 11
            ty =
             FLOAT
             bit_width = 32

            VARIANT
            discriminant = 46
            ty =
             STRUCT
             members =
              name = malt
              offset = 0
              ty =
               BOOL

            OPTIONAL
            discriminant_offset = 2
            ty =
             INT
             bit_width = 16
             signed    = true

            OPTIONAL
            discriminant_offset = 0
            ty =
             POINTER
             ty =
              BOOL

            123
            [ 4, 8, 15, 16, 23, 42 ]
            [ 1, 2, 3 ]
            ^52
            42
            42
            256
            hello
            ()
            i32
            ^struct { text: str, flag: bool, array: [3] i16 }
            any
            [ 3, -1, 4, 1, 5, 9 ]
            [ 4, 8, 15, 16, 23, 42 ]
            [ 1, hello, true, 5.030 ]
            { text = Hello, flag = false, array = [ 1, 2, 3 ] }
            { hello = world, foo = { bar = { baz = { qux = 1.200 } } } }
            { warm = true, crumble = false, crust_thickness = 1.300 }
            1089.500
            ()
            ()
            { malt = true }
            { warm = false, crumble = true, crust_thickness = 0.500 }
            30.000
            ()
            ()
            { malt = false }
            nil
            nil
            42
            ^21
            nil
            255
            this is an error!!
            1715004
            0x1a2b3c
            0b110100010101100111100

        "#]],
        0,
    )
}

#[test]
fn runtime_generic_lists() {
    check_files(
        "../../examples/lists_runtime_generic.capy",
        &[],
        "main",
        expect![[r#"
            ^42
            u128.[ 4, 8, 15, 16, 23 ]

        "#]],
        0,
    )
}

#[test]
fn comptime_generic_lists() {
    check_files(
        "../../examples/lists_comptime_generic.capy",
        &[],
        "main",
        expect![[r#"
            ^42
            u128.[ 4, 8, 15, 16, 23 ]

        "#]],
        0,
    )
}

#[test]
fn cast_f32_to_i32() {
    check_raw(
        r#"
            main :: () -> i32 {
                f : f32 = 2.5;

                i32.(f)
            }
        "#,
        "main",
        false,
        expect![[r#"

"#]],
        2,
    )
}

#[test]
fn local_tys() {
    check_raw(
        r#"
            main :: () -> i32 {
                int :: i32;
                imaginary :: distinct int;
                imaginary_vec3 :: distinct [3] imaginary;
                complex :: struct {
                    real_part: int,
                    imaginary_part: imaginary,
                };

                my_complex := complex.{
                    real_part = 5,
                    imaginary_part = 42,
                };

                do_math :: (c: complex) -> imaginary_vec3 {
                    // this is kind of akward because while we can access locals
                    // in the parameters and return type, we can't access `imaginary`
                    // from inside the body of this lambda
                    // this could be alleviated by adding a `type_of` builtin
                    i32.[1, c.real_part * i32.(c.imaginary_part), 3]
                };

                i32.(do_math(my_complex)[1])
            }
        "#,
        "main",
        false,
        expect![[r#"

"#]],
        5 * 42,
    )
}

#[test]
fn logical_booleans() {
    check_raw(
        r#"
            a :: (x: bool) -> bool {
                if x {
                    puts("a: true");
                } else {
                    puts("a: false");
                }
                x
            }

            b :: (x: bool) -> bool {
                if x {
                    puts("b: true");
                } else {
                    puts("b: false");
                }
                x
            }

            main :: () {
                puts("logical AND:\n");

                print_bool(a(true) && b(true));
                print_bool(a(true) && b(false));
                print_bool(a(false) && b(true));
                print_bool(a(false) && b(false));

                puts("logical OR:\n");

                print_bool(a(true) || b(true));
                print_bool(a(true) || b(false));
                print_bool(a(false) || b(true));
                print_bool(a(false) || b(false));
            }

            print_bool :: (b: bool) {
                if b {
                    puts("true\n");
                } else {
                    puts("false\n");
                }
            }

            puts :: (s: str) extern;
        "#,
        "main",
        false,
        expect![[r#"
            logical AND:

            a: true
            b: true
            true

            a: true
            b: false
            false

            a: false
            false

            a: false
            false

            logical OR:

            a: true
            true

            a: true
            true

            a: false
            b: true
            true

            a: false
            b: false
            false


        "#]],
        0,
    )
}

#[test]
fn bitwise_booleans() {
    check_raw(
        r#"
            a :: (x: bool) -> bool {
                if x {
                    puts("a: true");
                } else {
                    puts("a: false");
                }
                x
            }

            b :: (x: bool) -> bool {
                if x {
                    puts("b: true");
                } else {
                    puts("b: false");
                }
                x
            }

            main :: () {
                puts("bitwise AND:\n");

                print_bool(a(true) & b(true));
                print_bool(a(true) & b(false));
                print_bool(a(false) & b(true));
                print_bool(a(false) & b(false));

                puts("bitwise OR:\n");

                print_bool(a(true) | b(true));
                print_bool(a(true) | b(false));
                print_bool(a(false) | b(true));
                print_bool(a(false) | b(false));
            }

            print_bool :: (b: bool) {
                if b {
                    puts("true\n");
                } else {
                    puts("false\n");
                }
            }

            puts :: (s: str) extern;
        "#,
        "main",
        false,
        expect![[r#"
            bitwise AND:

            a: true
            b: true
            true

            a: true
            b: false
            false

            a: false
            b: true
            false

            a: false
            b: false
            false

            bitwise OR:

            a: true
            b: true
            true

            a: true
            b: false
            true

            a: false
            b: true
            true

            a: false
            b: false
            false


        "#]],
        0,
    )
}

#[test]
fn control_flow() {
    check_raw(
        r#"
            core :: #mod("core");

            fib :: (n: i32) -> i32 {
                if n <= 1 {
                    return n;
                }

                fib(n - 1) + fib(n - 2)
            }

            main :: () -> i32 {
                {
                    puts("before return");
                    return `ret_blk: {
                        puts("before break");
                        x := 5;
                        break loop {
                            res := fib(x);
                            if res > 1_000 {
                                core.println("fib(", x, ") = ", res);
                                break x;
                            }
                            x += 1;
                        };
                        puts("after break");
                        42
                    };
                    puts("after return");
                    1 + 1
                }

                puts("hello!");

                0
            }

            puts :: (s: str) -> i32 extern;
        "#,
        "main",
        true,
        expect![[r#"
            before return
            before break
            fib(17) = 1597

        "#]],
        17,
    )
}

#[test]
fn break_casting() {
    check_raw(
        r#"
            main :: () -> i64 {
                `blk: {
                    if true {
                        y : i8 = 5;
                        break `blk y;
                    }

                    y : i16 = 42;
                    y
                }
            }
        "#,
        "main",
        false,
        expect![[r#"

"#]],
        5,
    )
}

#[test]
fn bitwise_operators() {
    check_raw(
        r#"
            main :: () {
                print("~2147483647 =      ", ~u32.(4294967295));
                print(" 5032 &  25 =     ", 5032 & 32);
                print(" 5000 |  20 =   ", 5000 | 32);
                print(" 5032 ~  36 =   ", 5032 ~ 36);
                print(" 5032 &~ 36 =   ", 5032 &~ 36);
                print(" 5032 <<  2 =  ", 5032 << 2);
                print(" 5032 >>  2 =   ", 5032 >> 2);
                print("-5032 >>  2 =  ", -5032 >> 2);
            }

            print :: (s: str, n: i64) {
                s := ^[1000]char.(rawptr.(s));
                idx := 0;
                while idx < 100 {
                    ch := s[idx];
                    if ch == '\0' {
                        break;
                    }
                    putchar(ch);
                    idx += 1;
                }

                iprint(n);
                putchar('\n');
            }

            iprint :: (n: i64) {
                n := n;

                if n < 0 {
                    n = -n;
                    putchar('-');
                }

                if n > 9 {
                    a := n / 10;

                    n -= 10 * a;
                    iprint(a);
                }
                putchar(char.(u8.('0') + n));
            }

            putchar :: (ch: char) extern;
        "#,
        "main",
        false,
        expect![[r#"
            ~2147483647 =      0
             5032 &  25 =     32
             5000 |  20 =   5032
             5032 ~  36 =   5004
             5032 &~ 36 =   5000
             5032 <<  2 =  20128
             5032 >>  2 =   1258
            -5032 >>  2 =  -1258

        "#]],
        0,
    )
}

#[test]
fn early_return() {
    check_raw(
        r#"
            main :: () -> i16 {
                x := loop {
                    if true {
                        break 123;
                    }
                };

                // sometimes early return, sometimes not
                if true {
                    if true {
                        return x;
                    }
                } else {

                }

                // always early return
                {
                    {
                        if true {
                            return 5;
                        } else {
                            return 42;
                        }
                    }
                }

                0
            }
        "#,
        "main",
        false,
        expect![[r#"

"#]],
        123,
    )
}

#[test]
fn void_ptr() {
    check_raw(
        r#"
            main :: () -> i32 {
                // void variables are given a 0 sized stack allocation
                x := {};

                x := x;

                y := ^x;
                z := ^x;

                y_raw := ^usize.(rawptr.(^y))^;
                z_raw := ^usize.(rawptr.(^z))^;

                i32.(y_raw == z_raw)
            }
        "#,
        "main",
        false,
        expect![[r#"

"#]],
        1,
    )
}

#[test]
fn r#continue() {
    check_raw(
        r#"
            main :: () {
                i := 0;
                loop {
                    i += 1;

                    if i == 10 {
                        break;
                    }

                    if i % 2 == 0 {
                        continue;
                    }

                    printf("%i\n", i);
                }
            }

            printf :: (fmt: str, n: i32) extern;
        "#,
        "main",
        false,
        expect![[r#"
            1
            3
            5
            7
            9

        "#]],
        0,
    )
}

#[test]
fn defers() {
    check_raw(
        r#"
            main :: () -> i32 {
                defer printf(" How ye be?");
                {
                    defer printf(" Sailor!");
                    defer printf("ly");
                    {
                        defer printf(" World");
                        printf("Hello");
                        return 5;
                    }
                }
            }

            printf :: (text: str) extern;
        "#,
        "main",
        false,
        expect![[r#"
            Hello Worldly Sailor! How ye be?
        "#]],
        5,
    )
}

#[test]
fn defers_within_defers() {
    check_raw(
        r#"
            main :: () {
                defer printf("ly Sailor!");
                defer {
                    defer printf("World");
                    printf("Hello ");
                };
            }

            printf :: (text: str) extern;
        "#,
        "main",
        false,
        expect![[r#"
            Hello Worldly Sailor!
        "#]],
        0,
    )
}

#[test]
fn extern_fn_global() {
    check_raw(
        r#"
            main :: () {
                printf("Hello World!");
            }

            printf : (text: str) -> void : extern;
        "#,
        "main",
        false,
        expect![[r#"
            Hello World!
        "#]],
        0,
    )
}

#[test]
fn extern_fn_lambda() {
    check_raw(
        r#"
            main :: () {
                printf("Hello World!");
            }

            printf :: (text: str) extern;
        "#,
        "main",
        false,
        expect![[r#"
            Hello World!
        "#]],
        0,
    )
}

#[test]
fn comptime_globals_in_comptime_globals() {
    check_raw(
        r#"
            foo :: comptime {
                puts("comptime global in comptime global");
                42
            };

            func :: () -> i32 {
                foo
            }

            bar :: comptime func();

            main :: () -> i32 {
                baz :: comptime bar;

                baz;
                baz;

                baz
            }

            puts :: (text: str) extern;
        "#,
        "main",
        false,
        expect![[r#"

"#]],
        42,
    )
}

#[test]
fn globals_in_globals() {
    check_raw(
        r#"
            foo :: 123;
            bar :: foo;
            baz :: bar;

            main :: () -> i32 {
                baz
            }
        "#,
        "main",
        false,
        expect![[r#"

"#]],
        123,
    )
}

#[test]
fn global_referring_to_function() {
    check_raw(
        r#"
            add :: (a: i32, b: i32) -> i32 {
                a + b
            }

            foo :: add;

            main :: () -> i32 {
                add(1, 2)
            }
        "#,
        "main",
        false,
        expect![[r#"

"#]],
        3,
    )
}

#[test]
fn reorder_struct_literal_fields() {
    // there was a bug where simply changing the order of the fields
    // in the struct literal would also change the order of the struct.
    // e.g.
    // Under the bug, the following code would print this:
    // Foo {
    //   a = 4000000,
    //   b = 42,
    // }
    // Foo {
    //   a = 42,
    //   b = 4000000,
    // }
    // even though the following code always assigns 42 to b
    check_raw(
        r#"
            Foo :: struct {
                a: i64,
                b: i64,
            };

            main :: () {
                print_foo(Foo.{
                    a = 4_000_000,
                    b = 42,
                });

                print_foo(Foo.{
                    b = 42,
                    a = 4_000_000,
                });
            }

            print_foo :: (f: Foo) {
                print("Foo {\n  a = ");
                iprint(f.a);
                print(",\n  b = ");
                iprint(f.b);
                print(",\n}\n");
            }

            print :: (text: str) {
                text := [50]char.(text);

                i := 0;
                loop {
                    ch := text[i];
                    if ch == '\0' {
                        break;
                    }

                    putchar(ch);

                    i += 1;
                }
            }

            iprint :: (n: i64) {
                n := n;

                if n < 0 {
                    n = -n;
                    putchar('-');
                }

                if n > 9 {
                    a := n / 10;

                    n -= 10 * a;
                    iprint(a);
                }
                putchar(char.(u8.('0') + n));
            }

            puts :: (text: str) extern;
            putchar :: (ch: char) extern;
        "#,
        "main",
        false,
        expect![[r#"
        Foo {
          a = 4000000,
          b = 42,
        }
        Foo {
          a = 4000000,
          b = 42,
        }

"#]],
        0,
    )
}

#[test]
fn comptime_array_size() {
    check_raw(
        r#"
            Type :: comptime {
                x := 42;

                if x > 10 {
                    i8
                } else {
                    bool
                }
            };

            Size : usize : comptime {
                usize.((12.0 * (3.0 / 2.0) - 6.0) / 2.0)
            };

            main :: () -> i8 {
                x : [Size] Type = Type.[1, 3, 5, 7, 9, 11];

                x[5]
            }
        "#,
        "main",
        false,
        expect![[r#"

"#]],
        11,
    )
}

#[test]
fn distinct_array_to_slice() {
    check_raw(
        r#"
            RGB :: distinct [3] u8;

            main :: () -> u8 {
                red : RGB = u8.[150, 98, 123];

                components := []u8.(red);

                components[1]
            }
        "#,
        "main",
        false,
        expect![[r#"

"#]],
        98,
    )
}

#[test]
fn assign_to_cast() {
    check_raw(
        r#"
            main :: () -> u32 {
                x : u32 = 42;

                ptr := mut rawptr.(^mut x);

                ^mut u32.(ptr) ^= 5;

                x
            }
        "#,
        "main",
        false,
        expect![[r#"

"#]],
        5,
    )
}

#[test]
fn assign_to_param() {
    check_raw(
        r#"
            main :: () -> u32 {
                x : u32 = 42;

                do_stuff(^mut x);

                x
            }

            do_stuff :: (ptr: ^mut u32) {
                ptr ^= 5;
            }
        "#,
        "main",
        false,
        expect![[r#"

"#]],
        5,
    )
}

#[test]
fn hex_and_bin() {
    check_raw(
        r#"
            main :: () {
                iprint(0x1FeeeF001239 + 0b111101010101010);
            }

            iprint :: (n: i64) {
                n := n;

                if n < 0 {
                    n = -n;
                    putchar('-');
                }

                if n > 9 {
                    a := n / 10;

                    n -= 10 * a;
                    iprint(a);
                }
                putchar(char.(u8.('0') + n));
            }

            putchar :: (ch: char) extern;
        "#,
        "main",
        false,
        expect![[r#"
        35111072468195
"#]],
        0,
    )
}

#[test]
fn default_values() {
    check_raw(
        r#"
            core :: #mod("core");

            Foo :: distinct distinct struct {
                a: [2][4]u8,
                b: i16,
                c: distinct f32,
                d: bool,
                e: char,
                f: void,
            };

            main :: () {
                x: Foo;

                core.println(x);
            }
        "#,
        "main",
        true,
        expect![["
        { a = [ [ 0, 0, 0, 0 ], [ 0, 0, 0, 0 ] ], b = 0, c = 0.0, d = false, e = \0, f = () }

"]],
        0,
    )
}

#[test]
fn i128_literals() {
    check_raw(
        r#"
            core :: #mod("core");

            main :: () {
                x: i128 = 1_234;

                core.println(x);
            }
        "#,
        "main",
        true,
        expect![["
        1234

"]],
        0,
    )
}

#[test]
fn anon_struct_reorder_fields() {
    check_raw(
        r#"
            core :: #mod("core");

            Foo :: struct {
                a: u128,
                b: str,
                c: f64,
            };

            main :: () {
                x: Foo = .{
                    c = 1.0,
                    a = 42,
                    b = "haiiii >///<",
                };

                core.println(x);
            }
        "#,
        "main",
        true,
        expect![["
        { a = 42, b = haiiii >///<, c = 1.000 }

"]],
        0,
    )
}

#[test]
fn advanced_struct_cast() {
    check_raw(
        r#"
            core :: #mod("core");

            Foo :: struct {
                a: i32,
                b: f64,
                c: char,
                d: u128,
            };

            Bar :: struct {
                c: u8,
                d: f64,
                b: f32,
                a: i16,
            };

            main :: () {
                my_foo : Foo = Foo.{
                    a = 5,
                    b = 42.0,
                    c = 'a',
                    d = 256,
                };

                core.println(my_foo);

                my_bar : Bar = Bar.(my_foo);

                core.println(my_bar);
            };
        "#,
        "main",
        true,
        expect![["
        { a = 5, b = 42.000, c = a, d = 256 }
        { c = 97, d = 256.000, b = 42.000, a = 5 }

"]],
        0,
    )
}

#[test]
fn advanced_array_cast() {
    check_raw(
        r#"
            core :: #mod("core");

            main :: () {
                list : [3]u32 = .[1, 2, 3];

                core.println(core.type_of(list), " : ", list);

                list := [3]f64.(list);

                core.println(core.type_of(list), " : ", list);
            };
        "#,
        "main",
        true,
        expect![["
        [3] u32 : [ 1, 2, 3 ]
        [3] f64 : [ 1.000, 2.000, 3.000 ]

"]],
        0,
    )
}

#[test]
fn advanced_array_of_structs_cast() {
    check_raw(
        r#"
            core :: #mod("core");

            Foo :: struct {
                a: i32,
                b: f64,
                c: char,
                d: u128,
            };

            Bar :: struct {
                c: u8,
                d: f64,
                b: f32,
                a: i16,
            };

            main :: () {
                my_foo : Foo = Foo.{
                    a = 5,
                    b = 42.0,
                    c = 'a',
                    d = 256,
                };

                foo_list := .[my_foo, my_foo, my_foo];

                core.println(foo_list);

                bar_list := [3]Bar.(foo_list);

                core.println(bar_list);
            };
        "#,
        "main",
        true,
        expect![["
        [ { a = 5, b = 42.000, c = a, d = 256 }, { a = 5, b = 42.000, c = a, d = 256 }, { a = 5, b = 42.000, c = a, d = 256 } ]
        [ { c = 97, d = 256.000, b = 42.000, a = 5 }, { c = 97, d = 256.000, b = 42.000, a = 5 }, { c = 97, d = 256.000, b = 42.000, a = 5 } ]

"]],
        0,
    )
}

#[test]
fn commandline_args() {
    check_raw_with_args(
        r#"
            core :: #mod("core");

            main :: () {
                idx := 0;
                while idx < core.args.len {
                    core.println("arg(", idx, ") = ", core.args[idx]);

                    idx += 1;
                }
            }
        "#,
        "main",
        true,
        &["hello", "world!", "wow look at this arg", "foo=bar"],
        if cfg!(windows) {
            expect![["
            arg(0) = test-temp\\e0b12a0.exe
            arg(1) = hello
            arg(2) = world!
            arg(3) = wow look at this arg
            arg(4) = foo=bar

"]]
        } else {
            expect![["
            arg(0) = test-temp/e0b12a0
            arg(1) = hello
            arg(2) = world!
            arg(3) = wow look at this arg
            arg(4) = foo=bar

"]]
        },
        0,
    )
}

#[test]
fn enum_variants() {
    check_raw_with_args(
        r#"
            core :: #mod("core");

            Message :: enum {
                Quit,
                Move: struct { x: i32, y: i32 } | 5,
                Write: str,
                Change_Color: struct { r: i32, g: i32, b: i32 },
            };

            main :: () {
                msg_1 := Message.Quit.(());
                msg_2 := Message.Move.{
                    x = 25,
                    y = 100,
                };
                msg_3 := Message.Write.("the dark fire shall not avail you, flame of udun!");
                msg_4 := Message.Change_Color.{
                    r = 39,
                    g = 58,
                    b = 93,
                };

                core.println(msg_1);
                core.println(msg_2);
                core.println(msg_3);
                core.println(msg_4);

                // to make sure variant structs can be accessed like normal
                core.println(msg_4.r + msg_2.y + msg_4.b);
            }
        "#,
        "main",
        true,
        &[],
        expect![["
            ()
            { x = 25, y = 100 }
            the dark fire shall not avail you, flame of udun!
            { r = 39, g = 58, b = 93 }
            232

"]],
        0,
    )
}

#[test]
fn cast_variant_to_enum() {
    check_raw_with_args(
        r#"
            Animal :: enum {
                Dog: str,
                Fish: i32, // maybe this is the fish's age or something
            };

            main :: () {
                my_dog := Animal.Dog.("George");
                my_fish := Animal.Fish.(1000);

                animal_1 : Animal = my_dog;
                animal_2 : Animal = my_fish;
            }
        "#,
        "main",
        true,
        &[],
        expect![["

"]],
        0,
    )
}

#[test]
fn enums_and_switch_statements() {
    check_files(
        "../../examples/enums_and_switch_statements.capy",
        &[],
        "main",
        expect![[r#"
            [200] dog: George
            [100] cat!
            [300] it was a fish (age = 1000)
            [400] cow!!!
            [500] chicken >>>
            [700] sheep: Prof. Bahh, wool: 1.000, fullness: 0.500
            [600] oink oink

        "#]],
        0,
    )
}

#[test]
fn if_autocast_variant_to_enum_with_casting() {
    check_raw_with_args(
        r#"
            core :: #mod("core");

            Animal :: enum {
                Dog,
                Fish: i32,
                Cat,
            };

            main :: () {
                animal := if false {
                    Animal.Fish.(42)
                } else if true {
                    Animal.Dog.()
                } else {
                    Animal.Cat.()
                };

                core.println(animal);
            }
        "#,
        "main",
        true,
        &[],
        expect![["
        ()

"]],
        0,
    )
}

#[test]
fn if_autocast_variant_to_enum_with_singletons() {
    check_raw_with_args(
        r#"
            core :: #mod("core");

            Animal :: enum {
                Dog,
                Fish: i32,
                Cat,
            };

            main :: () {
                animal := if false {
                    Animal.Fish.(42)
                } else if true {
                    Animal.Dog
                } else {
                    Animal.Cat
                };

                core.println(animal);
            }
        "#,
        "main",
        true,
        &[],
        expect![["
        ()

"]],
        0,
    )
}

#[test]
fn switch_autocast_variant_to_enum_with_casting() {
    check_raw_with_args(
        r#"
            core :: #mod("core");

            State :: enum {
                A,
                B,
                C,
                D,
            };

            Animal :: enum {
                Dog,
                Fish: i32,
                Cat,
            };

            main :: () {
                animal := switch s in State.(State.C.()) {
                    State.A => Animal.Dog.(),
                    State.B => Animal.Fish.(42),
                    State.C => Animal.Cat.(),
                    State.D => Animal.Dog.()
                };

                core.println(#is_variant(animal, Animal.Cat));
            }
        "#,
        "main",
        true,
        &[],
        expect![["
        true

"]],
        0,
    )
}

#[test]
fn switch_autocast_variant_to_enum_with_singletons() {
    check_raw_with_args(
        r#"
            core :: #mod("core");

            State :: enum {
                A,
                B,
                C,
                D,
            };

            Animal :: enum {
                Dog,
                Fish: i32,
                Cat,
            };

            main :: () {
                animal := switch s in State.(State.C) {
                    .A => Animal.Dog,
                    .B => Animal.Fish.(42),
                    .C => Animal.Cat,
                    .D => Animal.Dog
                };

                core.println(animal);
            }
        "#,
        "main",
        true,
        &[],
        expect![["
        ()

"]],
        0,
    )
}

#[test]
fn autocast_array_to_slice() {
    check_raw_with_args(
        r#"
            core :: #mod("core");

            main :: () {
                foo := .[1, 2, 3];

                bar : []u128 = foo;

                core.println(bar);
            }
        "#,
        "main",
        true,
        &[],
        expect![["
        [ 1, 2, 3 ]

"]],
        0,
    )
}

#[test]
fn float_to_bits() {
    check_raw_with_args(
        r#"
            core :: #mod("core");
            fmt :: core.fmt;

            main :: () {
                bits : u32 = core.mem.f32_to_bits(42.5);
                core.println(fmt.binary(bits));
                core.println(core.mem.f32_from_bits(bits));

                bits : u64 = core.mem.f64_to_bits(42.5);
                core.println(fmt.binary_unsigned(bits));
                core.println(core.mem.f64_from_bits(bits));
            }
        "#,
        "main",
        true,
        &[],
        expect![["
        1000010001010100000000000000000
        42.500
        100000001000101010000000000000000000000000000000000000000000000
        42.500

"]],
        0,
    )
}

#[test]
fn unwrap_directive() {
    check_raw_with_args(
        r#"
            core :: #mod("core");

            Web_Event :: enum {
                Page_Load,
                Page_Unload,
                Key_Press: char,
                Paste: str,
                Click: struct {
                    x: i64,
                    y: i64,
                },
            };

            main :: () {
                clicked : Web_Event = Web_Event.Click.{
                    x = 20,
                    y = 80
                };

                unwrapped : Web_Event.Click = #unwrap(clicked, Web_Event.Click);

                core.assert(core.type_of(unwrapped) == Web_Event.Click);
                core.println(unwrapped);
            }
        "#,
        "main",
        true,
        &[],
        expect![["
        { x = 20, y = 80 }

"]],
        0,
    )
}

#[test]
fn quick_assign_ret() {
    check_raw_with_args(
        r#"
            main :: () -> u64 {
                foo := 5;

                foo += 25; // foo = 30
                foo *= 2;  // foo = 60
                foo -= 4;  // foo = 56
                foo /= 2;  // foo = 28

                foo
            }
        "#,
        "main",
        false,
        &[],
        expect![["

"]],
        28,
    )
}

#[test]
fn quick_assign_print() {
    check_raw_with_args(
        r#"
            core :: #mod("core");

            main :: () {
                foo : i64 = 5;

                foo += 25;      // foo = 30
                foo *= 2;       // foo = 60
                foo -= u8.(4);  // foo = 56
                foo /= 2;       // foo = 28

                core.println(foo);
            }
        "#,
        "main",
        true,
        &[],
        expect![["
        28

"]],
        0,
    )
}

#[test]
fn complex_comparison() {
    check_raw_with_args(
        r#"
            core :: #mod("core");

            main :: () {
                // strings
                core.println("" == "", " ", "" != ""); // true false
                core.println("a" == "a", " ", "a" != "a"); // true false
                core.println("abc" == "abc", " ", "abc" != "abc"); // true false
                core.println("Hello, world!" == "Hello, world!", " ", "Hello, world!" != "Hello, world!"); // true false
                core.println("abc" == "abcd", " ", "abc" != "abcd"); // false true
                core.println("abc" == "aBc", " ", "abc" != "aBc"); // false true
                core.println();

                // arrays
                core.println(.[] == .[], " ", .[] != .[]); // true false
                core.println(.[1, 2, 3] == .[1, 2, 3], " ", .[1, 2, 3] != .[1, 2, 3]); // true false
                core.println(.[1, 2, 3, 4] == .[1, 2, 42, 4], " ", .[1, 2, 3, 4] != .[1, 2, 42, 4]); // false true
                core.println(.[1, 2, 3, 4] == .[1, 2, 3, 5], " ", .[1, 2, 3, 4] != .[1, 2, 3, 5]); // false true
                core.println(.[1, 2, 3, 4] == .[2, 2, 3, 4], " ", .[1, 2, 3, 4] != .[2, 2, 3, 4]); // false true
                core.println(.[1, 2, 3, 4] == .[5, 6, 7, 8], " ", .[1, 2, 3, 4] != .[5, 6, 7, 8]); // false true
                core.println();

                // slices
                core.println([]void.(.[]) == []void.(.[]), " ", []void.(.[]) != []void.(.[])); // true false
                core.println([]u64.(.[1, 2, 3]) == []u64.(.[1, 2, 3]), " ", []u64.(.[1, 2, 3]) != []u64.(.[1, 2, 3])); // true false
                core.println([]u64.(.[1, 2, 3, 4]) == []u64.(.[1, 2, 42, 4]), " ", []u64.(.[1, 2, 3, 4]) != []u64.(.[1, 2, 42, 4])); // false true
                core.println([]u64.(.[1, 2, 3, 4]) == []u64.(.[1, 2, 3, 5]), " ", []u64.(.[1, 2, 3, 4]) != []u64.(.[1, 2, 3, 5])); // false true
                core.println([]u64.(.[1, 2, 3, 4]) == []u64.(.[5, 6, 7, 8]), " ", []u64.(.[1, 2, 3, 4]) != []u64.(.[5, 6, 7, 8])); // false tru
                core.println();

                // pointers
                core.println(^() == ^(), " ", ^() != ^()); // true false
                core.println(^42 == ^42, " ", ^42 != ^42); // true false
                core.println(^42 == ^32, " ", ^42 != ^32); // false true
                core.println();

                // structs
                Foo :: struct { temp: f64, cond: bool, age: usize };
                core.println(Foo.{temp=2.4,cond=false,age=5} == Foo.{temp=2.4,cond=false,age=5}, " ", Foo.{temp=2.4,cond=false,age=5} != Foo.{temp=2.4,cond=false,age=5}); // true false
                core.println(Foo.{temp=2.4,cond=false,age=5} == Foo.{temp=2.5,cond=false,age=5}, " ", Foo.{temp=2.4,cond=false,age=5} != Foo.{temp=2.5,cond=false,age=5}); // false true
                core.println(Foo.{temp=2.4,cond=false,age=5} == Foo.{temp=2.4,cond=true,age=5}, " ", Foo.{temp=2.4,cond=false,age=5} != Foo.{temp=2.4,cond=true,age=5}); // false true
                core.println(Foo.{temp=2.4,cond=false,age=5} == Foo.{temp=2.4,cond=false,age=10}, " ", Foo.{temp=2.4,cond=false,age=5} != Foo.{temp=2.4,cond=false,age=10}); // false true
                core.println();

                // enums
                Bar :: enum { Number: i64, Condition: bool };
                core.println(Bar.(Bar.Number.(42)) == Bar.(Bar.Number.(42)), " ", Bar.(Bar.Number.(42)) != Bar.(Bar.Number.(42))); // true false
                core.println(Bar.(Bar.Number.(42)) == Bar.(Bar.Number.(10)), " ", Bar.(Bar.Number.(42)) != Bar.(Bar.Number.(10))); // false true
                core.println(Bar.(Bar.Number.(42)) == Bar.(Bar.Condition.(true)), " ", Bar.(Bar.Number.(42)) != Bar.(Bar.Condition.(true))); // false true
                core.println(Bar.(Bar.Condition.(false)) == Bar.(Bar.Condition.(true)), " ", Bar.(Bar.Condition.(false)) != Bar.(Bar.Condition.(true))); // false true
                core.println(Bar.(Bar.Condition.(false)) == Bar.(Bar.Condition.(false)), " ", Bar.(Bar.Condition.(false)) != Bar.(Bar.Condition.(false))); // true false
                core.println();

                // options
                core.println(?u64.(42) == ?u64.(42), " ", ?u64.(42) != ?u64.(42)); // true false
                core.println(?u64.(42) == ?u64.(10), " ", ?u64.(42) != ?u64.(10)); // false true
                core.println(?u64.(42) == ?u64.(nil), " ", ?u64.(42) != ?u64.(nil)); // false true
                core.println(?u64.(nil) == ?u64.(nil), " ", ?u64.(nil) != ?u64.(nil)); // true false
            }
        "#,
        "main",
        true,
        &[],
        expect![["
        true false
        true false
        true false
        true false
        false true
        false true

        true false
        true false
        false true
        false true
        false true
        false true

        true false
        true false
        false true
        false true
        false true

        true false
        true false
        false true

        true false
        false true
        false true
        false true

        true false
        false true
        false true
        false true
        true false

        true false
        false true
        false true
        true false

"]],
        0,
    )
}

#[test]
fn varargs() {
    check_files(
        "../../examples/varargs.capy",
        &[],
        "main",
        expect![[r#"
        hello, world
        [ 1, 2, 3, 4, 5, 6, 7, 10 ]
        true
        [ hello, hi, what's up ]
        hello = 5, world = true

        "#]],
        0,
    )
}

#[test]
fn number_formatting() {
    // just another form of the above test
    check_raw_with_args(
        r#"
            core :: #mod("core");

            main :: () {
               print_base("octal", 8);
               print_base("decimal", 10);
               print_base("hex", 16);
               print_base("base 36", 36);
               print_base("base 62", 62);
            }

            print_base :: (name: str, base: u64) {
                core.println(name, ":");
                idx := 0;
                while idx <= base*2 {
                    core.println(core.fmt.Number_Formatting.{ number = i64.(idx), base = base, signed = false });
                    idx += 1;
                }
            }
        "#,
        "main",
        true,
        &[],
        expect![["
        octal:
        0
        1
        2
        3
        4
        5
        6
        7
        10
        11
        12
        13
        14
        15
        16
        17
        20
        decimal:
        0
        1
        2
        3
        4
        5
        6
        7
        8
        9
        10
        11
        12
        13
        14
        15
        16
        17
        18
        19
        20
        hex:
        0
        1
        2
        3
        4
        5
        6
        7
        8
        9
        a
        b
        c
        d
        e
        f
        10
        11
        12
        13
        14
        15
        16
        17
        18
        19
        1a
        1b
        1c
        1d
        1e
        1f
        20
        base 36:
        0
        1
        2
        3
        4
        5
        6
        7
        8
        9
        a
        b
        c
        d
        e
        f
        g
        h
        i
        j
        k
        l
        m
        n
        o
        p
        q
        r
        s
        t
        u
        v
        w
        x
        y
        z
        10
        11
        12
        13
        14
        15
        16
        17
        18
        19
        1a
        1b
        1c
        1d
        1e
        1f
        1g
        1h
        1i
        1j
        1k
        1l
        1m
        1n
        1o
        1p
        1q
        1r
        1s
        1t
        1u
        1v
        1w
        1x
        1y
        1z
        20
        base 62:
        0
        1
        2
        3
        4
        5
        6
        7
        8
        9
        a
        b
        c
        d
        e
        f
        g
        h
        i
        j
        k
        l
        m
        n
        o
        p
        q
        r
        s
        t
        u
        v
        w
        x
        y
        z
        A
        B
        C
        D
        E
        F
        G
        H
        I
        J
        K
        L
        M
        N
        O
        P
        Q
        R
        S
        T
        U
        V
        W
        X
        Y
        Z
        10
        11
        12
        13
        14
        15
        16
        17
        18
        19
        1a
        1b
        1c
        1d
        1e
        1f
        1g
        1h
        1i
        1j
        1k
        1l
        1m
        1n
        1o
        1p
        1q
        1r
        1s
        1t
        1u
        1v
        1w
        1x
        1y
        1z
        1A
        1B
        1C
        1D
        1E
        1F
        1G
        1H
        1I
        1J
        1K
        1L
        1M
        1N
        1O
        1P
        1Q
        1R
        1S
        1T
        1U
        1V
        1W
        1X
        1Y
        1Z
        20

"]],
        0,
    )
}

#[test]
fn try_to_void_option() {
    check_raw_with_args(
        r#"
            core :: #mod("core");

            foo :: () -> ?void {
                ?void.(nil).try;

                ()
            };

            main :: () {
                core.println(foo());
            }
        "#,
        "main",
        true,
        &[],
        expect![["
        nil

"]],
        0,
    )
}

#[test]
fn try_to_void_option_always_nil() {
    // although the function is marked as `-> ?void`, the internal body block is actually
    // always of type `nil`.
    //
    // this essentially checks the breaking code of try to make sure it won't try to
    // instantiate a nil if it doesn't need to
    check_raw_with_args(
        r#"
            core :: #mod("core");

            foo :: () -> ?void {
                ?void.(nil).try;

                nil
            };

            main :: () {
                core.println(foo());
            }
        "#,
        "main",
        true,
        &[],
        expect![["
        nil

"]],
        0,
    )
}

#[test]
fn try_to_nil() {
    // just another form of the above test
    check_raw_with_args(
        r#"
            core :: #mod("core");

            foo :: () -> nil {
                ?void.(nil).try;

                nil
            };

            main :: () {
                core.println(foo());
            }
        "#,
        "main",
        true,
        &[],
        expect![["
        nil

"]],
        0,
    )
}

#[test]
fn try_to_void_option_complex() {
    // this bug was SO FUCKING HARD TO NARROW DOWN OMFGGGGG
    check_raw_with_args(
        r#"
            core :: #mod("core");

            main :: () {
                do_stuff_on_stack();

                {
                    vals := .[make_void(), make_nil(), make_void(), make_nil()];

                    // if the bug is there you'll see a0 in memory instead of 0
                    // core.mem.print_mem(^vals, core.meta.size_of(core.type_of(vals)));

                    idx := 0;
                    while idx < vals.len {
                        val := vals[idx];

                        eq := val == nil;
                        ne := val != nil;

                        // core.println(val, " ", eq, " ", ne); // false true
                        // core.println(" ", eq, " ", ne); // false true
                        core.libc.puts(if eq { "true" } else { "false" });

                        idx += 1;
                    }
                }
            }

            make_void :: () -> ?void {
                ?u64.(42).try;
            }

            make_nil :: () -> ?void {
                ?u64.(nil).try;
            }

            do_stuff_on_stack :: () {
                arr: [100]u8;

                idx := 0;
                while idx < arr.len {
                    arr[idx] = 0xa0;
                    idx += 1;
                }
            }
        "#,
        "main",
        true,
        &[],
        expect![["
        false
        true
        false
        true

"]],
        0,
    )
}

#[test]
fn slightly_complex_optional_funcs_and_compares() {
    check_raw_with_args(
        r#"
            core :: #mod("core");

            foo :: (n: i64) -> ?i64 {
                if n % 2 == 0 {
                    n
                } else {
                    nil
                }
            }

            bar :: (n: i64) -> ?str {
                num : i64 = foo(n).try;

                if n <= 5 {
                    "hello"
                } else {
                    "world"
                }
            }

            baz :: (n: i64) -> ?void {
                name := bar(n).try;

                core.println(name);
            }

            main :: () {
                idx := 0;
                while idx <= 10 {
                    if baz(idx) == nil {
                        core.println("...");
                    }
                    idx += 1;
                }
            }
        "#,
        "main",
        true,
        &[],
        expect![["
        hello
        ...
        hello
        ...
        hello
        ...
        world
        ...
        world
        ...
        world

"]],
        0,
    )
}

#[test]
fn error_union_if_error_str() {
    check_raw_with_args(
        r#"
            core :: #mod("core");

            main :: () {
                idx := 0;
                while idx < 10 {
                    result := do_lots_of_work(idx);
                    core.println(idx, " : ", result);
                    idx += 1;
                }
            }

            do_lots_of_work :: (task_num: u32) -> str!u64 {
                work := do_work(task_num).try;

                work * 2
            }

            do_work :: (task_num: u32) -> str!u64 {
                if task_num == 3 {
                    return "task 3 is not supported!";
                }

                foo(task_num == 0 || task_num % 8 != 0).try;

                return task_num * 2;
            }

            foo :: (cond: bool) -> str!void {
                if !cond {
                    return "foo failed :(";
                }
            }
        "#,
        "main",
        true,
        &[],
        expect![["
        0 : 0
        1 : 4
        2 : 8
        3 : task 3 is not supported!
        4 : 16
        5 : 20
        6 : 24
        7 : 28
        8 : foo failed :(
        9 : 36

"]],
        0,
    )
}

#[test]
fn error_union_if_error_struct() {
    check_raw_with_args(
        r#"
            core :: #mod("core");

            Error_Kind :: enum {
                Not_Supported: struct {
                    task: u64
                },
                Foo_Failed,
            };

            print_error_kind :: (kind: Error_Kind) {
                switch k in kind {
                    .Not_Supported => core.print("task #", k.task, " is not supported"),
                    .Foo_Failed => core.print("foo failed :("),
                }
            }

            Error :: struct {
                why: Error_Kind,
                timestamp: str,
            };

            main :: () {
                idx := 0;
                while idx < 10 {
                    result := do_lots_of_work(idx);

                    if #is_variant(result, u64) {
                        num := #unwrap(result, u64);

                        core.println(idx, " : ", num);
                    } else if #is_variant(result, Error) {
                        err := #unwrap(result, Error);

                        core.println("THERE WAS AN ERROR WHILE TRYING TO RUN TASK #", idx, ":");
                        core.print("why = ");
                        print_error_kind(err.why);
                        core.println("\ntimestamp = ", err.timestamp);
                    }

                    idx += 1;
                }
            }

            do_lots_of_work :: (task_num: u32) -> Error!u64 {
                work := do_work(task_num).try;

                work * 2
            }

            do_work :: (task_num: u32) -> Error!u64 {
                if task_num == 3 {
                    return .{
                        why = Error_Kind.Not_Supported.{
                            task = task_num,
                        },
                        timestamp = "1955-11-05 6:15am"
                    };
                }

                foo(task_num == 0 || task_num % 8 != 0).try;

                return task_num * 2;
            }

            foo :: (cond: bool) -> Error!void {
                if !cond {
                    return .{
                        why = Error_Kind.Foo_Failed,
                        timestamp = "1955-11-12 10:04pm",
                    };
                }
            }
        "#,
        "main",
        true,
        &[],
        expect![["
        0 : 0
        1 : 4
        2 : 8
        THERE WAS AN ERROR WHILE TRYING TO RUN TASK #3:
        why = task #3 is not supported
        timestamp = 1955-11-05 6:15am
        4 : 16
        5 : 20
        6 : 24
        7 : 28
        THERE WAS AN ERROR WHILE TRYING TO RUN TASK #8:
        why = foo failed :(
        timestamp = 1955-11-12 10:04pm
        9 : 36

"]],
        0,
    )
}

#[test]
fn error_union_if_comparison() {
    check_raw_with_args(
        r#"
            core :: #mod("core");

            main :: () {
                idx := 0;
                while idx < 10 {
                    result := do_lots_of_work(idx);

                    if result == 20 {
                        core.println(idx, " : 20!!!!!!!");
                    } else if result == "foo failed :(" {
                        core.println(idx, " : the foo function failed :O");
                    } else if #is_variant(result, u64) {
                        num := #unwrap(result, u64);

                        core.println(idx, " : ", num);
                    } else if #is_variant(result, str) {
                        err := #unwrap(result, str);

                        core.println("THERE WAS AN ERROR WHILE TRYING TO RUN TASK #", idx, ":");
                        core.println("why = ", err);
                    }

                    idx += 1;
                }
            }

            do_lots_of_work :: (task_num: u32) -> str!u64 {
                work := do_work(task_num).try;

                work * 2
            }

            do_work :: (task_num: u32) -> str!u64 {
                if task_num == 3 {
                    return "task #3 is not supported";
                }

                foo(task_num == 0 || task_num % 8 != 0).try;

                return task_num * 2;
            }

            foo :: (cond: bool) -> str!void {
                if !cond {
                    return "foo failed :(";
                }
            }
        "#,
        "main",
        true,
        &[],
        expect![["
        0 : 0
        1 : 4
        2 : 8
        THERE WAS AN ERROR WHILE TRYING TO RUN TASK #3:
        why = task #3 is not supported
        4 : 16
        5 : 20!!!!!!!
        6 : 24
        7 : 28
        8 : the foo function failed :O
        9 : 36

"]],
        0,
    )
}

#[test]
fn error_union_printing() {
    // todo: make core.println print the type name of zero-sized types
    check_raw_with_args(
        r#"
        core :: #mod("core");

        Error_Kind :: enum {
            Not_Supported: struct {
                task: u64
            },
            Foo_Failed,
        };

        print_error_kind :: (kind: Error_Kind) {
            switch k in kind {
                Error_Kind.Not_Supported => core.print("task #", k.task, " is not supported"),
                Error_Kind.Foo_Failed => core.print("foo failed :("),
            }
        }

        Error :: struct {
            why: Error_Kind,
            timestamp: str,
        };

        main :: () {
            idx := 0;
            while idx < 10 {
                result := do_lots_of_work(idx);

                core.println(idx, " : ", result);

                idx += 1;
            }
        }

        do_lots_of_work :: (task_num: u64) -> Error!u64 {
            work := do_work(task_num).try;

            work * 2
        }

        do_work :: (task_number: u64) -> Error!u64 {
            if task_number == 3 {
                return .{
                    why = Error_Kind.Not_Supported.{
                        task = task_number,
                    },
                    timestamp = "1955-11-05 6:15am"
                };
            }

            foo(task_number == 0 || task_number % 8 != 0).try;

            return task_number * 2;
        }

        foo :: (cond: bool) -> Error!void {
            if !cond {
                return .{
                    why = Error_Kind.Foo_Failed,
                    timestamp = "1955-11-12 10:04pm",
                };
            }
        }
    "#,
        "main",
        true,
        &[],
        expect![["
        0 : 0
        1 : 4
        2 : 8
        3 : { why = { task = 3 }, timestamp = 1955-11-05 6:15am }
        4 : 16
        5 : 20
        6 : 24
        7 : 28
        8 : { why = (), timestamp = 1955-11-12 10:04pm }
        9 : 36

"]],
        0,
    )
}

#[test]
fn nullable_pointers() {
    check_raw_with_args(
        r#"
        malloc :: (size: usize) -> ?mut rawptr extern;
        free :: (ptr: ?mut rawptr) extern;
        puts :: (s: str) -> i32 extern;

        main :: () {
            mem := ?^mut i32.(malloc(4));

            if mem == nil {
                puts("nil");
            } else {
                puts("SUCCESS!");
            }

            free(mem);
        }
    "#,
        "main",
        true,
        &[],
        expect![["
        SUCCESS!

"]],
        0,
    )
}

#[test]
fn unwrap_optionals() {
    check_raw_with_args(
        r#"
            core :: #mod("core");

            main :: () {
                opts := ?u64.[42, nil];

                idx := 0;
                while idx < opts.len {
                    opt := opts[idx];

                    if #is_variant(opt, u64) {
                        inner := #unwrap(opt, u64);
                        core.println(inner);
                    } else if #is_variant(opt, nil) {
                        inner := #unwrap(opt, nil);
                        core.println(inner);
                    }

                    idx += 1;
                }
            }
        "#,
        "main",
        true,
        &[],
        expect![["
        42
        nil

"]],
        0,
    )
}

#[test]
fn unwrap_nullable_optionals() {
    check_raw_with_args(
        r#"
            core :: #mod("core");

            main :: () {
                x := 42;

                opts := ?^u64.[^x, nil];

                idx := 0;
                while idx < opts.len {
                    opt := opts[idx];

                    if #is_variant(opt, ^u64) {
                        inner := #unwrap(opt, ^u64);
                        core.println(inner);
                    } else if #is_variant(opt, nil) {
                        inner := #unwrap(opt, nil);
                        core.println(inner);
                    }

                    idx += 1;
                }
            }
        "#,
        "main",
        true,
        &[],
        expect![["
        ^42
        nil

"]],
        0,
    )
}

// the "ptrs_to_ptrs.capy" and "comptime_types.capy" tests are not reproducible

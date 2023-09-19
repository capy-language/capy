mod compiler;
mod compiler_defined;
mod convert;
mod mangle;

use compiler::comptime::ComptimeResult;
use compiler::program::compile_program;
use cranelift::prelude::isa::{self};
use cranelift::prelude::{settings, Configurable};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_object::object::write;
use cranelift_object::{ObjectBuilder, ObjectModule};

use interner::Interner;
use rustc_hash::FxHashMap;
use std::mem;
use std::path::PathBuf;
use std::process::{exit, Command};
use target_lexicon::Triple;

pub(crate) type CraneliftSignature = cranelift::prelude::Signature;
pub(crate) type CapyFnSignature = hir_ty::FunctionSignature;

pub use compiler::comptime::{eval_comptime_blocks, ComptimeToCompile};

pub fn compile_jit(
    verbose: bool,
    entry_point: hir::Fqn,
    project_root: &std::path::Path,
    interner: &Interner,
    bodies_map: &FxHashMap<hir::FileName, hir::Bodies>,
    tys: &hir_ty::InferenceResult,
    comptime_results: &FxHashMap<ComptimeToCompile, ComptimeResult>,
) -> fn(usize, usize) -> usize {
    let mut flag_builder = settings::builder();
    flag_builder.set("use_colocated_libcalls", "false").unwrap();
    flag_builder.set("is_pic", "false").unwrap();
    let isa_builder = cranelift_native::builder().unwrap_or_else(|msg| {
        panic!("host machine is not supported: {}", msg);
    });
    let isa = isa_builder
        .finish(settings::Flags::new(flag_builder))
        .unwrap();
    let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());

    let mut module = JITModule::new(builder);

    let cmain = compile_program(
        verbose,
        entry_point,
        project_root,
        interner,
        bodies_map,
        tys,
        &mut module,
        comptime_results,
    );

    // Finalize the functions which were defined, which resolves any
    // outstanding relocations (patching in addresses, now that they're
    // available).
    // This also prepares the code for JIT execution
    module.finalize_definitions().unwrap();

    let code_ptr = module.get_finalized_function(cmain);

    unsafe { mem::transmute::<_, fn(usize, usize) -> usize>(code_ptr) }
}

#[allow(clippy::too_many_arguments)]
pub fn compile_obj(
    verbose: bool,
    entry_point: hir::Fqn,
    project_root: &std::path::Path,
    interner: &Interner,
    bodies_map: &FxHashMap<hir::FileName, hir::Bodies>,
    tys: &hir_ty::InferenceResult,
    comptime_results: &FxHashMap<ComptimeToCompile, ComptimeResult>,
    target: Triple,
) -> Result<Vec<u8>, write::Error> {
    let mut flag_builder = settings::builder();
    // flag_builder.set("use_colocated_libcalls", "false").unwrap();
    flag_builder.set("is_pic", "true").unwrap();

    let isa_builder = isa::lookup(target).unwrap_or_else(|msg| {
        println!("invalid target: {}", msg);
        exit(1);
    });
    let isa = isa_builder
        .finish(settings::Flags::new(flag_builder))
        .unwrap();

    let builder = ObjectBuilder::new(
        isa,
        entry_point.module.to_string(project_root, interner),
        cranelift_module::default_libcall_names(),
    )
    .unwrap();
    let mut module = ObjectModule::new(builder);

    compile_program(
        verbose,
        entry_point,
        project_root,
        interner,
        bodies_map,
        tys,
        &mut module,
        comptime_results,
    );

    // Finalize the functions which were defined, which resolves any
    // outstanding relocations (patching in addresses, now that they're
    // available).
    // This also generates the proper .o
    let product = module.finish();

    product.emit()
}

pub fn link_to_exec(object_file: &PathBuf) -> PathBuf {
    let exe_path = object_file
        .parent()
        .unwrap()
        .join(object_file.file_stem().unwrap());
    let success = Command::new("gcc")
        .arg(object_file)
        .arg("-o")
        .arg(&exe_path)
        .status()
        .unwrap()
        .success();
    assert!(success);
    exe_path
}

#[cfg(test)]
mod tests {
    use core::panic;
    use std::{env, fs, path::Path};

    use ast::AstNode;
    use expect_test::{expect, Expect};
    use hir_ty::InferenceCtx;
    use la_arena::Arena;
    use path_clean::PathClean;
    use uid_gen::UIDGenerator;

    use super::*;

    fn check(
        main_file: &str,
        other_files: &[&str],
        entry_point: &str,
        stdout_expect: Expect,
        expected_status: i32,
    ) {
        let current_dir = env!("CARGO_MANIFEST_DIR");
        env::set_current_dir(current_dir).unwrap();

        let mut interner = Interner::default();
        let mut world_index = hir::WorldIndex::default();

        let mut uid_gen = UIDGenerator::default();
        let mut twr_arena = Arena::new();
        let mut bodies_map = FxHashMap::default();

        let mut comptimes = Vec::new();

        for file in other_files {
            let file = file.replace('/', std::path::MAIN_SEPARATOR_STR);
            let file_path = Path::new(current_dir).join(file).clean();
            let text = &fs::read_to_string(&file_path).unwrap();

            let tokens = lexer::lex(text);
            let parse = parser::parse_source_file(&tokens, text);
            assert_eq!(parse.errors(), &[]);

            let tree = parse.into_syntax_tree();
            let root = ast::Root::cast(tree.root(), &tree).unwrap();
            let (index, diagnostics) =
                hir::index(root, &tree, &mut uid_gen, &mut twr_arena, &mut interner);

            assert_eq!(diagnostics, vec![]);

            let module = hir::FileName(interner.intern(&file_path.to_string_lossy()));

            let (bodies, diagnostics) = hir::lower(
                root,
                &tree,
                &file_path,
                &index,
                &mut uid_gen,
                &mut twr_arena,
                &mut interner,
                false,
            );

            comptimes.extend(bodies.comptimes().map(|comptime| ComptimeToCompile {
                module_name: module,
                comptime,
            }));

            assert_eq!(diagnostics, vec![]);

            world_index.add_module(module, index);
            bodies_map.insert(module, bodies);
        }

        let main_file = main_file.replace('/', std::path::MAIN_SEPARATOR_STR);
        let main_file_path = Path::new(current_dir).join(main_file).clean();
        let text = &fs::read_to_string(&main_file_path).unwrap();
        let module = hir::FileName(interner.intern(&main_file_path.to_string_lossy()));
        let tokens = lexer::lex(text);
        let parse = parser::parse_source_file(&tokens, text);
        assert_eq!(parse.errors(), &[]);

        let tree = parse.into_syntax_tree();
        let root = ast::Root::cast(tree.root(), &tree).unwrap();
        let (index, diagnostics) =
            hir::index(root, &tree, &mut uid_gen, &mut twr_arena, &mut interner);

        assert_eq!(diagnostics, vec![]);

        let (bodies, diagnostics) = hir::lower(
            root,
            &tree,
            &main_file_path,
            &index,
            &mut uid_gen,
            &mut twr_arena,
            &mut interner,
            false,
        );
        comptimes.extend(bodies.comptimes().map(|comptime| ComptimeToCompile {
            module_name: module,
            comptime,
        }));
        assert_eq!(diagnostics, vec![]);
        world_index.add_module(module, index);
        bodies_map.insert(module, bodies);

        let (inference_result, diagnostics) =
            InferenceCtx::new(&bodies_map, &world_index, &twr_arena).finish();
        assert_eq!(diagnostics, vec![]);

        println!("comptime:");

        let comptime_results = eval_comptime_blocks(
            true,
            comptimes,
            Path::new(""),
            &interner,
            &bodies_map,
            &inference_result,
            Triple::host().pointer_width().unwrap().bits(),
        );

        println!("actual program:");

        let bytes = compile_obj(
            true,
            hir::Fqn {
                module,
                name: hir::Name(interner.intern(entry_point)),
            },
            Path::new(""),
            &interner,
            &bodies_map,
            &inference_result,
            &comptime_results,
            Triple::host(),
        )
        .unwrap();

        let output_folder = env::current_dir().unwrap().join("test-temp");

        let _ = fs::create_dir(&output_folder);

        let main_name = main_file_path.file_stem().unwrap().to_string_lossy();
        let file = output_folder.join(format!("{}.o", main_name));
        fs::write(&file, bytes.as_slice()).unwrap_or_else(|why| {
            panic!("{}: {why}", file.display());
        });

        let exec = link_to_exec(&file);

        let output = std::process::Command::new(exec.clone())
            .output()
            .unwrap_or_else(|_| panic!("{} did not run successfully", exec.display()));

        assert_eq!(output.status.code().unwrap(), expected_status);

        let stdout = std::str::from_utf8(&output.stdout)
            .unwrap()
            .replace('\r', "");
        let stdout = format!("{}\n", stdout);

        println!("{:?}", stdout);

        stdout_expect.assert_eq(&stdout);
    }

    #[test]
    fn hello_world() {
        check(
            "../../examples/hello_world.capy",
            &["../../examples/std/libc.capy"],
            "main",
            expect![[r#"
            Hello, World!

            "#]],
            0,
        )
    }

    #[test]
    fn vectors() {
        check(
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
        check(
            "../../examples/fib.capy",
            &["../../examples/io.capy"],
            "main",
            expect![[r#"
            Running Fibonacci(28) x 5 times...
            Ready... Go!
            Fibonacci number #28 = 317811

            "#]],
            0,
        )
    }

    #[test]
    fn entry_point() {
        check(
            "../../examples/entry_point.capy",
            &[],
            "_start",
            expect![[r#"
            _start
            Hello from Main!
            main() returned with: 0

            "#]],
            255,
        )
    }

    #[test]
    fn drink() {
        check(
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
        check(
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
    fn array_of_arrays() {
        check(
            "../../examples/arrays_of_arrays.capy",
            &["../../examples/std/libc.capy"],
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
    fn files() {
        check(
            "../../examples/files.capy",
            &["../../examples/std/libc.capy"],
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
        check(
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
        check(
            "../../examples/pretty.capy",
            &["../../examples/std/libc.capy"],
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
        check(
            "../../examples/float_to_string.capy",
            &[
                "../../examples/std/libc.capy",
                "../../examples/std/ptr.capy",
                "../../examples/std/math.capy",
            ],
            "main",
            expect![[r#"
            3.141

            ln 10 = 2.302
            ln 50 = 3.912
            ln 100 = 4.605
            ln 500 = 6.214
            log 10 = 1.000
            log 50 = 1.698
            log 100 = 2.000
            log 500 = 2.698

            "#]],
            0,
        )
    }

    #[test]
    fn first_class_functions() {
        check(
            "../../examples/first_class_functions.capy",
            &[],
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
        check(
            "../../examples/structs.capy",
            &["../../examples/std/libc.capy"],
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
        check(
            "../../examples/comptime.capy",
            &[
                "../../examples/std/libc.capy",
                "../../examples/std/math.capy",
            ],
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

    #[test]
    fn string() {
        check(
            "../../examples/string.capy",
            &[
                "../../examples/std/libc.capy",
                "../../examples/std/ptr.capy",
            ],
            "main",
            expect![[r#"
            Reallocating!
            cap: 2, len: 1
            cap: 2, len: 2
            Reallocating!
            cap: 4, len: 3
            cap: 4, len: 4
            Reallocating!
            cap: 8, len: 5
            cap: 8, len: 6
            Reallocating!
            cap: 16, len: 11
            cap: 16, len: 12
            cap: 16, len: 13
            Hello World!

            "#]],
            0,
        )
    }

    #[test]
    fn auto_deref() {
        check(
            "../../examples/auto_deref.capy",
            &["../../examples/std/libc.capy"],
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

    // the "ptrs_to_ptrs.capy" test is not reproducible
}

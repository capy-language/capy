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

pub use compiler::comptime::{eval_comptime_blocks, ComptimeToCompile};

pub fn compile_jit(
    verbose: bool,
    entry_point: hir::Fqn,
    mod_dir: &std::path::Path,
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
        mod_dir,
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
    mod_dir: &std::path::Path,
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
        entry_point.file.to_string(mod_dir, interner),
        cranelift_module::default_libcall_names(),
    )
    .unwrap();
    let mut module = ObjectModule::new(builder);

    compile_program(
        verbose,
        entry_point,
        mod_dir,
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

pub fn link_to_exec(object_file: &PathBuf, libs: Option<&[String]>) -> PathBuf {
    let exe_path = object_file
        .parent()
        .unwrap()
        .join(object_file.file_stem().unwrap());
    let success = if let Some(libs) = libs {
        Command::new("gcc")
            .arg(object_file)
            .arg("-o")
            .arg(&exe_path)
            .args(libs.iter().map(|lib| "-l".to_string() + lib))
            .status()
            .unwrap()
            .success()
    } else {
        Command::new("gcc")
            .arg(object_file)
            .arg("-o")
            .arg(&exe_path)
            .status()
            .unwrap()
            .success()
    };

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
    use path_clean::PathClean;
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
        let current_dir = env!("CARGO_MANIFEST_DIR");
        env::set_current_dir(current_dir).unwrap();

        let mut modules = FxHashMap::default();

        const CORE_DEPS: &[&str] = &[
            "../../core/mod.capy",
            "../../core/ptr.capy",
            "../../core/libc.capy",
            "../../core/math.capy",
        ];

        for file in other_files.iter().chain(CORE_DEPS.iter()) {
            let file = file.replace('/', std::path::MAIN_SEPARATOR_STR);
            let file = Path::new(current_dir).join(file).clean();
            let text = fs::read_to_string(&file).unwrap();

            modules.insert(file.to_string_lossy().to_string(), text);
        }

        let main_file = main_file.replace('/', std::path::MAIN_SEPARATOR_STR);
        let main_file = Path::new(current_dir).join(main_file).clean();
        let text = fs::read_to_string(&main_file).unwrap();
        modules.insert(main_file.to_string_lossy().to_string(), text);

        compile(
            modules
                .iter()
                .map(|(k, v)| (k.as_str(), v.as_str()))
                .collect(),
            &main_file.to_string_lossy(),
            entry_point,
            false,
            stdout_expect,
            expected_status,
        )
    }

    #[track_caller]
    fn check_raw(input: &str, entry_point: &str, stdout_expect: Expect, expected_status: i32) {
        let modules = test_utils::split_multi_module_test_data(input);

        compile(
            modules,
            "main.capy",
            entry_point,
            true,
            stdout_expect,
            expected_status,
        )
    }

    #[track_caller]
    fn compile(
        modules: FxHashMap<&str, &str>,
        main_file: &str,
        entry_point: &str,
        fake_file_system: bool,
        stdout_expect: Expect,
        expected_status: i32,
    ) {
        let mod_dir = env::current_dir().unwrap().join("../../").clean();

        let mut interner = Interner::default();
        let mut world_index = hir::WorldIndex::default();

        let mut uid_gen = UIDGenerator::default();
        let mut bodies_map = FxHashMap::default();

        let mut comptimes = Vec::new();

        for (file, text) in &modules {
            if *file == main_file {
                continue;
            }

            let tokens = lexer::lex(text);
            let parse = parser::parse_source_file(&tokens, text);
            assert_eq!(parse.errors(), &[]);

            let tree = parse.into_syntax_tree();
            let root = ast::Root::cast(tree.root(), &tree).unwrap();
            let (index, diagnostics) = hir::index(root, &tree, &mut interner);

            assert_eq!(diagnostics, vec![]);

            let module = hir::FileName(interner.intern(file));

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

            comptimes.extend(bodies.comptimes().map(|comptime| ComptimeToCompile {
                file_name: module,
                comptime,
            }));

            assert_eq!(diagnostics, vec![]);

            world_index.add_file(module, index);
            bodies_map.insert(module, bodies);
        }

        let text = &modules[main_file];
        let file = hir::FileName(interner.intern(main_file));
        let tokens = lexer::lex(text);
        let parse = parser::parse_source_file(&tokens, text);
        assert_eq!(parse.errors(), &[]);

        let tree = parse.into_syntax_tree();
        let root = ast::Root::cast(tree.root(), &tree).unwrap();
        let (index, diagnostics) = hir::index(root, &tree, &mut interner);

        assert_eq!(diagnostics, vec![]);

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
        comptimes.extend(bodies.comptimes().map(|comptime| ComptimeToCompile {
            file_name: file,
            comptime,
        }));
        assert_eq!(diagnostics, vec![]);
        world_index.add_file(file, index);
        bodies_map.insert(file, bodies);

        let entry_point = hir::Fqn {
            file,
            name: hir::Name(interner.intern(entry_point)),
        };

        let (inference_result, diagnostics) =
            InferenceCtx::new(&bodies_map, &world_index).finish(Some(entry_point));
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
            entry_point,
            if fake_file_system {
                Path::new("")
            } else {
                &mod_dir
            },
            &interner,
            &bodies_map,
            &inference_result,
            &comptime_results,
            Triple::host(),
        )
        .unwrap();

        let output_folder = env::current_dir().unwrap().join("test-temp");

        let _ = fs::create_dir(&output_folder);

        let caller = core::panic::Location::caller();
        let out_name = format!("test{}", caller.line());

        let file = output_folder.join(format!("{}.o", out_name));
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

        println!("stdout: {:?}", stdout);

        dbg!(&stdout_expect.data());
        println!("expected: {:?}", trim_indent(stdout_expect.data()));
        stdout_expect.assert_eq(&stdout);
    }

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
            Running Fibonacci(28) x 5 times...
            Ready... Go!
            Fibonacci number #28 = 317811

            "#]],
            0,
        )
    }

    #[test]
    fn entry_point() {
        check_files(
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
    fn array_of_arrays() {
        check_files(
            "../../examples/arrays_of_arrays.capy",
            &[],
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
        check_files(
            "../../examples/files.capy",
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
            log 100 = 2.000
            log 500 = 2.698

            "#]],
            0,
        )
    }

    #[test]
    fn first_class_functions() {
        check_files(
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
            &[],
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
        check_files(
            "../../examples/string.capy",
            &[],
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
        check_files(
            "../../examples/auto_deref.capy",
            &[],
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
    fn cast_f32_to_i32() {
        check_raw(
            r#"
                main :: () -> i32 {
                    f : f32 = 2.5;

                    f as i32
                }
            "#,
            "main",
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
                
                    my_complex := complex {
                        real_part: 5,
                        imaginary_part: 42,
                    };
                
                    do_math :: (c: complex) -> imaginary_vec3 {
                        // this is kind of akward because while we can access locals
                        // in the parameters and return type, we can't access `imaginary`
                        // from inside the body of this lambda
                        // this could be alleviated by adding a `type_of` builtin
                        [3] i32 { 1, c.real_part * c.imaginary_part as i32, 3 }
                    };
                
                    do_math(my_complex)[1] as i32
                }
            "#,
            "main",
            expect![[r#"

"#]],
            5 * 42,
        )
    }

    #[test]
    fn logical_operators() {
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

                puts :: (s: string) extern;
            "#,
            "main",
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
    fn control_flow() {
        check_raw(
            r#"
                fib :: (n: i32) -> i32 {
                    if n <= 1 {
                        return n;
                    }
                
                    fib(n - 1) + fib(n - 2)
                }
                
                main :: () -> i32 {
                    {
                        puts("before return");
                        return {
                            puts("before break");
                            x := 5;
                            break loop {
                                res := fib(x);
                                if res > 1_000 {
                                    printf("fib(%i) = %i\n", x, res);
                                    break x;
                                }
                                x = x + 1;
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
                
                puts :: (s: string) extern;
                printf :: (s: string, n1: i32, n2: i32) -> i32 extern;
            "#,
            "main",
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
                    {
                        if true {
                            y : i8 = 5;
                            break y;
                        }
    
                        y : i16 = 42;
                        y
                    }
                }
            "#,
            "main",
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
                    printf("~2147483647 =      %i\n", ~{4294967295 as u32});
                    printf(" 5032 &  25 =     %i\n", 5032 & 32);
                    printf(" 5000 |  20 =   %i\n", 5000 | 32);
                    printf(" 5032 ~  36 =   %i\n", 5032 ~ 36);
                    printf(" 5032 &~ 36 =   %i\n", 5032 &~ 36); 
                    printf(" 5032 <<  2 =  %i\n", 5032 << 2);
                    printf(" 5032 >>  2 =   %i\n", 5032 >> 2);
                    printf("-5032 >>  2 =  %i\n", -5032 >> 2);
                }
                
                printf :: (s: string, n: i64) extern;
            "#,
            "main",
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
    // the "ptrs_to_ptrs.capy" test is not reproducible
}

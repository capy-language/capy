mod builtin;
mod compiler;
pub(crate) mod convert;
mod extend;
mod layout;
mod mangle;

use compiler::program::compile_program;
use cranelift::prelude::isa::{self};
use cranelift::prelude::{settings, Configurable};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_object::object::write;
use cranelift_object::{ObjectBuilder, ObjectModule};

use hir::FQComptime;
use hir_ty::ComptimeResult;
use interner::Interner;
use rustc_hash::FxHashMap;
use std::ffi::c_char;
use std::mem;
use std::path::{Path, PathBuf};
use std::process::{exit, Command, Output};
use target_lexicon::{OperatingSystem, Triple};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verbosity {
    None,
    LocalFunctions { include_disasm: bool },
    AllFunctions { include_disasm: bool },
}

impl Verbosity {
    pub fn should_show(self, is_mod: bool) -> bool {
        match self {
            Verbosity::None => false,
            Verbosity::LocalFunctions { .. } => !is_mod,
            Verbosity::AllFunctions { .. } => true,
        }
    }

    pub fn include_disasm(self, is_mod: bool) -> bool {
        match self {
            Verbosity::None => false,
            Verbosity::LocalFunctions { include_disasm } => !is_mod && include_disasm,
            Verbosity::AllFunctions { include_disasm } => include_disasm,
        }
    }
}

pub(crate) type FinalSignature = cranelift::prelude::Signature;

pub use compiler::comptime::eval_comptime_blocks;

pub fn compile_jit(
    verbosity: Verbosity,
    entry_point: hir::Fqn,
    mod_dir: &std::path::Path,
    interner: &Interner,
    world_bodies: &hir::WorldBodies,
    tys: &hir_ty::ProjectInference,
    comptime_results: &FxHashMap<FQComptime, ComptimeResult>,
) -> fn(usize, *const *const c_char) -> usize {
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
        verbosity,
        entry_point,
        mod_dir,
        interner,
        world_bodies,
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

    unsafe { mem::transmute::<_, fn(usize, *const *const c_char) -> usize>(code_ptr) }
}

#[allow(clippy::too_many_arguments)]
pub fn compile_obj(
    verbosity: Verbosity,
    entry_point: hir::Fqn,
    mod_dir: &std::path::Path,
    interner: &Interner,
    world_bodies: &hir::WorldBodies,
    tys: &hir_ty::ProjectInference,
    comptime_results: &FxHashMap<FQComptime, ComptimeResult>,
    target: Triple,
) -> Result<Vec<u8>, write::Error> {
    let mut flag_builder = settings::builder();
    flag_builder.set("use_colocated_libcalls", "false").unwrap();
    flag_builder.set("is_pic", "false").unwrap();

    let isa_builder = isa::lookup(target).unwrap_or_else(|msg| {
        println!("invalid target: {}", msg);
        exit(1);
    });
    let isa = isa_builder
        .finish(settings::Flags::new(flag_builder.clone()))
        .unwrap();

    let builder = ObjectBuilder::new(
        isa,
        entry_point.file.to_string(mod_dir, interner),
        cranelift_module::default_libcall_names(),
    )
    .unwrap();
    let mut module = ObjectModule::new(builder);

    compile_program(
        verbosity,
        entry_point,
        mod_dir,
        interner,
        world_bodies,
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

#[derive(Debug)]
pub enum LinkingErr {
    NoCommand,
    IO(std::io::Error),
    CmdFailed {
        cmd_name: &'static str,
        output: Output,
    },
}

/// Returns `None`
pub fn link_to_exec(
    object_file: &PathBuf,
    target: Triple,
    libs: &[String],
) -> Result<PathBuf, LinkingErr> {
    let mut file_name = object_file.file_stem().unwrap().to_os_string();

    if target.operating_system == OperatingSystem::Windows {
        file_name.push(".exe");
    }

    let exe_path = object_file.parent().unwrap().join(file_name);

    if which::which("zig").is_ok() {
        link_with_zig(object_file, libs, &exe_path)?;
        Ok(exe_path)
    } else if which::which("gcc").is_ok() {
        link_with_gcc(object_file, target, libs, &exe_path)?;
        Ok(exe_path)
    } else {
        Err(LinkingErr::NoCommand)
    }
}

fn link_with_zig(
    object_file: &PathBuf,
    libs: &[String],
    exe_path: &Path,
) -> Result<(), LinkingErr> {
    let zig = Command::new("zig")
        .arg("build-exe")
        .arg(object_file)
        .args(libs)
        .arg("--library")
        .arg("C")
        .arg(format!("-femit-bin={}", exe_path.display()))
        .output()
        .map_err(LinkingErr::IO)?;

    if !zig.status.success() {
        return Err(LinkingErr::CmdFailed {
            cmd_name: "gcc",
            output: zig,
        });
    }

    Ok(())
}

fn link_with_gcc(
    object_file: &PathBuf,
    target: Triple,
    libs: &[String],
    exe_path: &Path,
) -> Result<(), LinkingErr> {
    let linker_args: &[&str] = match target.operating_system {
        OperatingSystem::Darwin(_) => {
            // check if -ld_classic is supported
            let ld_v = Command::new("ld").arg("-v").output().unwrap();
            let stderr = String::from_utf8(ld_v.stderr).expect("`ld` should have given utf8");

            if stderr.contains("ld-classic") {
                &["-Xlinker", "-ld_classic"]
            } else {
                &[]
            }
        }
        _ => &[],
    };

    let gcc = Command::new("gcc")
        .arg("-o")
        .arg(exe_path)
        .args(linker_args)
        .args(libs.iter().map(|lib| "-l".to_string() + lib))
        .arg(object_file)
        .output()
        .map_err(LinkingErr::IO)?;

    if !gcc.status.success() {
        return Err(LinkingErr::CmdFailed {
            cmd_name: "gcc",
            output: gcc,
        });
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use core::panic;
    use std::{collections::HashMap, env, fs, path::Path};

    use ast::AstNode;
    use expect_test::{expect, Expect};
    use hir_ty::{InferenceCtx, InferenceResult};
    use path_clean::PathClean;
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

    #[allow(clippy::too_many_arguments)]
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

            assert_eq!(diagnostics, vec![]);

            world_index.add_file(module, index);
            world_bodies.add_file(module, bodies);
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
        assert_eq!(diagnostics, vec![]);
        world_index.add_file(file, index);
        world_bodies.add_file(file, bodies);

        let entry_point = hir::Fqn {
            file,
            name: hir::Name(interner.intern(entry_point)),
        };

        let mut comptime_results = FxHashMap::default();

        let InferenceResult {
            tys, diagnostics, ..
        } = InferenceCtx::new(&world_index, &world_bodies, &interner, |comptime, tys| {
            eval_comptime_blocks(
                Verbosity::AllFunctions {
                    include_disasm: true,
                },
                vec![comptime],
                &mut comptime_results,
                Path::new(""),
                &interner,
                &world_bodies,
                tys,
                HOST.pointer_width().unwrap().bits(),
            );

            comptime_results[&comptime].clone()
        })
        .finish(Some(entry_point), false);
        assert_eq!(diagnostics, vec![]);

        println!("comptime:");

        // evaluate any comptimes that haven't been ran yet
        eval_comptime_blocks(
            Verbosity::AllFunctions {
                include_disasm: true,
            },
            world_bodies.find_comptimes(),
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

        let exec = link_to_exec(&file, HOST, &[]).unwrap();

        let output = std::process::Command::new(&exec)
            .args(args)
            .output()
            .unwrap_or_else(|_| panic!("{} did not run successfully", exec.display()));

        println!("test exited with {}", output.status);

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
                
                i32                (134218372) : size = 4, align = 4, stride = 4
                i64                (134218504) : size = 8, align = 8, stride = 8
                u64                (134217992) : size = 8, align = 8, stride = 8
                i8                 (134218273) : size = 1, align = 1, stride = 1
                u128               (134218000) : size = 16, align = 8, stride = 16
                usize              (134217992) : size = 8, align = 8, stride = 8
                f32                (201326724) : size = 4, align = 4, stride = 4
                void               (67108896) : size = 0, align = 1, stride = 0
                any                (536871184) : size = 16, align = 8, stride = 16
                rawptr             (671088904) : size = 8, align = 8, stride = 8
                rawslice           (738197776) : size = 16, align = 8, stride = 16
                str                (335544584) : size = 8, align = 8, stride = 8
                bool               (268435489) : size = 1, align = 1, stride = 1
                char               (402653217) : size = 1, align = 1, stride = 1
                type               (469762180) : size = 4, align = 4, stride = 4
                Person             (1073741824) : size = 12, align = 8, stride = 16
                Foo                (1073741825) : size = 1, align = 1, stride = 1
                [6] Person         (1207959552) : size = 96, align = 8, stride = 96
                [ ] Person         (1275068416) : size = 16, align = 8, stride = 16
                 ^  Person         (1342177280) : size = 8, align = 8, stride = 8
                distinct Person    (1140850688) : size = 12, align = 8, stride = 16
                Dessert            (1476395008) : size = 17, align = 8, stride = 24
                Dessert.Brownie    (1543503876) : size = 0, align = 1, stride = 0
                Dessert.Apple_Pie  (1543503874) : size = 16, align = 8, stride = 16
                Dessert.Milkshake  (1543503879) : size = 1, align = 1, stride = 1
                Farm_Animal        (1476395009) : size = 1, align = 1, stride = 1
                Farm_Animal.Sheep  (1543503881) : size = 0, align = 1, stride = 0
                ()       -> void   (1409286144) : size = 8, align = 8, stride = 8
                (x: i32) -> f32    (1409286145) : size = 8, align = 8, stride = 8
                
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
                Dessert.Apple_Pie == Dessert.Cheesecake : false
                Dessert.Cheesecake == Dessert.Cheesecake : true
                Farm_Animal.Cow == Dessert.Ice_Cream : false
                Farm_Animal.Cow == Farm_Animal.Cow : true
                () -> void == (x : i32) -> f32 : false
                () -> void == () -> void : true
                
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
                [ 1, hello, true, 5.300 ]
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
                
            "#]],
            0,
        )
    }

    #[test]
    fn lists() {
        check_files(
            "../../examples/lists.capy",
            &[],
            "main",
            expect![[r#"
                42
                [ 4, 8, 15, 16, 23 ]
                
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
                core :: mod "core";

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
                                    core.println("fib(", x, ") = ", res);
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
                
                puts :: (s: str) extern;
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
                    s := (^[1000]char).(rawptr.(s));
                    idx := 0;
                    while idx < 100 {
                        ch := s[idx];
                        if ch == '\0' {
                            break;
                        }
                        putchar(ch);
                        idx = idx + 1;
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

                        n = n - 10 * a;
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
                
                    y_raw := (^usize).(rawptr.(^y))^;
                    z_raw := (^usize).(rawptr.(^z))^;

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
                        i = i + 1;
                
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

                        i = i + 1;
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

                        n = n - 10 * a;
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

                    ptr := (mut rawptr).(^mut x);

                    (^mut u32).(ptr) ^= 5;

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

                        n = n - 10 * a;
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
                core :: mod "core";

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
            { a = [ [ 0, 0, 0, 0 ], [ 0, 0, 0, 0 ] ], b = 0, c = 0.000, d = false, e = \0, f = () }

"]],
            0,
        )
    }

    #[test]
    fn i128_literals() {
        check_raw(
            r#"
                core :: mod "core";

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
                core :: mod "core";

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
                core :: mod "core";

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
                core :: mod "core";

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
                core :: mod "core";

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
                core :: mod "core";

                main :: () {
                    idx := 0;
                    while idx < core.args.len {
                        core.println("arg(", idx, ") = ", core.args[idx]);

                        idx = idx + 1;
                    }
                }
            "#,
            "main",
            true,
            &["hello", "world!", "wow look at this arg", "foo=bar"],
            if cfg!(windows) {
                expect![["
                arg(0) = test-temp\\14e703d.exe
                arg(1) = hello
                arg(2) = world!
                arg(3) = wow look at this arg
                arg(4) = foo=bar

"]]
            } else {
                expect![["
                arg(0) = test-temp/14e703d
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
                core :: mod "core";

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
            &["hello", "world!", "wow look at this arg", "foo=bar"],
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
            &["hello", "world!", "wow look at this arg", "foo=bar"],
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
                [700] sheep: hello, wool: 1.000, fullness: 0.500
                [600] oink oink
                
            "#]],
            0,
        )
    }

    #[test]
    fn if_autocast_variant_to_enum() {
        check_raw_with_args(
            r#"
                core :: mod "core";

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
            &["hello", "world!", "wow look at this arg", "foo=bar"],
            expect![["
            ()

"]],
            0,
        )
    }

    #[test]
    fn switch_autocast_variant_to_enum() {
        check_raw_with_args(
            r#"
                core :: mod "core";

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
                        A => Animal.Dog.(),
                        B => Animal.Fish.(42),
                        C => Animal.Cat.(),
                        D => Animal.Dog.()
                    };

                    core.println(animal);
                }
            "#,
            "main",
            true,
            &["hello", "world!", "wow look at this arg", "foo=bar"],
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
                core :: mod "core";

                main :: () {
                    foo := .[1, 2, 3];

                    bar : []u128 = foo;

                    core.println(bar);
                }
            "#,
            "main",
            true,
            &["hello", "world!", "wow look at this arg", "foo=bar"],
            expect![["
            [ 1, 2, 3 ]

"]],
            0,
        )
    }

    // the "ptrs_to_ptrs.capy" and "comptime_types.capy" tests are not reproducible
}

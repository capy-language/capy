mod convert;
mod functions;
mod gen;
mod mangle;

use cranelift::prelude::isa::{self};
use cranelift::prelude::{settings, Configurable};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_object::object::write;
use cranelift_object::{ObjectBuilder, ObjectModule};
use hir_ty::ResolvedTy;

use gen::CodeGen;
use interner::Interner;
use la_arena::Arena;
use rustc_hash::FxHashMap;
use std::mem;
use std::path::PathBuf;
use std::process::{exit, Command};
use std::str::FromStr;
use target_lexicon::Triple;

pub(crate) type CraneliftSignature = cranelift::prelude::Signature;
pub(crate) type CapyFnSignature = hir_ty::FunctionSignature;

pub fn compile_jit(
    verbose: bool,
    entry_point: hir::Fqn,
    resolved_arena: &Arena<ResolvedTy>,
    interner: &Interner,
    bodies_map: &FxHashMap<hir::Name, hir::Bodies>,
    tys: &hir_ty::InferenceResult,
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

    let cmain = CodeGen::new(
        verbose,
        entry_point,
        resolved_arena,
        interner,
        bodies_map,
        tys,
        &mut module,
    )
    .finish();

    // Finalize the functions which were defined, which resolves any
    // outstanding relocations (patching in addresses, now that they're
    // available).
    // This also prepares the code for JIT execution
    module.finalize_definitions().unwrap();

    let code_ptr = module.get_finalized_function(cmain);

    unsafe { mem::transmute::<_, fn(usize, usize) -> usize>(code_ptr) }
}

pub fn compile_obj(
    verbose: bool,
    entry_point: hir::Fqn,
    resolved_arena: &Arena<ResolvedTy>,
    interner: &Interner,
    bodies_map: &FxHashMap<hir::Name, hir::Bodies>,
    tys: &hir_ty::InferenceResult,
    target: Option<&str>,
) -> Result<Vec<u8>, write::Error> {
    let mut flag_builder = settings::builder();
    // flag_builder.set("use_colocated_libcalls", "false").unwrap();
    flag_builder.set("is_pic", "true").unwrap();

    let isa_builder = if let Some(target) = target {
        isa::lookup(Triple::from_str(target).unwrap_or_else(|msg| {
            println!("invalid target: {}", msg);
            exit(1);
        }))
        .unwrap_or_else(|msg| {
            println!("invalid target: {}", msg);
            exit(1);
        })
    } else {
        cranelift_native::builder().unwrap_or_else(|msg| {
            println!("host machine is not supported: {}", msg);
            exit(1);
        })
    };
    let isa = isa_builder
        .finish(settings::Flags::new(flag_builder))
        .unwrap();

    let builder = ObjectBuilder::new(
        isa,
        interner.lookup(entry_point.module.0),
        cranelift_module::default_libcall_names(),
    )
    .unwrap();
    let mut module = ObjectModule::new(builder);

    CodeGen::new(
        verbose,
        entry_point,
        resolved_arena,
        interner,
        bodies_map,
        tys,
        &mut module,
    )
    .finish();

    // Finalize the functions which were defined, which resolves any
    // outstanding relocations (patching in addresses, now that they're
    // available).
    // This also generates the proper .o
    let product = module.finish();

    product.emit()
}

pub fn link_to_exec(path: &PathBuf) -> PathBuf {
    let exe_path = path.parent().unwrap().join(path.file_stem().unwrap());
    let success = Command::new("gcc")
        .arg(path)
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
    use std::{env, fs, path::Path};

    use ast::AstNode;
    use expect_test::{expect, Expect};
    use hir::UIDGenerator;
    use hir_ty::InferenceCtx;
    use regex::Regex;

    use super::*;

    fn check(
        main_file: &str,
        other_files: &[&str],
        entry_point: &str,
        stdout_expect: Expect,
        expected_status: i32,
    ) {
        env::set_current_dir(env!("CARGO_MANIFEST_DIR")).unwrap();

        let mut interner = Interner::default();
        let mut world_index = hir::WorldIndex::default();

        let mut uid_gen = UIDGenerator::default();
        let mut twr_arena = Arena::new();
        let mut bodies_map = FxHashMap::default();

        for file in other_files {
            let module_name = Path::new(file).file_stem().unwrap().to_str().unwrap();
            let text = &fs::read_to_string(file).unwrap();

            let tokens = lexer::lex(text);
            let tree = parser::parse_source_file(&tokens, text).into_syntax_tree();
            let root = ast::Root::cast(tree.root(), &tree).unwrap();
            let (index, _) = hir::index(root, &tree, &mut uid_gen, &mut twr_arena, &mut interner);

            let module = hir::Name(interner.intern(module_name));

            world_index.add_module(module, index);

            let (bodies, _) = hir::lower(
                root,
                &tree,
                module,
                &world_index,
                &mut uid_gen,
                &mut twr_arena,
                &mut interner,
            );
            bodies_map.insert(module, bodies);
        }

        let main_name = Path::new(main_file).file_stem().unwrap().to_str().unwrap();
        let text = &fs::read_to_string(main_file).unwrap();
        let module = hir::Name(interner.intern(main_name));
        let tokens = lexer::lex(text);
        let tree = parser::parse_source_file(&tokens, text).into_syntax_tree();
        let root = ast::Root::cast(tree.root(), &tree).unwrap();
        let (index, _) = hir::index(root, &tree, &mut uid_gen, &mut twr_arena, &mut interner);
        world_index.add_module(module, index);

        let (bodies, _) = hir::lower(
            root,
            &tree,
            module,
            &world_index,
            &mut uid_gen,
            &mut twr_arena,
            &mut interner,
        );
        bodies_map.insert(module, bodies);

        let mut resolved_arena = Arena::new();

        let (inference_result, _) =
            InferenceCtx::new(&bodies_map, &world_index, &twr_arena, &mut resolved_arena).finish();

        let bytes = compile_obj(
            true,
            hir::Fqn {
                module,
                name: hir::Name(interner.intern(entry_point)),
            },
            &resolved_arena,
            &interner,
            &bodies_map,
            &inference_result,
            None,
        )
        .unwrap();

        let output_folder = env::current_dir().unwrap().join("test-temp");

        let _ = fs::create_dir(&output_folder);

        let file = output_folder.join(format!("{}.o", main_name));
        fs::write(&file, bytes.as_slice()).unwrap_or_else(|why| {
            panic!("{}: {why}", file.display());
        });

        let exec = link_to_exec(&file);

        let output = std::process::Command::new(exec.clone())
            .output()
            .expect(&format!("{} did not run successfully", exec.display()));

        assert_eq!(output.status.code().unwrap(), expected_status);

        let re = Regex::new(r#"[^A-Za-z0-9\n\s().=#!_:,\[\]\-><{}]"#).unwrap();
        let stdout = std::str::from_utf8(&output.stdout)
            .unwrap()
            .replace("\r", "");
        let stdout = re.replace_all(&stdout, "");

        let trim_expect_data = trim_indent(stdout_expect.data());
        let mut trim_expect_data = trim_expect_data.bytes();
        let mut stdout_data = stdout.bytes();

        for _ in 0..trim_expect_data.len().max(stdout_data.len()) {
            let expect = trim_expect_data.next();
            let actual = stdout_data.next();

            println!(
                "{:>3} : {:>3} | {:>2} : {:>2} {}",
                expect.map(|expect| expect.to_string()).unwrap_or_default(),
                actual.map(|expect| expect.to_string()).unwrap_or_default(),
                expect
                    .map(|expect| match expect as char {
                        '\r' => "\\r".to_string(),
                        '\n' => "\\n".to_string(),
                        other => other.to_string(),
                    })
                    .unwrap_or_default(),
                actual
                    .map(|actual| match actual as char {
                        '\r' => "\\r".to_string(),
                        '\n' => "\\n".to_string(),
                        other => other.to_string(),
                    })
                    .unwrap_or_default(),
                if expect != actual { "NOT EQUAL" } else { "" }
            );
        }

        let stdout = format!("{}\n", stdout);

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
    fn readme() {
        check(
            "../../examples/readme.capy",
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
            my_array[1][1][0] = 2
            my_array[1][1][1] = 4
            my_array[1][1][2] = 6
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
            
            global[0][0][0] = 123
            global[0][0][1] = 456
            global[0][0][2] = 789
            global[0][1][0] = 123
            global[0][1][1] = 456
            global[0][1][2] = 789
            global[0][2][0] = 123
            global[0][2][1] = 456
            global[0][2][2] = 789
            global[1][0][0] = 123
            global[1][0][1] = 456
            global[1][0][2] = 789
            global[1][1][0] = 123
            global[1][1][1] = 456
            global[1][1][2] = 789
            global[1][2][0] = 123
            global[1][2][1] = 456
            global[1][2][2] = 789
            global[2][0][0] = 123
            global[2][0][1] = 456
            global[2][0][2] = 789
            global[2][1][0] = 123
            global[2][1][1] = 456
            global[2][1][2] = 789
            global[2][2][0] = 123
            global[2][2][1] = 456
            global[2][2][2] = 789
            
            "#]],
            0,
        )
    }

    #[test]
    fn files() {
        check(
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

    // "ptrs.capy" and "ptrs_to_ptrs.capy" tests won't be the same on all platforms
}

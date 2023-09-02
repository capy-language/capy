mod source;

use std::{cell::RefCell, env, io, path::PathBuf, process::exit, rc::Rc, time::Instant};

use clap::{Parser, Subcommand};
use hir::WorldIndex;
use itertools::Itertools;
use la_arena::Arena;
use line_index::LineIndex;
use path_clean::PathClean;
use rustc_hash::FxHashMap;
use std::fs;
use uid_gen::UIDGenerator;

use crate::source::SourceFile;

#[derive(Debug, Parser)]
#[command(name = "Capy Programming Language")]
#[command(author = "NotAFlyingGoose <notaflyinggoose@gmail.com>")]
#[command(version)]
#[command(about = "A Cool Programming Language", long_about = None)]
struct CompilerConfig {
    #[command(subcommand)]
    action: BuildAction,
}

#[derive(Debug, Subcommand)]
enum BuildAction {
    /// Takes in one or more .capy files and compiles them
    Build {
        /// The file to compile
        #[arg(required = true)]
        file: String,

        /// The entry point function of the program
        #[arg(long, default_value = "main")]
        entry_point: String,

        /// The target to compile for. If supplied, no linking will be done
        #[arg(long)]
        target: Option<String>,

        /// Whether or not to show advanced compiler information
        #[arg(short, long, default_value_t = 0, action = clap::ArgAction::Count)]
        verbose: u8,
    },
    /// Takes in one or more .capy files, compiles them, and runs the compiled executable
    Run {
        /// The files to compile and run
        #[arg(required = true)]
        file: String,

        /// The entry point function of the program
        #[arg(long, default_value = "main")]
        entry_point: String,

        /// Whether or not to run by JIT instead of by compilation to an executable file
        #[arg(long)]
        jit: bool,

        /// Whether or not to show advanced compiler information
        #[arg(short, long, default_value_t = 0, action = clap::ArgAction::Count)]
        verbose: u8,
    },
}

macro_rules! get_build_config {
    (
        $action:expr => $($property:ident),+
    ) => {
        match $action {
            BuildAction::Build {
                $($property,)+ target
            } => ($($property,)+ CompilationConfig::Compile(target)),
            BuildAction::Run {
                $($property,)+ jit
            } => ($($property,)+ if jit { CompilationConfig::Jit } else { CompilationConfig::Run })
        }
    };
}

fn main() -> io::Result<()> {
    let config = CompilerConfig::parse();

    let (file, entry_point, verbose, config) =
        get_build_config!(config.action => file, entry_point, verbose);

    let file = env::current_dir().unwrap().join(file).clean();

    let contents = match fs::read_to_string(&file) {
        Ok(contents) => contents,
        Err(why) => {
            println!("{}: {}", file.display(), why);
            exit(1)
        }
    };

    compile_file(file, contents, entry_point, config, verbose)
}

#[derive(Clone, PartialEq)]
enum CompilationConfig {
    Compile(Option<String>),
    Run,
    Jit,
}

const ANSI_RED: &str = "\x1B[1;91m";
const ANSI_GREEN: &str = "\x1B[1;92m";
const ANSI_WHITE: &str = "\x1B[1;97m";
const ANSI_RESET: &str = "\x1B[0m";

fn compile_file(
    file_name: PathBuf,
    file_contents: String,
    entry_point: String,
    config: CompilationConfig,
    verbose: u8,
) -> io::Result<()> {
    let with_color = supports_color::on(supports_color::Stream::Stdout).is_some();
    let (ansi_red, ansi_green, ansi_white, ansi_reset) = if with_color {
        (ANSI_RED, ANSI_GREEN, ANSI_WHITE, ANSI_RESET)
    } else {
        ("", "", "", "")
    };

    if !file_name.to_string_lossy().ends_with(".capy") {
        println!("{ansi_red}error{ansi_white}: capy files must end in `.capy`{ansi_reset}");
        exit(1)
    }

    println!("{ansi_green}Compiling{ansi_reset}  ...");
    let compilation_start = Instant::now();

    let interner = Rc::new(RefCell::new(interner::Interner::default()));
    let world_index = Rc::new(RefCell::new(WorldIndex::default()));
    let bodies_map = Rc::new(RefCell::new(FxHashMap::default()));
    let uid_gen = Rc::new(RefCell::new(UIDGenerator::default()));
    let twr_arena = Rc::new(RefCell::new(Arena::new()));

    let main_fn = hir::Name(interner.borrow_mut().intern(&entry_point));

    let mut line_indexes = FxHashMap::default();
    let mut source_files = FxHashMap::default();

    // parse the first source file given in the `capy` command

    let mut source_file = SourceFile::parse(
        file_name.clone(),
        file_contents.clone(),
        uid_gen.clone(),
        twr_arena.clone(),
        interner.clone(),
        bodies_map.clone(),
        world_index.clone(),
        verbose,
    );

    line_indexes.insert(source_file.module, LineIndex::new(&file_contents));

    if verbose >= 1 {
        println!();
    }

    let mut current_imports = source_file.build_bodies();
    source_files.insert(source_file.module, source_file);

    // find all imports in the source file, compile them, then do the same for their imports

    let mut project_root = file_name.parent().unwrap().to_path_buf();

    while !current_imports.is_empty() {
        let cloned_imports = current_imports.clone();
        current_imports.clear();
        for file_name in cloned_imports {
            if source_files.contains_key(&file_name) {
                continue;
            }

            let file_name = {
                let interner = interner.borrow();
                PathBuf::from(interner.lookup(file_name.0))
            };
            let file_contents = match fs::read_to_string(&file_name) {
                Ok(contents) => contents,
                Err(why) => {
                    println!("{}: {}", file_name.display(), why);
                    exit(1)
                }
            };

            if !file_name.starts_with(&project_root) {
                let last_common_idx = file_name
                    .components()
                    .zip(project_root.components())
                    .find_position(|(file_name_comp, project_root_comp)| {
                        file_name_comp != project_root_comp
                    })
                    .map(|(idx, _)| idx)
                    .unwrap_or(0);
                let least_common_path =
                    PathBuf::from_iter(project_root.components().take(last_common_idx));

                if project_root != least_common_path {
                    project_root = least_common_path;
                }
            }

            let mut source_file = SourceFile::parse(
                file_name,
                file_contents.clone(),
                uid_gen.clone(),
                twr_arena.clone(),
                interner.clone(),
                bodies_map.clone(),
                world_index.clone(),
                verbose,
            );

            line_indexes.insert(source_file.module, LineIndex::new(&file_contents));

            current_imports.extend(source_file.build_bodies());

            source_files.insert(source_file.module, source_file);
        }
    }

    if verbose >= 1 {
        println!();
    }

    // infer types

    let (inference, ty_diagnostics) = hir_ty::InferenceCtx::new(
        &bodies_map.borrow(),
        &world_index.borrow(),
        &twr_arena.borrow(),
    )
    .finish();
    if verbose >= 2 {
        let debug = inference.debug(&project_root, &interner.borrow(), true);
        println!("{}", debug);
        if !debug.is_empty() {
            println!();
        }
    }

    // print out errors and warnings

    let has_errors = ty_diagnostics.iter().any(hir_ty::TyDiagnostic::is_error)
        || source_files.iter().any(|(_, source)| source.has_errors());
    source_files
        .iter()
        .for_each(|(_, source)| source.print_diagnostics(&project_root, with_color));
    for d in ty_diagnostics {
        let line_index = &line_indexes[&d.module];
        let source_file = &source_files[&d.module];

        println!(
            "{}",
            diagnostics::Diagnostic::from_ty(d)
                .display(
                    &source_file.file_name.to_string_lossy(),
                    &source_file.contents,
                    &project_root,
                    &interner.borrow(),
                    line_index,
                    with_color,
                )
                .join("\n")
        )
    }

    if has_errors {
        println!("\nnot compiling due to previous errors");
        exit(1);
    }

    let main_modules = source_files
        .iter()
        .filter(|(_, sf)| sf.has_fn_of_name(main_fn))
        .map(|(name, _)| *name)
        .collect_vec();
    if main_modules.is_empty() {
        println!(
            "{ansi_red}error{ansi_white}: there is no `{}` function{ansi_reset}",
            interner.borrow().lookup(main_fn.0)
        );
        std::process::exit(1);
    } else if main_modules.len() > 1 {
        println!(
            "{ansi_red}error{ansi_white}: there are multiple `{}` functions{ansi_reset}",
            interner.borrow().lookup(main_fn.0)
        );
        std::process::exit(1);
    }

    let parse_finish = compilation_start.elapsed();

    // frontend stuff is finally over
    // now we can actually compile it

    println!(
        "{ansi_green}Finalizing{ansi_reset} (parsed in {:.2}s)",
        parse_finish.as_secs_f32()
    );
    let interner = interner.borrow();

    let main_module = main_modules.first().unwrap();
    if config == CompilationConfig::Jit {
        let jit_fn = codegen::compile_jit(
            verbose >= 1,
            hir::Fqn {
                module: *main_module,
                name: main_fn,
            },
            &project_root,
            &interner,
            &bodies_map.borrow(),
            &inference,
        );

        println!(
            "{ansi_green}Finished{ansi_reset}   {} (JIT) in {:.2}s",
            interner.lookup(main_module.0),
            compilation_start.elapsed().as_secs_f32(),
        );
        println!(
            "{ansi_green}Running{ansi_reset}    `{}`\n",
            interner.lookup(main_module.0)
        );
        let status = jit_fn(0, 0);
        println!("\nProcess exited with {}", status);

        return Ok(());
    }

    let bytes = match codegen::compile_obj(
        verbose >= 1,
        hir::Fqn {
            module: *main_module,
            name: main_fn,
        },
        &project_root,
        &interner,
        &bodies_map.borrow(),
        &inference,
        match &config {
            CompilationConfig::Compile(target) => target.as_deref(),
            _ => None,
        },
    ) {
        Ok(bytes) => bytes,
        Err(why) => {
            println!("Cranelift Error: {}", why);
            return Ok(());
        }
    };

    let output_folder = env::current_dir().unwrap().join("out");

    let _ = fs::create_dir(&output_folder);

    let output_file_name = std::path::PathBuf::from(interner.lookup(main_module.0));
    let output_file_name = output_file_name.file_name().unwrap().to_string_lossy();
    let file = output_folder.join(format!("{output_file_name}.o",));
    fs::write(&file, bytes.as_slice()).unwrap_or_else(|why| {
        println!("{}: {why}", file.display());
        exit(1);
    });

    if let CompilationConfig::Compile(Some(target)) = config {
        println!(
            "{ansi_green}Finished{ansi_reset}   {} ({}) in {:.2}s",
            file.display(),
            target,
            compilation_start.elapsed().as_secs_f32(),
        );
        return Ok(());
    }

    let exec = codegen::link_to_exec(&file);
    println!(
        "{ansi_green}Finished{ansi_reset}   {} ({}) in {:.2}s",
        interner.lookup(main_module.0),
        exec.display(),
        compilation_start.elapsed().as_secs_f32(),
    );

    if matches!(config, CompilationConfig::Compile(_)) {
        return Ok(());
    }

    println!("{ansi_green}Running{ansi_reset}    `{}`\n", exec.display());
    match std::process::Command::new(exec).status() {
        Ok(status) => {
            println!("\nProcess exited with {}", status);
        }
        Err(why) => {
            println!("\nProcess exited early: {}", why);
        }
    }

    Ok(())
}

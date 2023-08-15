mod source;

use std::{cell::RefCell, env, io, process::exit, rc::Rc, time::Instant};

use clap::{Parser, Subcommand};
use hir::{UIDGenerator, WorldIndex};
use la_arena::Arena;
use line_index::LineIndex;
use rustc_hash::FxHashMap;
use std::fs;

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
        /// The files to compile
        #[arg(required = true)]
        files: Vec<String>,

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
        files: Vec<String>,

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

const ANSI_RED: &str = "\x1B[1;91m";
const ANSI_GREEN: &str = "\x1B[1;92m";
const ANSI_WHITE: &str = "\x1B[1;97m";
const ANSI_RESET: &str = "\x1B[0m";

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

    let (files, entry_point, verbose, config) =
        get_build_config!(config.action => files, entry_point, verbose);

    let files = files
        .iter()
        .map(|filename| match fs::read_to_string(filename) {
            Ok(contents) => (filename.clone(), contents),
            Err(why) => {
                println!("{}: {}", filename, why);
                exit(1)
            }
        })
        .collect();

    compile_files(files, entry_point, config, verbose)
}

#[derive(Clone, PartialEq)]
enum CompilationConfig {
    Compile(Option<String>),
    Run,
    Jit,
}

fn compile_files(
    files: Vec<(String, String)>,
    entry_point: String,
    config: CompilationConfig,
    verbose: u8,
) -> io::Result<()> {
    println!("{ANSI_GREEN}Compiling{ANSI_RESET}  ...");
    let compilation_start = Instant::now();

    let interner = Rc::new(RefCell::new(interner::Interner::default()));
    let world_index = Rc::new(RefCell::new(WorldIndex::default()));
    let bodies_map = Rc::new(RefCell::new(FxHashMap::default()));
    let uid_gen = Rc::new(RefCell::new(UIDGenerator::default()));
    let twr_arena = Rc::new(RefCell::new(Arena::new()));
    let resolved_arena = Rc::new(RefCell::new(Arena::new()));

    let main_fn = hir::Name(interner.borrow_mut().intern(&entry_point));

    let mut line_indexes = FxHashMap::default();
    let mut source_files = FxHashMap::default();

    let mut main_modules = Vec::new();
    for (file_name, contents) in files {
        let source_file = SourceFile::parse(
            file_name.clone(),
            contents.clone(),
            uid_gen.clone(),
            twr_arena.clone(),
            resolved_arena.clone(),
            interner.clone(),
            bodies_map.clone(),
            world_index.clone(),
            verbose,
        );

        if source_file.has_fn_of_name(main_fn) {
            main_modules.push(source_file.module);
        }

        line_indexes.insert(source_file.module, LineIndex::new(&contents));
        source_files.insert(source_file.module, source_file);
    }
    if verbose >= 1 {
        println!();
    }

    if main_modules.is_empty() {
        println!(
            "{ANSI_RED}error{ANSI_WHITE}: there is no `{}` function{ANSI_RESET}",
            interner.borrow().lookup(main_fn.0)
        );
        std::process::exit(1);
    } else if main_modules.len() > 1 {
        println!(
            "{ANSI_RED}error{ANSI_WHITE}: there are multiple `{}` functions{ANSI_RESET}",
            interner.borrow().lookup(main_fn.0)
        );
        std::process::exit(1);
    }

    // parse the bodies of each file into hir::Expr's and hir::LocalDef's

    source_files
        .iter_mut()
        .for_each(|(_, source)| source.build_bodies());
    if verbose >= 1 {
        println!();
    }

    // infer types

    let (inference, ty_diagnostics) = hir_ty::InferenceCtx::new(
        &bodies_map.borrow(),
        &world_index.borrow(),
        &twr_arena.borrow(),
        &mut resolved_arena.borrow_mut(),
    )
    .finish();
    if verbose >= 2 {
        let debug = inference.debug(&resolved_arena.borrow(), &interner.borrow(), true);
        println!("{}", debug);
        if !debug.is_empty() {
            println!();
        }
    }

    // print out errors and warnings

    let has_errors =
        !ty_diagnostics.is_empty() || source_files.iter().any(|(_, source)| source.has_errors());
    source_files
        .iter()
        .for_each(|(_, source)| source.print_diagnostics());
    for d in ty_diagnostics {
        let line_index = &line_indexes[&d.module];
        let source_file = &source_files[&d.module];

        println!(
            "{}",
            diagnostics::Diagnostic::from_ty(d)
                .display(
                    &source_file.file_name,
                    &source_file.contents,
                    &resolved_arena.borrow(),
                    &interner.borrow(),
                    line_index,
                )
                .join("\n")
        )
    }

    if has_errors {
        println!("\nnot compiling due to previous errors");
        exit(1);
    }

    let parse_finish = compilation_start.elapsed();

    // frontend stuff is finally over
    // now we can actually compile it

    println!(
        "{ANSI_GREEN}Finalizing{ANSI_RESET} (parsed in {:.2}s)",
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
            &resolved_arena.borrow(),
            &interner,
            &bodies_map.borrow(),
            &inference,
        );

        println!(
            "{ANSI_GREEN}Finished{ANSI_RESET}   {} (JIT) in {:.2}s",
            interner.lookup(main_module.0),
            compilation_start.elapsed().as_secs_f32(),
        );
        println!(
            "{ANSI_GREEN}Running{ANSI_RESET}    `{}`\n",
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
        &resolved_arena.borrow(),
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

    let file = output_folder.join(format!("{}.o", interner.lookup(main_module.0)));
    fs::write(&file, bytes.as_slice()).unwrap_or_else(|why| {
        println!("{}: {why}", file.display());
        exit(1);
    });

    if let CompilationConfig::Compile(Some(target)) = config {
        println!(
            "{ANSI_GREEN}Finished{ANSI_RESET}   {} ({}) in {:.2}s",
            file.display(),
            target,
            compilation_start.elapsed().as_secs_f32(),
        );
        return Ok(());
    }

    let exec = codegen::link_to_exec(&file);
    println!(
        "{ANSI_GREEN}Finished{ANSI_RESET}   {} ({}) in {:.2}s",
        interner.lookup(main_module.0),
        exec.display(),
        compilation_start.elapsed().as_secs_f32(),
    );

    if matches!(config, CompilationConfig::Compile(_)) {
        return Ok(());
    }

    println!("{ANSI_GREEN}Running{ANSI_RESET}    `{}`\n", exec.display());
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

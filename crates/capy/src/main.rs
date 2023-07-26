mod source;

use std::{cell::RefCell, env, io, process::exit, rc::Rc, time::Instant};

use clap::{Parser, Subcommand};
use hir::WorldIndex;
use la_arena::Arena;
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
                $($property,)+
            } => ($($property,)+ false),
            BuildAction::Run {
                $($property,)+
            } => ($($property,)+ true)
        }
    };
}

fn main() -> io::Result<()> {
    let config = CompilerConfig::parse();

    let (files, entry_point, verbose, should_run) =
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

    compile_files(files, entry_point, should_run, verbose)
}

fn compile_files(
    files: Vec<(String, String)>,
    entry_point: String,
    should_run: bool,
    verbose: u8,
) -> io::Result<()> {
    println!("{ANSI_GREEN}Compiling{ANSI_RESET}  ...");
    let compilation_start = Instant::now();

    let interner = Rc::new(RefCell::new(interner::Interner::default()));
    let world_index = Rc::new(RefCell::new(WorldIndex::default()));
    let bodies_map = Rc::new(RefCell::new(FxHashMap::default()));
    let tys_map = Rc::new(RefCell::new(FxHashMap::default()));
    let twr_arena = Rc::new(RefCell::new(Arena::new()));
    let resolved_arena = Rc::new(RefCell::new(Arena::new()));

    let mut source_files = Vec::new();
    for (file_name, contents) in files {
        source_files.push(SourceFile::parse(
            file_name.clone(),
            contents.clone(),
            twr_arena.clone(),
            resolved_arena.clone(),
            interner.clone(),
            bodies_map.clone(),
            tys_map.clone(),
            world_index.clone(),
            verbose,
        ));
    }
    if verbose >= 1 {
        println!();
    }

    let main_fn = hir::Name(interner.borrow_mut().intern(&entry_point));

    let main_modules = source_files
        .iter()
        .filter(|source| source.has_fn_of_name(main_fn))
        .map(|source| (source.file_name.clone(), source.module))
        .collect::<Vec<_>>();
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

    source_files
        .iter_mut()
        .for_each(|source| source.build_bodies());
    if verbose >= 1 {
        println!();
    }

    source_files
        .iter_mut()
        .for_each(|source| source.build_tys());

    source_files
        .iter()
        .for_each(|source| source.print_diagnostics());
    if source_files.iter().any(|source| source.has_errors()) {
        println!("\nnot compiling due to previous errors");
        exit(1);
    }

    let (main_file_name, main_module) = main_modules.first().unwrap();

    let parse_finish = compilation_start.elapsed();

    println!(
        "{ANSI_GREEN}Finalizing{ANSI_RESET} (parsed in {:.2}s)",
        parse_finish.as_secs_f32()
    );
    let interner = interner.borrow_mut();
    match codegen::compile(
        &main_file_name,
        verbose >= 1,
        hir::Fqn {
            module: *main_module,
            name: main_fn,
        },
        &resolved_arena.borrow(),
        &interner,
        &bodies_map.borrow(),
        &tys_map.borrow(),
        &world_index.borrow(),
    ) {
        Ok(output) => {
            let output_folder = env::current_dir().unwrap().join("out");
            let file = output_folder.join(&format!("{}.o", interner.lookup(main_module.0)));
            fs::write(&file, output.as_slice()).unwrap_or_else(|why| {
                println!("{}: {why}", file.display());
                exit(1);
            });

            let exec = codegen::link_to_exec(&file);
            let full_finish = compilation_start.elapsed();
            println!(
                "{ANSI_GREEN}Finished{ANSI_RESET}   {} ({}) in {:.2}s",
                interner.lookup(main_module.0),
                exec.display(),
                full_finish.as_secs_f32(),
            );

            if !should_run {
                return Ok(());
            }
            println!("{ANSI_GREEN}Running{ANSI_RESET}    `{}`\n", exec.display());
            match std::process::Command::new(exec).status() {
                Ok(status) => {
                    println!("\nProcess exited with {}", status.to_string());
                }
                Err(why) => {
                    println!("\nProcess exited early: {}", why.to_string());
                }
            }
        }
        Err(why) => println!("Error Compiling with LLVM: {why}"),
    }

    Ok(())
}

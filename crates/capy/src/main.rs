mod source;

use std::{cell::RefCell, env, io, process::exit, rc::Rc, time::Instant};

use clap::{Parser, Subcommand};
use hir::WorldIndex;
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
    Build {
        #[arg(required = true)]
        files: Vec<String>,

        #[arg(short, long, default_value_t = 0, action = clap::ArgAction::Count)]
        verbose: u8,
    },
    Run {
        #[arg(required = true)]
        files: Vec<String>,

        #[arg(short, long, default_value_t = 0, action = clap::ArgAction::Count)]
        verbose: u8,
    },
}

const ANSI_RED: &str = "\x1B[1;91m";
const ANSI_GREEN: &str = "\x1B[1;92m";
const ANSI_WHITE: &str = "\x1B[1;97m";
const ANSI_RESET: &str = "\x1B[0m";

fn main() -> io::Result<()> {
    let config = CompilerConfig::parse();

    let (files, verbose, should_run) = match config.action {
        BuildAction::Build { files, verbose } => (files, verbose, false),
        BuildAction::Run { files, verbose } => (files, verbose, true),
    };

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

    compile_files(files, should_run, verbose)
}

fn compile_files(files: Vec<(String, String)>, should_run: bool, verbose: u8) -> io::Result<()> {
    println!("{ANSI_GREEN}Compiling{ANSI_RESET}  ...");
    let compilation_start = Instant::now();

    let interner = Rc::new(RefCell::new(interner::Interner::default()));
    let world_index = Rc::new(RefCell::new(WorldIndex::default()));
    let bodies_map = Rc::new(RefCell::new(FxHashMap::default()));
    let tys_map = Rc::new(RefCell::new(FxHashMap::default()));

    let mut source_files = Vec::new();
    for (file_name, contents) in files {
        source_files.push(SourceFile::parse(
            file_name.clone(),
            contents.clone(),
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

    let main_modules = source_files
        .iter()
        .filter(|source| source.has_main())
        .map(|source| (source.file_name.clone(), source.module))
        .collect::<Vec<_>>();
    if main_modules.is_empty() {
        println!("{ANSI_RED}error{ANSI_WHITE}: there is no main function{ANSI_RESET}");
    } else if main_modules.len() > 1 {
        println!("{ANSI_RED}error{ANSI_WHITE}: there are multiple main functions{ANSI_RESET}");
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

    let main_fn = hir::Name(interner.borrow_mut().intern("main"));
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
        &interner,
        &bodies_map.borrow_mut(),
        &tys_map.borrow_mut(),
        &world_index.borrow_mut(),
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

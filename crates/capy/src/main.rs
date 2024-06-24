mod git;
mod source;

use std::{
    cell::RefCell, env, ffi::CString, io, mem, panic::AssertUnwindSafe, path::PathBuf,
    process::exit, rc::Rc, str::FromStr, time::Instant,
};

use clap::{Parser, Subcommand};
use codegen::Verbosity;
use hir::{FQComptime, WorldBodies, WorldIndex};
use hir_ty::{ComptimeResult, InferenceResult};
use interner::Interner;
use itertools::Itertools;
use line_index::LineIndex;
use path_clean::PathClean;
use platform_dirs::AppDirs;
use rustc_hash::FxHashMap;
use std::fs;
use target_lexicon::Triple;
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

        /// The final executable name. This doesn't need a file extension
        #[arg(short, long)]
        output: Option<String>,

        /// The directory to search for modules.
        /// If this folder does not contain `core` it will be downloaded
        #[arg(long)]
        mod_dir: Option<String>,

        /// Whether or not to redownload the `core` module from the GitHub.
        /// WARNING: This will wipe the entire `core` folder.
        #[arg(long)]
        redownload_core: bool,

        /// Whether or not to show advanced compiler information
        #[arg(short, long, default_value_t = 0, action = clap::ArgAction::Count)]
        verbose: u8,

        /// Libraries to link against
        /// This literally works by passing the args to gcc with "-l"
        #[arg(long)]
        libs: Vec<String>,

        /// This needs to be here due to the way the `get_build_config` macro works, but it's
        /// skipped so that clap can still give an error if it's found
        #[arg(skip)]
        args: Vec<String>,
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

        /// The final executable name. This doesn't need a file extension
        #[arg(short, long)]
        output: Option<String>,

        /// The directory to search for modules.
        /// If this folder does not contain `core` it will be downloaded
        #[arg(long)]
        mod_dir: Option<String>,

        /// Whether or not to redownload the `core` module from the GitHub.
        /// WARNING: This will wipe the entire `core` folder.
        #[arg(long)]
        redownload_core: bool,

        /// Whether or not to show advanced compiler information
        #[arg(short, long, default_value_t = 0, action = clap::ArgAction::Count)]
        verbose: u8,

        /// Libraries to link against
        /// This literally works by passing the args to gcc with "-l"
        #[arg(long)]
        libs: Vec<String>,

        /// A list of arguments to feed into the capy program.
        /// These are accessable from the `args` global in `core`.
        /// Like Cargo, this can be passed in by using `--`
        #[arg(last = true)]
        args: Vec<String>,
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

    let (file, entry_point, output, verbose, mod_dir, redownload_core, libs, args, config) = get_build_config!(config.action => file, entry_point, output, verbose, mod_dir, redownload_core, libs, args);

    let file = env::current_dir()
        .unwrap()
        .join(file.replace(['/', '\\'], std::path::MAIN_SEPARATOR_STR))
        .clean();

    let contents = match fs::read_to_string(&file) {
        Ok(contents) => contents,
        Err(why) => {
            println!("{}: {}", file.display(), why);
            exit(1)
        }
    };

    compile_file(
        file,
        contents,
        entry_point,
        output,
        mod_dir,
        redownload_core,
        config,
        verbose,
        &libs,
        &args,
    )
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

#[allow(clippy::too_many_arguments)]
fn compile_file(
    file_name: PathBuf,
    file_contents: String,
    entry_point: String,
    output: Option<String>,
    mod_dir: Option<String>,
    redownload_core: bool,
    config: CompilationConfig,
    verbose: u8,
    libs: &[String],
    args: &[String],
) -> io::Result<()> {
    let with_color = supports_color::on(supports_color::Stream::Stdout).is_some();
    let (ansi_red, ansi_green, ansi_white, ansi_reset) = if with_color {
        (ANSI_RED, ANSI_GREEN, ANSI_WHITE, ANSI_RESET)
    } else {
        ("", "", "", "")
    };

    let mod_dir = if let Some(mod_dir) = mod_dir {
        env::current_dir().unwrap().join(mod_dir).clean()
    } else if let Some(mod_dir) = AppDirs::new(Some("capy"), false) {
        mod_dir.data_dir.join("modules")
    } else {
        PathBuf::new()
            .join(std::path::MAIN_SEPARATOR_STR)
            .join("capy")
            .join("modules")
            .clean()
    };

    let core_dir = mod_dir.join("core");

    if redownload_core && core_dir.exists() {
        std::fs::remove_dir_all(&core_dir)
            .unwrap_or_else(|why| panic!("couldn't detele `{}`: {}", core_dir.display(), why));
    }

    if !core_dir.exists() {
        println!(
            "{ansi_green}Downloading{ansi_reset}: {}",
            core_dir.display()
        );
        fs::create_dir_all(&mod_dir)
            .unwrap_or_else(|why| panic!("couldn't create `{}`: {}", mod_dir.display(), why));
        git::download_core(&mod_dir);
    }

    if output
        .as_ref()
        .map(|o| o.contains(['/', '\\']))
        .unwrap_or(false)
    {
        println!("{ansi_red}error{ansi_white}: the output cannot contain file separators");
        exit(1)
    }

    if !file_name.to_string_lossy().ends_with(".capy") {
        println!("{ansi_red}error{ansi_white}: capy files must end in `.capy`{ansi_reset}");
        exit(1)
    }

    let target = match &config {
        CompilationConfig::Compile(target) => target.as_deref(),
        _ => None,
    }
    .map(|target| {
        Triple::from_str(target).unwrap_or_else(|msg| {
            println!("invalid target: {}", msg);
            exit(1);
        })
    })
    .unwrap_or_else(Triple::host);

    println!("{ansi_green}Compiling{ansi_reset}  ...");
    let compilation_start = Instant::now();

    let interner = Rc::new(RefCell::new(interner::Interner::default()));
    let world_index = Rc::new(RefCell::new(WorldIndex::default()));
    let world_bodies = Rc::new(RefCell::new(WorldBodies::default()));
    let uid_gen = Rc::new(RefCell::new(UIDGenerator::default()));

    let entry_point_name = hir::Name(interner.borrow_mut().intern(&entry_point));

    let mut line_indexes = FxHashMap::default();
    let mut source_files = FxHashMap::default();

    // parse the first source file given in the `capy` command

    let mut source_file = SourceFile::parse(
        file_name.clone(),
        file_contents.clone(),
        uid_gen.clone(),
        interner.clone(),
        world_index.clone(),
        world_bodies.clone(),
        &mod_dir,
        verbose,
    );

    line_indexes.insert(source_file.module, LineIndex::new(&file_contents));

    let mut current_imports = source_file.build_bodies(&mod_dir);
    source_files.insert(source_file.module, source_file);

    // find all imports in the source file, compile them, then do the same for their imports

    while !current_imports.is_empty() {
        let old_imports = mem::take(&mut current_imports);
        for file_name in old_imports {
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

            let mut source_file = SourceFile::parse(
                file_name,
                file_contents.clone(),
                uid_gen.clone(),
                interner.clone(),
                world_index.clone(),
                world_bodies.clone(),
                &mod_dir,
                verbose,
            );

            line_indexes.insert(source_file.module, LineIndex::new(&file_contents));

            let imports = source_file.build_bodies(&mod_dir);
            current_imports.extend(imports);

            source_files.insert(source_file.module, source_file);
        }
    }

    // infer types
    let main_files = source_files
        .iter()
        .filter(|(_, sf)| sf.has_fn_of_name(entry_point_name))
        .map(|(name, _)| *name)
        .collect_vec();
    let main_file = main_files.first();
    let entry_point = main_file.map(|file| hir::Fqn {
        file: *file,
        name: entry_point_name,
    });

    let mut comptime_results = FxHashMap::<FQComptime, ComptimeResult>::default();

    let InferenceResult {
        tys,
        diagnostics: ty_diagnostics,
        any_were_unsafe_to_compile,
    } = hir_ty::InferenceCtx::new(
        &world_index.borrow(),
        &world_bodies.borrow(),
        &interner.borrow(),
        |comptime, tys| {
            if let Some(result) = comptime_results.get(&comptime) {
                return result.clone();
            }

            let interner = interner.borrow();
            let world_bodies = world_bodies.borrow();

            let interner: &Interner = &interner;
            let world_bodies: &hir::WorldBodies = &world_bodies;

            if verbose >= 4 {
                println!("comptime JIT:\n");
            }

            // todo: i kinda did AssertUnwindSafe bc i wanted to get rid of the error.
            // i *think* it should be fine.
            std::panic::catch_unwind(AssertUnwindSafe(|| {
                codegen::eval_comptime_blocks(
                    if verbose >= 4 {
                        Verbosity::AllFunctions
                    } else {
                        Verbosity::None
                    },
                    vec![comptime],
                    &mut comptime_results,
                    &mod_dir,
                    interner,
                    world_bodies,
                    tys,
                    target.pointer_width().unwrap().bits(),
                )
            }))
            .unwrap_or_else(|_| {
                println!(
                    "\n{ansi_red}error{ansi_white}: comptime compilation panicked{ansi_reset}"
                );
                std::process::exit(1);
            });

            comptime_results[&comptime].clone()
        },
    )
    .finish(entry_point, verbose >= 3);

    if verbose >= 2 {
        let debug = tys.debug(&mod_dir, &interner.borrow(), verbose >= 3, true);
        println!("=== types ===\n");
        println!("{}", debug);

        if any_were_unsafe_to_compile {
            println!("\nSOMETHING WAS UNSAFE TO COMPILE");
        }
    }

    // print out errors and warnings

    let has_errors = ty_diagnostics.iter().any(hir_ty::TyDiagnostic::is_error)
        || source_files.iter().any(|(_, source)| source.has_errors());
    source_files
        .iter()
        .for_each(|(_, source)| source.print_diagnostics(&mod_dir, with_color));
    for d in ty_diagnostics {
        let line_index = &line_indexes[&d.file];
        let source_file = &source_files[&d.file];

        println!(
            "{}",
            diagnostics::Diagnostic::from_ty(d)
                .display(
                    &source_file.file_name.to_string_lossy(),
                    &source_file.contents,
                    &mod_dir,
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

    // evaluate any comptimes that haven't been ran yet
    codegen::eval_comptime_blocks(
        if verbose >= 4 {
            Verbosity::AllFunctions
        } else {
            Verbosity::None
        },
        world_bodies.borrow().find_comptimes(),
        &mut comptime_results,
        &mod_dir,
        &interner.borrow(),
        &world_bodies.borrow(),
        &tys,
        target.pointer_width().unwrap().bits(),
    );

    match main_files.len().cmp(&1) {
        std::cmp::Ordering::Less => {
            println!(
                "{ansi_red}error{ansi_white}: there is no `{}` function{ansi_reset}",
                interner.borrow().lookup(entry_point_name.0)
            );
            std::process::exit(1);
        }
        std::cmp::Ordering::Equal => {}
        std::cmp::Ordering::Greater => {
            println!(
                "{ansi_red}error{ansi_white}: there are multiple `{}` functions{ansi_reset}",
                interner.borrow().lookup(entry_point_name.0)
            );
            std::process::exit(1);
        }
    }

    let parse_finish = compilation_start.elapsed();

    // frontend stuff is finally over
    // now we can actually compile it

    println!(
        "{ansi_green}Finalizing{ansi_reset} (parsed in {:.2}s)",
        parse_finish.as_secs_f32()
    );

    let interner = interner.borrow();

    if verbose >= 4 {
        println!("\nactual program:\n");
    }

    let comp_verbosity = if verbose >= 4 {
        Verbosity::AllFunctions
    } else if verbose >= 1 {
        Verbosity::LocalFunctions
    } else {
        Verbosity::None
    };

    if config == CompilationConfig::Jit {
        let jit_fn = codegen::compile_jit(
            comp_verbosity,
            entry_point.unwrap(),
            &mod_dir,
            &interner,
            &world_bodies.borrow(),
            &tys,
            &comptime_results,
        );

        println!(
            "{ansi_green}Finished{ansi_reset}   {} (JIT) in {:.2}s",
            main_file.unwrap().to_string(&mod_dir, &interner),
            compilation_start.elapsed().as_secs_f32(),
        );
        print!(
            "{ansi_green}Running{ansi_reset}    `{}",
            main_file.unwrap().to_string(&mod_dir, &interner)
        );
        for arg in args {
            print!(" {arg}");
        }
        println!("`\n");

        // convert `args` to a list of cstrings bc the jit_fn is a C main function
        let args = ["capy-run-jit"]
            .into_iter()
            .chain(args.iter().map(|a| a.as_str()))
            .map(|arg| match CString::new(arg.as_bytes()) {
                Ok(cstr) => cstr,
                Err(why) => {
                    println!("error passing {:?} as an argument: {why}", arg);
                    exit(1);
                }
            })
            .collect_vec();
        // do this separately so that the pointers don't dangle
        let args = args.iter().map(|arg| arg.as_ptr()).collect_vec();

        let status = jit_fn(args.len(), args.as_ptr());
        println!("\nProcess exited with {}", status);

        return Ok(());
    }

    let bytes = match codegen::compile_obj(
        comp_verbosity,
        entry_point.unwrap(),
        &mod_dir,
        &interner,
        &world_bodies.borrow(),
        &tys,
        &comptime_results,
        target.clone(),
    ) {
        Ok(bytes) => bytes,
        Err(why) => {
            println!("Cranelift Error: {}", why);
            return Ok(());
        }
    };

    // let output_folder = env::current_dir().unwrap().join("out");
    let output_folder = PathBuf::from("out");

    let _ = fs::create_dir(&output_folder);

    let output = output.unwrap_or_else(|| {
        let main_file = std::path::PathBuf::from(interner.lookup(main_file.unwrap().0));
        main_file.file_stem().unwrap().to_string_lossy().to_string()
    });
    let mut object_file = output_folder.join(&output);
    object_file.set_extension("o");
    fs::write(&object_file, bytes.as_slice()).unwrap_or_else(|why| {
        println!("{}: {why}", object_file.display());
        exit(1);
    });

    if let CompilationConfig::Compile(Some(target)) = config {
        println!(
            "{ansi_green}Finished{ansi_reset}   {} ({}) in {:.2}s",
            object_file.display(),
            target,
            compilation_start.elapsed().as_secs_f32(),
        );
        return Ok(());
    }

    let exec = codegen::link_to_exec(&object_file, target, libs);
    println!(
        "{ansi_green}Finished{ansi_reset}   {} ({}) in {:.2}s",
        output,
        exec.display(),
        compilation_start.elapsed().as_secs_f32(),
    );

    if matches!(config, CompilationConfig::Compile(_)) {
        return Ok(());
    }

    print!("{ansi_green}Running{ansi_reset}    `{}", exec.display(),);
    for arg in args {
        print!(" {arg}");
    }
    println!("`\n");

    match std::process::Command::new(exec).args(args).status() {
        Ok(status) => {
            println!("\nProcess exited with {}", status);
        }
        Err(why) => {
            println!("\nProcess exited early: {}", why);
        }
    }

    Ok(())
}

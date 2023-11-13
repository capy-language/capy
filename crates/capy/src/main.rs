mod git;
mod source;

use std::{
    cell::RefCell, env, io, mem, path::PathBuf, process::exit, rc::Rc, str::FromStr, time::Instant,
};

use clap::{Parser, Subcommand};
use codegen::Verbosity;
use hir::WorldIndex;
use itertools::Itertools;
use line_index::LineIndex;
use path_clean::PathClean;
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

        /// Whether or not to show advanced compiler information
        #[arg(short, long, default_value_t = 0, action = clap::ArgAction::Count)]
        verbose: u8,

        /// libraries to link against
        /// this literally works by passing the args to gcc with "-l"
        #[arg(long)]
        libs: Option<Vec<String>>,
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

        /// Whether or not to show advanced compiler information
        #[arg(short, long, default_value_t = 0, action = clap::ArgAction::Count)]
        verbose: u8,

        /// libraries to link against
        /// this literally works by passing the args to gcc with "-l"
        #[arg(long)]
        libs: Option<Vec<String>>,
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

    let (file, entry_point, output, verbose, mod_dir, libs, config) =
        get_build_config!(config.action => file, entry_point, output, verbose, mod_dir, libs);

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
        config,
        verbose,
        libs.as_deref(),
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
    config: CompilationConfig,
    verbose: u8,
    libs: Option<&[String]>,
) -> io::Result<()> {
    let with_color = supports_color::on(supports_color::Stream::Stdout).is_some();
    let (ansi_red, ansi_green, ansi_white, ansi_reset) = if with_color {
        (ANSI_RED, ANSI_GREEN, ANSI_WHITE, ANSI_RESET)
    } else {
        ("", "", "", "")
    };

    let mod_dir = if let Some(mod_dir) = mod_dir {
        env::current_dir().unwrap().join(mod_dir).clean()
    } else {
        PathBuf::new()
            .join(std::path::MAIN_SEPARATOR_STR)
            .join("capy")
            .join("modules")
            .clean()
    };
    let core_dir = mod_dir.join("core");
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
    let bodies_map = Rc::new(RefCell::new(FxHashMap::default()));
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
        bodies_map.clone(),
        world_index.clone(),
        verbose,
    );

    line_indexes.insert(source_file.module, LineIndex::new(&file_contents));

    let (mut current_imports, mut comptimes) = source_file.build_bodies(&mod_dir);
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
                bodies_map.clone(),
                world_index.clone(),
                verbose,
            );

            line_indexes.insert(source_file.module, LineIndex::new(&file_contents));

            let (imports, new_comptimes) = source_file.build_bodies(&mod_dir);
            current_imports.extend(imports);
            comptimes.extend(new_comptimes);

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

    let (inference, ty_diagnostics) = hir_ty::InferenceCtx::new(
        &bodies_map.borrow(),
        &world_index.borrow(),
        &interner.borrow(),
    )
    .finish(entry_point);
    if verbose >= 2 {
        let debug = inference.debug(&mod_dir, &interner.borrow(), true);
        println!("=== types ===\n");
        println!("{}", debug);
    }

    // print out errors and warnings

    let has_errors = ty_diagnostics.iter().any(hir_ty::TyDiagnostic::is_error)
        || source_files.iter().any(|(_, source)| source.has_errors());
    source_files
        .iter()
        .for_each(|(_, source)| source.print_diagnostics(&mod_dir, with_color));
    for d in ty_diagnostics {
        let line_index = &line_indexes[&d.module];
        let source_file = &source_files[&d.module];

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
        println!("comptime JIT:\n");
    }

    let comptime_results = codegen::eval_comptime_blocks(
        if verbose >= 4 {
            Verbosity::AllFunctions
        } else {
            Verbosity::None
        },
        comptimes,
        &mod_dir,
        &interner,
        &bodies_map.borrow(),
        &inference,
        target.pointer_width().unwrap().bits(),
    );

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
            &bodies_map.borrow(),
            &inference,
            &comptime_results,
        );

        println!(
            "{ansi_green}Finished{ansi_reset}   {} (JIT) in {:.2}s",
            main_file.unwrap().to_string(&mod_dir, &interner),
            compilation_start.elapsed().as_secs_f32(),
        );
        println!(
            "{ansi_green}Running{ansi_reset}    `{}`\n",
            main_file.unwrap().to_string(&mod_dir, &interner)
        );
        let status = jit_fn(0, 0);
        println!("\nProcess exited with {}", status);

        return Ok(());
    }

    let bytes = match codegen::compile_obj(
        comp_verbosity,
        entry_point.unwrap(),
        &mod_dir,
        &interner,
        &bodies_map.borrow(),
        &inference,
        &comptime_results,
        target,
    ) {
        Ok(bytes) => bytes,
        Err(why) => {
            println!("Cranelift Error: {}", why);
            return Ok(());
        }
    };

    let output_folder = env::current_dir().unwrap().join("out");

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

    let exec = codegen::link_to_exec(&object_file, libs);
    println!(
        "{ansi_green}Finished{ansi_reset}   {} ({}) in {:.2}s",
        output,
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

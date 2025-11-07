#![allow(clippy::uninlined_format_args)]
#![allow(clippy::too_many_arguments)]

mod git;
mod source;

#[cfg(unix)]
use std::os::unix::process::ExitStatusExt;
use std::{
    cell::RefCell,
    env,
    ffi::CString,
    io::{self, Write},
    mem,
    panic::AssertUnwindSafe,
    path::PathBuf,
    process::exit,
    rc::Rc,
    str::FromStr,
    time::Instant,
};

use clap::{ColorChoice, Parser, Subcommand};
use enum_display::EnumDisplay;
use hir::{
    WorldBodies, WorldIndex,
    common::{ComptimeResultMap, Fqn, Name},
};
use hir_ty::InferenceResult;
use interner::Interner;
use itertools::Itertools;
use la_arena::Arena;
use line_index::LineIndex;
use path_clean::PathClean;
use platform_dirs::AppDirs;
use rustc_hash::FxHashMap;
use std::fs;
use target_lexicon::{OperatingSystem, Triple};
use uid_gen::UIDGenerator;

use crate::source::SourceFile;

macro_rules! create_build_action {
    (
        $name:ident:
        both { $($both_field:tt)+ }
        #[$build_attr:meta]
        build_only { $($build_field:tt)+ }
        #[$run_attr:meta]
        run_only { $($run_field:tt)+ }
        final_config_struct = $final_config_struct:ident
        compile_mode_enum = $compile_mode_enum:ident
        build_specific_struct = $build_specific_struct:ident
        run_specific_struct = $run_specific_struct:ident
    ) => {
        #[derive(Debug, Subcommand)]
        enum $name {
            #[$build_attr]
            Build {
                $($both_field)+
                $($build_field)+
            },
            #[$run_attr]
            Run {
                $($both_field)+
                $($run_field)+
            }
        }

        impl $name {
            fn into_final_config(self) -> $final_config_struct {
                create_build_action!(
                    @into_match
                    both {
                        $($both_field)+
                    }
                    build_only {
                        $($build_field)+
                    }
                    run_only {
                        $($run_field)+
                    }
                    self => $final_config_struct ($compile_mode_enum: $build_specific_struct, $run_specific_struct)
                )
            }
        }

        create_build_action!(@make_struct $final_config_struct {
            $($both_field)+
            specific: $compile_mode_enum,
        });

        create_build_action!(@make_struct $build_specific_struct {
            $($build_field)+,
        });

        create_build_action!(@make_struct $run_specific_struct {
            $($run_field)+,
        });

        #[derive(Debug)]
        enum $compile_mode_enum {
            Build($build_specific_struct),
            Run($run_specific_struct),
        }
    };
    (@make_struct $name:ident { } -> ($($result:tt)*) ) => (
        #[derive(Debug)]
        struct $name {
            $($result)*
        }
    );
    (@make_struct $name:ident { $param:ident : $type:ty, $($rest:tt)* } -> ($($result:tt)*) ) => (
        create_build_action!(@make_struct $name { $($rest)* } -> (
            $($result)*
            $param : $type,
        ));
    );
    (@make_struct $name:ident { $( $(#[$_:meta])* $param:ident : $type:ty ),* $(,)* } ) => (
        create_build_action!(@make_struct $name { $($param : $type,)* } -> ());
    );
    (
        @into_match
        both { $( $(#[$_attr1:meta])* $both_param:ident : $_type1:ty ),* $(,)* }
        build_only { $( $(#[$_attr2:meta])* $build_param:ident : $_type2:ty ),* $(,)* }
        run_only { $( $(#[$_attr3:meta])* $run_param:ident : $_type3:ty ),* $(,)* }
        $value:expr => $into_struct:ident ($config_enum:ident: $build_only_struct:ident, $run_only_struct:ident)
    ) => (
        match $value {
            Self::Build {
                $($both_param,)+
                $($build_param,)+
            } => $into_struct {
                $($both_param,)+
                specific: $config_enum::Build($build_only_struct {
                    $($build_param,)+
                })
            },
            Self::Run {
                $($both_param,)+
                $($run_param,)+
            } => $into_struct {
                $($both_param,)+
                specific: $config_enum::Run($run_only_struct {
                    $($run_param,)+
                })
            }
        }
    )
}

#[derive(Debug, Parser)]
#[command(name = "Capy Programming Language")]
#[command(author = "NotAFlyingGoose <notaflyinggoose@gmail.com>")]
#[command(version)]
#[command(about = "A statically typed, compiled programming language, largely inspired by Jai, Odin, and Zig", long_about = None)]
struct CLIConfig {
    #[command(subcommand)]
    action: CLIAction,
}

create_build_action! {
    CLIAction:
    both {
        /// The file to compile
        #[arg(required = true)]
        file: String,

        /// The entry point function of the program
        #[arg(long, default_value = "main")]
        entry_point: String,

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

        /// Shows the generated AST (Abstract Syntax Tree).
        #[arg(long, default_value_t)]
        verbose_ast: VerboseScope,

        /// Shows the generated HIR for every global.
        #[arg(long, default_value_t)]
        verbose_hir: VerboseScope,

        /// Shows type information for each HIR expression in the program.
        #[arg(long, default_value_t)]
        verbose_types: VerboseScope,

        /// Shows the generated Cranelift IR (or assembly) of comptime blocks.
        #[arg(long, default_value_t)]
        verbose_comptime: VerboseCodegenScope,

        /// Shows the generated Cranelift IR (or assembly) of the final binary.
        #[arg(long, default_value_t)]
        verbose_binary: VerboseCodegenScope,

        /// Shows all available advanced compiler information.
        #[arg(long)]
        verbose_all: bool,

        /// Sets the color output of the program
        #[arg(long, default_value_t = ColorChoice::Auto)]
        color: ColorChoice,

        /// Will skip building the final executable binary and only output a .o file
        #[arg(long)]
        no_exec: bool,

        /// Libraries to link against.
        /// This literally works by passing the args to gcc with "-l"
        #[arg(long)]
        libs: Vec<String>,
    }
    /// Takes in one or more .capy files and compiles them
    build_only {
        /// The target to compile for. If supplied, no linking will be done
        #[arg(long)]
        target: Option<String>,
    }
    /// Takes in one or more .capy files, compiles them, and runs the compiled executable
    run_only {
        /// Whether or not to run by JIT instead of by building and running an executable
        #[arg(long)]
        jit: bool,

        /// A list of arguments to feed into the capy program.
        /// These are accessable from the `args` global in `core`.
        /// Like Cargo, this can be passed in by using `--`
        #[arg(last = true, verbatim_doc_comment)]
        args: Vec<String>,
    }
    final_config_struct = FinalConfig
    compile_mode_enum = CompileMode
    build_specific_struct = BuildSpecific
    run_specific_struct = RunSpecific
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, clap::ValueEnum, Default, EnumDisplay)]
#[clap(rename_all = "kebab_case")]
#[enum_display(case = "Kebab")]
pub(crate) enum VerboseCodegenScope {
    #[default]
    None,
    Local,
    LocalAsm,
    All,
    AllAsm,
}

impl VerboseCodegenScope {
    fn into_verbosity(self) -> codegen::Verbosity {
        match self {
            VerboseCodegenScope::None => codegen::Verbosity::None,
            VerboseCodegenScope::Local => codegen::Verbosity::LocalFunctions {
                include_disasm: false,
            },
            VerboseCodegenScope::LocalAsm => codegen::Verbosity::LocalFunctions {
                include_disasm: true,
            },
            VerboseCodegenScope::All => codegen::Verbosity::AllFunctions {
                include_disasm: false,
            },
            VerboseCodegenScope::AllAsm => codegen::Verbosity::AllFunctions {
                include_disasm: true,
            },
        }
    }

    fn is_none(self) -> bool {
        self == Self::None
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, clap::ValueEnum, EnumDisplay)]
#[clap(rename_all = "kebab_case")]
#[enum_display(case = "Kebab")]
pub(crate) enum VerboseScope {
    #[default]
    None,
    Local,
    All,
}

impl VerboseScope {
    fn should_show(self, is_mod: bool) -> bool {
        match self {
            Self::None => false,
            Self::Local => !is_mod,
            Self::All => true,
        }
    }

    fn is_none(self) -> bool {
        self == Self::None
    }
}

impl FinalConfig {
    fn should_run(&self) -> bool {
        matches!(self.specific, CompileMode::Run(_))
    }

    fn should_jit(&self) -> bool {
        matches!(
            self.specific,
            CompileMode::Run(RunSpecific { jit: true, .. })
        )
    }

    fn target(&self) -> Triple {
        match &self.specific {
            CompileMode::Build(BuildSpecific {
                target: Some(target),
                ..
            }) => Triple::from_str(target).unwrap_or_else(|msg| {
                println!("invalid target: {}", msg);
                exit(1);
            }),
            CompileMode::Build(BuildSpecific { target: None, .. }) | CompileMode::Run(_) => {
                Triple::host()
            }
        }
    }

    fn args(&self) -> &[String] {
        match &self.specific {
            CompileMode::Run(RunSpecific { args, .. }) => args,
            CompileMode::Build(_) => &[],
        }
    }
}

fn main() -> io::Result<()> {
    let config = CLIConfig::parse();

    compile_file(config.action.into_final_config())
}

const ANSI_RED: &str = "\x1B[1;91m";
const ANSI_GREEN: &str = "\x1B[1;92m";
const ANSI_WHITE: &str = "\x1B[1;97m";
const ANSI_RESET: &str = "\x1B[0m";

fn compile_file(mut config: FinalConfig) -> io::Result<()> {
    if config.verbose_all {
        if config.verbose_ast.is_none() {
            config.verbose_ast = VerboseScope::All;
        }
        if config.verbose_hir.is_none() {
            config.verbose_hir = VerboseScope::All;
        }
        if config.verbose_types.is_none() {
            config.verbose_types = VerboseScope::All;
        }
        if config.verbose_comptime.is_none() {
            config.verbose_comptime = VerboseCodegenScope::AllAsm;
        }
        if config.verbose_binary.is_none() {
            config.verbose_binary = VerboseCodegenScope::AllAsm;
        }
    }

    let file_name = env::current_dir()
        .unwrap()
        .join(
            config
                .file
                .replace(['/', '\\'], std::path::MAIN_SEPARATOR_STR),
        )
        .clean();

    let file_contents = match fs::read_to_string(&file_name) {
        Ok(contents) => contents,
        Err(why) => {
            println!("{}: {}", file_name.display(), why);
            exit(1)
        }
    };

    let with_color = match config.color {
        ColorChoice::Auto => supports_color::on(supports_color::Stream::Stdout).is_some(),
        ColorChoice::Always => true,
        ColorChoice::Never => false,
    };
    let (ansi_red, ansi_green, ansi_white, ansi_reset) = if with_color {
        (ANSI_RED, ANSI_GREEN, ANSI_WHITE, ANSI_RESET)
    } else {
        ("", "", "", "")
    };

    let mod_dir = if let Some(mod_dir) = &config.mod_dir {
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

    if config.redownload_core && core_dir.exists() {
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

    if config
        .output
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

    let target = config.target();

    println!("{ansi_green}Compiling{ansi_reset}  ...");
    let compilation_start = Instant::now();

    let interner = Rc::new(RefCell::new(interner::Interner::default()));
    let world_index = Rc::new(RefCell::new(WorldIndex::default()));
    let world_bodies = Rc::new(RefCell::new(WorldBodies::default()));
    let uid_gen = Rc::new(RefCell::new(UIDGenerator::default()));

    let entry_point_name = Name(interner.borrow_mut().intern(&config.entry_point));

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
        config.verbose_hir,
        config.verbose_ast,
        config.verbose_types,
        with_color,
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
                config.verbose_hir,
                config.verbose_ast,
                config.verbose_types,
                with_color,
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
    let entry_point = main_file.map(|file| Fqn {
        file: *file,
        name: entry_point_name,
    });

    let comptime_verbosity = config.verbose_comptime.into_verbosity();

    let mut comptime_results = ComptimeResultMap::default();

    let mut generic_values = Arena::new();

    let InferenceResult {
        tys,
        diagnostics: ty_diagnostics,
        any_were_unsafe_to_compile,
    } = hir_ty::InferenceCtx::new(
        &world_index.borrow(),
        &world_bodies.borrow(),
        &interner.borrow(),
        &mut generic_values,
        |comptime, tys| {
            if let Some(result) = comptime_results.get(comptime) {
                return result.clone();
            }

            let interner = interner.borrow();
            let world_bodies = world_bodies.borrow();

            let interner: &Interner = &interner;
            let world_bodies: &hir::WorldBodies = &world_bodies;

            let is_mod = comptime.loc.file().is_mod(&mod_dir, interner);
            if comptime_verbosity.should_show(is_mod) {
                println!("comptime JIT:\n");
            }

            // todo: i kinda did AssertUnwindSafe bc i wanted to get rid of the error.
            // i *think* it should be fine.
            std::panic::catch_unwind(AssertUnwindSafe(|| {
                codegen::eval_comptime_blocks(
                    comptime_verbosity,
                    &mut std::iter::once(comptime),
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

            comptime_results[comptime].clone()
        },
    )
    .finish(entry_point, !config.verbose_types.is_none());

    if !config.verbose_types.is_none() {
        let debug = tys.debug(
            &mod_dir,
            &interner.borrow(),
            config.verbose_types == VerboseScope::All,
            with_color,
        );
        println!("=== types ===\n");
        println!("{}", debug);

        if any_were_unsafe_to_compile {
            println!("SOMETHING WAS UNSAFE TO COMPILE");
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

    assert!(
        !any_were_unsafe_to_compile,
        "some things were marked as unsafe to compile (which means they contained buggy or uncompilable code) and yet no errors were produced"
    );

    // evaluate any comptimes that haven't been ran yet
    codegen::eval_comptime_blocks(
        comptime_verbosity,
        &mut world_bodies.borrow().find_comptimes(),
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

    let final_verbosity = config.verbose_binary.into_verbosity();

    if final_verbosity != codegen::Verbosity::None {
        println!("\nactual program:\n");
    }

    if config.should_jit() {
        let jit_fn = codegen::compile_jit(
            final_verbosity,
            entry_point.unwrap().make_concrete(None),
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
        let args = config.args();
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
        final_verbosity,
        entry_point.unwrap().make_concrete(None),
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

    let output = config.output.clone().unwrap_or_else(|| {
        let main_file = std::path::PathBuf::from(interner.lookup(main_file.unwrap().0));
        main_file.file_stem().unwrap().to_string_lossy().to_string()
    });
    let mut object_file = output_folder.join(&output);
    object_file.set_extension("o");
    fs::write(&object_file, bytes.as_slice()).unwrap_or_else(|why| {
        println!("{}: {why}", object_file.display());
        exit(1);
    });

    if target != Triple::host() || config.no_exec {
        println!(
            "{ansi_green}Finished{ansi_reset}   {} ({}) in {:.2}s",
            object_file.display(),
            target,
            compilation_start.elapsed().as_secs_f32(),
        );
        return Ok(());
    }

    println!(
        "{ansi_green}Linking{ansi_reset}    (compiler took {:.2}s)",
        compilation_start.elapsed().as_secs_f32()
    );

    let exec = match codegen::link_to_exec(&object_file, &target, &config.libs) {
        Ok(exec) => {
            println!(
                "{ansi_green}Finished{ansi_reset}   {} ({}) in {:.2}s",
                output,
                exec.display(),
                compilation_start.elapsed().as_secs_f32(),
            );
            exec
        }
        Err(codegen::LinkingErr::NoCommand) => {
            println!(
                "{ansi_red}error{ansi_white}: capy requires either `zig` or `gcc` in order to link to an executable. use --no-exec if you only want the .o file"
            );
            exit(1)
        }
        Err(codegen::LinkingErr::IO(why)) => {
            println!("{ansi_red}error{ansi_white}: while trying to build the executable:\n{why}");
            exit(1)
        }
        Err(codegen::LinkingErr::CmdFailed { cmd_name, output }) => {
            println!("{cmd_name} stdout:");
            std::io::stdout().write_all(&output.stdout).unwrap();
            println!("{cmd_name} stderr:");
            std::io::stdout().write_all(&output.stderr).unwrap();
            println!(
                "{ansi_red}error{ansi_white}: {cmd_name} failed! ({})",
                output.status
            );
            exit(1)
        }
    };

    if !config.should_run() {
        return Ok(());
    }

    print!("{ansi_green}Running{ansi_reset}    `{}", exec.display(),);

    let args = config.args();
    for arg in args {
        print!(" {arg}");
    }
    println!("`\n");

    match std::process::Command::new(exec).args(args).status() {
        Ok(status) => {
            print!("\nProcess exited with {}", status);

            if let Some(code) = status.code() {
                let code = code as u32;

                match (target.operating_system, code) {
                    // https://learn.microsoft.com/en-us/openspecs/windows_protocols/ms-erref/596a1078-e883-4972-9bbc-49e60bebca55
                    (OperatingSystem::Windows, 0xC00000FD) => {
                        print!(" STATUS_STACK_OVERFLOW")
                    }
                    (OperatingSystem::Windows, 0xC000001D) => {
                        print!(" STATUS_ILLEGAL_INSTRUCTION")
                    }
                    (OperatingSystem::Windows, 0xC0000005) => {
                        print!(" STATUS_ACCESS_VIOLATION")
                    }
                    (OperatingSystem::Windows, _) if code & 0x80000000 != 0 => {
                        print!(" (unknown error code)");
                    }
                    _ => {}
                }
            }

            #[cfg(unix)]
            if let Some(signal) = status.signal() {
                match (target.operating_system, signal) {
                    // https://developer.apple.com/documentation/xcode/understanding-the-exception-types-in-a-crash-report
                    (OperatingSystem::Darwin(_), libc::SIGSEGV) => {
                        print!(" EXC_BAD_ACCESS");
                    }
                    (OperatingSystem::Darwin(_), libc::SIGBUS) => {
                        print!(" EXC_BAD_ACCESS");
                    }
                    (OperatingSystem::Darwin(_), libc::SIGTRAP) => {
                        print!(" EXC_BREAKPOINT");
                    }
                    (OperatingSystem::Darwin(_), libc::SIGILL) => {
                        print!(" EXC_BAD_INSTRUCTION");
                    }
                    _ => {}
                }
            }

            println!();
        }
        Err(why) => {
            println!("\nProcess exited early: {}", why);
        }
    }

    Ok(())
}

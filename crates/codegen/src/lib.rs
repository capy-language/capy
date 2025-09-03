#![allow(clippy::uninlined_format_args)]
#![allow(clippy::too_many_arguments)]

mod builtin;
mod compiler;
pub(crate) mod convert;
mod debug;
mod extend;
mod layout;
mod mangle;

#[cfg(test)]
mod tests;

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
    flag_builder.set("is_pic", "true").unwrap();

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
    target: &Triple,
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
    target: &Triple,
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

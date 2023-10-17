use hir::Fqn;
use interner::Interner;

use crate::{
    compiler::{comptime::ComptimeToCompile, FunctionToCompile},
    compiler_defined::CompilerDefinedFunction,
};

pub(crate) trait Mangle {
    fn to_mangled_name(&self, mod_dir: &std::path::Path, interner: &Interner) -> String;
}

impl Mangle for Fqn {
    fn to_mangled_name(&self, mod_dir: &std::path::Path, interner: &Interner) -> String {
        let mut mangled = "_C".to_string();

        push_file_name(&mut mangled, self.file, mod_dir, interner, 'N');

        let name_str = interner.lookup(self.name.0);
        mangled.push_str(&name_str.len().to_string());
        mangled.push_str(name_str);

        mangled.push('E');

        mangled
    }
}

impl Mangle for FunctionToCompile {
    fn to_mangled_name(&self, mod_dir: &std::path::Path, interner: &Interner) -> String {
        if let Some(name) = self.function_name {
            return hir::Fqn {
                file: self.file_name,
                name,
            }
            .to_mangled_name(mod_dir, interner);
        };

        let mut mangled = String::new();

        push_file_name(&mut mangled, self.file_name, mod_dir, interner, 'L');

        mangled.push_str("l_");
        mangled.push_str(&self.lambda.into_raw().to_string());

        mangled.push('E');

        mangled
    }
}

impl Mangle for ComptimeToCompile {
    fn to_mangled_name(&self, mod_dir: &std::path::Path, interner: &Interner) -> String {
        let mut mangled = String::new();

        push_file_name(&mut mangled, self.file_name, mod_dir, interner, 'Z');

        mangled.push_str("c_");
        mangled.push_str(&self.comptime.into_raw().to_string());

        mangled.push('E');

        mangled
    }
}

impl Mangle for CompilerDefinedFunction {
    fn to_mangled_name(&self, _: &std::path::Path, _: &Interner) -> String {
        let mut mangled = String::from("_CI");

        let name = match self {
            CompilerDefinedFunction::PtrBitcast => "ptr_bitcast",
        };
        mangled.push_str(&name.len().to_string());
        mangled.push_str(name);

        mangled.push('E');

        mangled
    }
}

fn push_file_name(
    mangled: &mut String,
    file_name: hir::FileName,
    mod_dir: &std::path::Path,
    interner: &Interner,
    final_letter: char,
) {
    let file_str = file_name.to_string(mod_dir, interner);

    let (mod_str, file_str) = file_str
        .split_once("::")
        .map(|(first, second)| (Some(first), second))
        .unwrap_or((None, &file_str));

    if mod_str.is_some() {
        mangled.push('M');
    }

    let parts = file_str.split('.').collect::<Vec<_>>();

    mangled.push_str(&format!("{}{}", "F".repeat(parts.len()), final_letter));

    if let Some(mod_str) = mod_str {
        mangled.push_str(&mod_str.len().to_string());
        mangled.push_str(mod_str);
    }

    for part in parts {
        mangled.push_str(&part.len().to_string());
        mangled.push_str(part);
    }
}

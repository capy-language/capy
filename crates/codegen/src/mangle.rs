use hir::Fqn;
use interner::Interner;

use crate::compiler::{comptime::ComptimeToCompile, LambdaToCompile};

pub(crate) trait Mangle {
    fn to_mangled_name(&self, project_root: &std::path::Path, interner: &Interner) -> String;
}

impl Mangle for Fqn {
    fn to_mangled_name(&self, project_root: &std::path::Path, interner: &Interner) -> String {
        let mut mangled = String::new();

        let module_str = self.module.to_string(project_root, interner);
        let parts = module_str.split('.').collect::<Vec<_>>();

        mangled.push_str(&format!("_C{}N", "M".repeat(parts.len())));

        for part in parts {
            mangled.push_str(&part.len().to_string());
            mangled.push_str(part);
        }

        let name_str = interner.lookup(self.name.0);
        mangled.push_str(&name_str.len().to_string());
        mangled.push_str(name_str);

        mangled.push('E');

        mangled
    }
}

impl Mangle for LambdaToCompile {
    fn to_mangled_name(&self, project_root: &std::path::Path, interner: &Interner) -> String {
        let mut mangled = String::new();

        let module_str = self.module_name.to_string(project_root, interner);
        let parts = module_str.split('.').collect::<Vec<_>>();

        mangled.push_str(&format!("_C{}L", "M".repeat(parts.len())));

        for part in parts {
            mangled.push_str(&part.len().to_string());
            mangled.push_str(part);
        }

        mangled.push_str("l_");
        mangled.push_str(&self.lambda.into_raw().to_string());

        mangled.push('E');

        mangled
    }
}

impl Mangle for ComptimeToCompile {
    fn to_mangled_name(&self, project_root: &std::path::Path, interner: &Interner) -> String {
        let mut mangled = String::new();

        let module_str = self.module_name.to_string(project_root, interner);
        let parts = module_str.split('.').collect::<Vec<_>>();

        mangled.push_str(&format!("_C{}C", "M".repeat(parts.len())));

        for part in parts {
            mangled.push_str(&part.len().to_string());
            mangled.push_str(part);
        }

        mangled.push_str("c_");
        mangled.push_str(&self.comptime.into_raw().to_string());

        mangled.push('E');

        mangled
    }
}

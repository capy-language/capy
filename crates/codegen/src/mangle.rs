use hir::Fqn;
use interner::Interner;

pub(crate) trait Mangle {
    fn to_mangled_name(&self, interner: &Interner) -> String;
}

impl Mangle for Fqn {
    fn to_mangled_name(&self, interner: &Interner) -> String {
        let mut mangled = String::new();

        mangled.push_str("_ZN");

        let module_str = interner.lookup(self.module.0);
        mangled.push_str(&module_str.len().to_string());
        mangled.push_str(module_str);

        let name_str = interner.lookup(self.name.0);
        mangled.push_str(&name_str.len().to_string());
        mangled.push_str(name_str);

        mangled.push('E');

        mangled
    }
}

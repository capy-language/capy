use hir::Fqn;
use interner::Interner;

pub(crate) trait Mangle {
    fn to_mangled_name(&self, interer: &Interner) -> String;
}

impl Mangle for Fqn {
    fn to_mangled_name(&self, interer: &Interner) -> String {
        let mut mangled = String::new();

        mangled.push_str("_ZN");

        let module_str = interer.lookup(self.module.0);
        mangled.push_str(&module_str.len().to_string());
        mangled.push_str(module_str);

        let name_str = interer.lookup(self.name.0);
        mangled.push_str(&name_str.len().to_string());
        mangled.push_str(name_str);

        mangled.push_str("E");

        mangled
    }
}

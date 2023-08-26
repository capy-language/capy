use hir::Fqn;
use interner::Interner;
use la_arena::Idx;

pub(crate) trait Mangle {
    fn to_mangled_name(&self, interner: &Interner) -> String;
}

impl Mangle for Fqn {
    fn to_mangled_name(&self, interner: &Interner) -> String {
        let mut mangled = String::new();

        mangled.push_str("_CMN");

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

impl Mangle for (hir::Name, Idx<hir::Lambda>) {
    fn to_mangled_name(&self, interner: &Interner) -> String {
        let mut mangled = String::new();

        mangled.push_str("_CML");

        let module_str = interner.lookup(self.0 .0);
        mangled.push_str(&module_str.len().to_string());
        mangled.push_str(module_str);

        mangled.push_str("l_");
        mangled.push_str(&self.1.into_raw().to_string());

        mangled.push('E');

        mangled
    }
}

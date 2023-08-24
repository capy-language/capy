use interner::Interner;
use text_size::TextRange;

use crate::{Fqn, Name};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Path {
    ThisModule(Name),
    OtherModule(Fqn),
}

impl Path {
    pub fn display(&self, interner: &Interner) -> String {
        match self {
            Path::ThisModule(name) => interner.lookup(name.0).to_string(),
            Path::OtherModule(fqn) => format!(
                "{}.{}",
                interner.lookup(fqn.module.0),
                interner.lookup(fqn.name.0)
            ),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum PathWithRange {
    ThisModule {
        name: Name,
        range: TextRange,
    },
    OtherModule {
        fqn: Fqn,
        module_range: TextRange,
        name_range: TextRange,
    },
}

impl PathWithRange {
    pub fn path(self) -> Path {
        match self {
            Self::ThisModule { name, .. } => Path::ThisModule(name),
            Self::OtherModule { fqn, .. } => Path::OtherModule(fqn),
        }
    }

    pub fn into_fqn(self, this_module: Name) -> Fqn {
        match self {
            PathWithRange::ThisModule { name, .. } => Fqn {
                module: this_module,
                name,
            },
            PathWithRange::OtherModule { fqn, .. } => fqn,
        }
    }
}

pub struct NameResDiagnostic {
    pub kind: NameResDiagnosticKind,
    pub range: TextRange,
}

pub enum NameResDiagnosticKind {
    Undefined(Name),
}

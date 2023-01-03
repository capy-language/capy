use text_size::TextRange;

use crate::{Name, Fqn};


#[derive(Debug, Clone, Copy)]
pub enum Path {
    ThisModule(Name),
    OtherModule(Fqn),
}

#[derive(Debug, Clone, Copy)]
pub enum PathWithRange {
    ThisModule { name: Name, range: TextRange },
    OtherModule { fqn: Fqn, module_range: TextRange, name_range: TextRange },
}

impl PathWithRange {
    pub fn path(self) -> Path {
        match self {
            Self::ThisModule { name, .. } => Path::ThisModule(name),
            Self::OtherModule { fqn, .. } => Path::OtherModule(fqn),
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


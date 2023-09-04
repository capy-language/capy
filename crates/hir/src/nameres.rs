use interner::Interner;
use text_size::TextRange;

use crate::{FileName, Fqn, Name};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Path {
    ThisModule(Name),
    OtherModule(Fqn),
}

impl Path {
    pub fn to_string(&self, project_root: &std::path::Path, interner: &Interner) -> String {
        match self {
            Path::ThisModule(name) => interner.lookup(name.0).to_string(),
            Path::OtherModule(fqn) => fqn.to_string(project_root, interner),
        }
    }

    pub fn to_naive_string(&self, interner: &Interner) -> String {
        match self {
            Path::ThisModule(name) => interner.lookup(name.0).to_string(),
            Path::OtherModule(fqn) => format!(
                r#"{}::{}"#,
                interner.lookup(fqn.module.0),
                interner.lookup(fqn.name.0),
            ),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum PathWithRange {
    ThisModule(NameWithRange),
    OtherModule {
        fqn: Fqn,
        module_range: TextRange,
        name_range: TextRange,
    },
}

impl PathWithRange {
    pub fn path(self) -> Path {
        match self {
            Self::ThisModule(NameWithRange { name, .. }) => Path::ThisModule(name),
            Self::OtherModule { fqn, .. } => Path::OtherModule(fqn),
        }
    }

    pub fn into_fqn(self, current_module: FileName) -> Fqn {
        match self {
            PathWithRange::ThisModule(NameWithRange { name, .. }) => Fqn {
                module: current_module,
                name,
            },
            PathWithRange::OtherModule { fqn, .. } => fqn,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NameWithRange {
    pub name: Name,
    pub range: TextRange,
}

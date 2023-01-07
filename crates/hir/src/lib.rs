mod body;
mod index;
mod nameres;
mod world_index;

pub use index::*;
pub use body::*;
pub use world_index::*;

use interner::{Key, Interner};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name(pub Key);

// short for Fully Qualified Name
// not only the name of whatever we're referring to, but also the module it's contained in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Fqn {
    pub module: Name,
    pub name: Name,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Type {
    Unknown,
    S32,
    String,
    Named(Name),
    Void,
}

impl Type {
    pub fn display(self, interner: &Interner) -> &str {
        match self {
            Self::Unknown => "?",
            Self::S32 => "s32",
            Self::String => "string",
            Self::Named(n) => interner.lookup(n.0),
            Self::Void => "void",
        }
    }
}

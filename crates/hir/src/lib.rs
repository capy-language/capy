mod body;
mod index;
mod nameres;
mod world_index;

use ast::AstNode;
use ast::AstToken;
pub use body::*;
pub use index::*;
pub use nameres::*;
use syntax::SyntaxTree;
use text_size::TextRange;
pub use world_index::*;

use interner::{Interner, Key};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name(pub Key);

// short for Fully Qualified Name
// not only the name of whatever we're referring to, but also the module it's contained in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Fqn {
    pub module: Name,
    pub name: Name,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TyWithRange {
    Unknown,
    /// a bit-width of u32::MAX represents an isize
    IInt {
        bit_width: u32,
        range: TextRange,
    },
    /// a bit-width of u32::MAX represents a usize
    UInt {
        bit_width: u32,
        range: TextRange,
    },
    Bool {
        range: TextRange,
    },
    String {
        range: TextRange,
    },
    Array {
        size: u32,
        sub_ty: Box<TyWithRange>,
        range: TextRange,
    },
    Named {
        name: Name,
        range: TextRange,
    },
    Void {
        range: Option<TextRange>,
    },
}

impl TyWithRange {
    pub fn parse(ty: Option<ast::Ty>, interner: &mut Interner, tree: &SyntaxTree) -> TyWithRange {
        let ty = if let Some(ty) = ty {
            ty
        } else {
            return TyWithRange::Unknown;
        };

        match ty {
            ast::Ty::Array(array_ty) => TyWithRange::Array {
                size: match array_ty
                    .size(tree)
                    .and_then(|ast| ast.value(tree))
                    .map(|ast| ast.text(tree))
                    .and_then(|ast| ast.parse().ok())
                {
                    Some(size) => size,
                    None => return TyWithRange::Unknown,
                },
                sub_ty: Box::new(Self::parse(array_ty.ty(tree), interner, tree)),
                range: array_ty.range(tree),
            },
            ast::Ty::Named(path_ty) => match path_ty.path(tree) {
                Some(path) => {
                    Self::from_name(Name(interner.intern(path.text(tree))), path.range(tree))
                }
                None => TyWithRange::Unknown,
            },
        }
    }

    fn from_name(name: Name, range: TextRange) -> Self {
        if name.0 == Key::void() {
            TyWithRange::Void { range: Some(range) }
        } else if name.0 == Key::isize() {
            TyWithRange::IInt {
                bit_width: u32::MAX,
                range,
            }
        } else if name.0 == Key::i128() {
            TyWithRange::IInt {
                bit_width: 128,
                range,
            }
        } else if name.0 == Key::i64() {
            TyWithRange::IInt {
                bit_width: 64,
                range,
            }
        } else if name.0 == Key::i32() {
            TyWithRange::IInt {
                bit_width: 32,
                range,
            }
        } else if name.0 == Key::i16() {
            TyWithRange::IInt {
                bit_width: 16,
                range,
            }
        } else if name.0 == Key::i8() {
            TyWithRange::IInt {
                bit_width: 8,
                range,
            }
        } else if name.0 == Key::usize() {
            TyWithRange::UInt {
                bit_width: u32::MAX,
                range,
            }
        } else if name.0 == Key::u128() {
            TyWithRange::UInt {
                bit_width: 128,
                range,
            }
        } else if name.0 == Key::u64() {
            TyWithRange::UInt {
                bit_width: 64,
                range,
            }
        } else if name.0 == Key::u32() {
            TyWithRange::UInt {
                bit_width: 32,
                range,
            }
        } else if name.0 == Key::u16() {
            TyWithRange::UInt {
                bit_width: 16,
                range,
            }
        } else if name.0 == Key::u8() {
            TyWithRange::UInt {
                bit_width: 8,
                range,
            }
        } else if name.0 == Key::bool() {
            TyWithRange::Bool { range }
        } else if name.0 == Key::string() {
            TyWithRange::String { range }
        } else {
            TyWithRange::Named { name, range }
        }
    }
    pub fn display(&self, interner: &Interner) -> String {
        match self {
            Self::Unknown { .. } => "?".to_string(),
            Self::IInt { bit_width, .. } => {
                if *bit_width != u32::MAX {
                    format!("i{}", bit_width)
                } else {
                    "isize".to_string()
                }
            }
            Self::UInt { bit_width, .. } => {
                if *bit_width != u32::MAX {
                    format!("i{}", bit_width)
                } else {
                    "isize".to_string()
                }
            }
            Self::Bool { .. } => "bool".to_string(),
            Self::String { .. } => "string".to_string(),
            Self::Array { size, sub_ty, .. } => format!("[{size}]{}", sub_ty.display(interner)),
            Self::Named { name, .. } => interner.lookup(name.0).to_string(),
            Self::Void { .. } => "void".to_string(),
        }
    }
}

mod body;
mod index;
mod nameres;
mod world_index;

use std::path::Component;

use ast::AstToken;
pub use body::*;
pub use index::*;
pub use nameres::*;
use syntax::SyntaxTree;
use text_size::TextRange;
use uid_gen::UIDGenerator;
pub use world_index::*;

use interner::{Interner, Key};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileName(pub Key);

impl FileName {
    pub fn to_string(&self, project_root: &std::path::Path, interner: &Interner) -> String {
        let mut res = String::new();

        let file_name = interner.lookup(self.0);
        let relative_path = pathdiff::diff_paths(file_name, project_root).unwrap();

        let components = relative_path
            .components()
            .filter(|c| !matches!(c, Component::Prefix(_) | Component::RootDir))
            .collect::<Vec<_>>();
        for (idx, component) in components.iter().enumerate() {
            let component = component.as_os_str().to_string_lossy();

            if idx < components.len() - 1 {
                res.push_str(&component);

                res.push('.');
            } else {
                res.push_str(
                    &component
                        .rsplit_once('.')
                        .map(|(name, _)| name.replace('.', "-"))
                        .unwrap_or(component.to_string()),
                );
            }
        }

        res
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name(pub Key);

// short for Fully Qualified Name
// not only the name of whatever we're referring to, but also the module it's contained in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Fqn {
    pub module: FileName,
    pub name: Name,
}

impl Fqn {
    pub fn to_string(&self, project_root: &std::path::Path, interner: &Interner) -> String {
        format!(
            r#"{}::{}"#,
            self.module.to_string(project_root, interner),
            interner.lookup(self.name.0),
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum PrimitiveTy {
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
    Float {
        bit_width: u32,
        range: TextRange,
    },
    Bool {
        range: TextRange,
    },
    String {
        range: TextRange,
    },
    Char {
        range: TextRange,
    },
    Type {
        range: TextRange,
    },
    Any {
        range: TextRange,
    },
    Void {
        range: Option<TextRange>,
    },
}

impl PrimitiveTy {
    pub fn range(&self) -> Option<TextRange> {
        match self {
            PrimitiveTy::IInt { range, .. }
            | PrimitiveTy::UInt { range, .. }
            | PrimitiveTy::Float { range, .. }
            | PrimitiveTy::Bool { range }
            | PrimitiveTy::String { range }
            | PrimitiveTy::Char { range }
            | PrimitiveTy::Type { range }
            | PrimitiveTy::Any { range } => Some(*range),
            PrimitiveTy::Void { range } => *range,
        }
    }

    pub fn parse(
        ty: Option<ast::Expr>,
        interner: &mut Interner,
        tree: &SyntaxTree,
    ) -> Option<Self> {
        if let Some(ast::Expr::VarRef(var_ref)) = ty {
            let ident = var_ref.name(tree)?;

            let key = interner.intern(ident.text(tree));
            let range = ident.range(tree);

            if key == Key::void() {
                Some(PrimitiveTy::Void { range: Some(range) })
            } else if key == Key::isize() {
                Some(PrimitiveTy::IInt {
                    bit_width: u32::MAX,
                    range,
                })
            } else if key == Key::i128() {
                Some(PrimitiveTy::IInt {
                    bit_width: 128,
                    range,
                })
            } else if key == Key::i64() {
                Some(PrimitiveTy::IInt {
                    bit_width: 64,
                    range,
                })
            } else if key == Key::i32() {
                Some(PrimitiveTy::IInt {
                    bit_width: 32,
                    range,
                })
            } else if key == Key::i16() {
                Some(PrimitiveTy::IInt {
                    bit_width: 16,
                    range,
                })
            } else if key == Key::i8() {
                Some(PrimitiveTy::IInt {
                    bit_width: 8,
                    range,
                })
            } else if key == Key::usize() {
                Some(PrimitiveTy::UInt {
                    bit_width: u32::MAX,
                    range,
                })
            } else if key == Key::u128() {
                Some(PrimitiveTy::UInt {
                    bit_width: 128,
                    range,
                })
            } else if key == Key::u64() {
                Some(PrimitiveTy::UInt {
                    bit_width: 64,
                    range,
                })
            } else if key == Key::u32() {
                Some(PrimitiveTy::UInt {
                    bit_width: 32,
                    range,
                })
            } else if key == Key::u16() {
                Some(PrimitiveTy::UInt {
                    bit_width: 16,
                    range,
                })
            } else if key == Key::u8() {
                Some(PrimitiveTy::UInt {
                    bit_width: 8,
                    range,
                })
            } else if key == Key::f64() {
                Some(PrimitiveTy::Float {
                    bit_width: 64,
                    range,
                })
            } else if key == Key::f32() {
                Some(PrimitiveTy::Float {
                    bit_width: 32,
                    range,
                })
            } else if key == Key::bool() {
                Some(PrimitiveTy::Bool { range })
            } else if key == Key::string() {
                Some(PrimitiveTy::String { range })
            } else if key == Key::char() {
                Some(PrimitiveTy::Char { range })
            } else if key == Key::r#type() {
                Some(PrimitiveTy::Type { range })
            } else if key == Key::any() {
                Some(PrimitiveTy::Any { range })
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn display(&self) -> String {
        match self {
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
            Self::Float { bit_width, .. } => format!("f{}", bit_width),
            Self::Bool { .. } => "bool".to_string(),
            Self::String { .. } => "string".to_string(),
            Self::Char { .. } => "char".to_string(),
            Self::Type { .. } => "type".to_string(),
            Self::Any { .. } => "any".to_string(),
            Self::Void { .. } => "void".to_string(),
        }
    }
}

#![allow(clippy::uninlined_format_args)]
#![allow(clippy::too_many_arguments)]

mod body;
pub mod common;
mod index;
mod world_index;

use std::{
    borrow::Cow,
    env,
    path::{Component, Path},
};

use ast::AstToken;
pub use body::*;
use common::{NaiveGlobalLoc, SubDir};
pub use index::*;
use syntax::SyntaxTree;
use text_size::TextRange;
use uid_gen::UIDGenerator;
pub use world_index::*;

use interner::{Interner, Key};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum PrimitiveTy {
    /// a bit-width of u8::MAX represents an isize
    IInt {
        bit_width: u8,
        range: TextRange,
    },
    /// a bit-width of u8::MAX represents a usize
    UInt {
        bit_width: u8,
        range: TextRange,
    },
    Float {
        bit_width: u8,
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
    RawPtr {
        mutable: bool,
        range: TextRange,
    },
    RawSlice {
        range: TextRange,
    },
    Void {
        range: TextRange,
    },
}

impl PrimitiveTy {
    pub fn range(&self) -> TextRange {
        match self {
            PrimitiveTy::IInt { range, .. }
            | PrimitiveTy::UInt { range, .. }
            | PrimitiveTy::Float { range, .. }
            | PrimitiveTy::Bool { range }
            | PrimitiveTy::String { range }
            | PrimitiveTy::Char { range }
            | PrimitiveTy::Type { range }
            | PrimitiveTy::Any { range }
            | PrimitiveTy::RawPtr { range, .. }
            | PrimitiveTy::RawSlice { range }
            | PrimitiveTy::Void { range } => *range,
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
                Some(PrimitiveTy::Void { range })
            } else if key == Key::isize() {
                Some(PrimitiveTy::IInt {
                    bit_width: u8::MAX,
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
                    bit_width: u8::MAX,
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
            } else if key == Key::str() {
                Some(PrimitiveTy::String { range })
            } else if key == Key::char() {
                Some(PrimitiveTy::Char { range })
            } else if key == Key::r#type() {
                Some(PrimitiveTy::Type { range })
            } else if key == Key::any() {
                Some(PrimitiveTy::Any { range })
            } else if key == Key::rawptr() {
                Some(PrimitiveTy::RawPtr {
                    mutable: false,
                    range,
                })
            } else if key == Key::rawslice() {
                Some(PrimitiveTy::RawSlice { range })
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
                if *bit_width != u8::MAX {
                    format!("i{}", bit_width)
                } else {
                    "isize".to_string()
                }
            }
            Self::UInt { bit_width, .. } => {
                if *bit_width != u8::MAX {
                    format!("u{}", bit_width)
                } else {
                    "usize".to_string()
                }
            }
            Self::Float { bit_width, .. } => format!("f{}", bit_width),
            Self::Bool { .. } => "bool".to_string(),
            Self::String { .. } => "str".to_string(),
            Self::Char { .. } => "char".to_string(),
            Self::Type { .. } => "type".to_string(),
            Self::Any { .. } => "any".to_string(),
            Self::RawPtr { mutable: false, .. } => "rawptr".to_string(),
            Self::RawPtr { mutable: true, .. } => "mut rawptr".to_string(),
            Self::RawSlice { .. } => "rawslice".to_string(),
            Self::Void { .. } => "void".to_string(),
        }
    }
}

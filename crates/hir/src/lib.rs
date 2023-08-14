mod body;
mod index;
mod nameres;
mod world_index;

use ast::{AstNode, AstToken};
pub use body::*;
pub use index::*;
use la_arena::{Arena, Idx};
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

#[derive(Default)]
pub struct UIDGenerator {
    inner: u32,
}

impl UIDGenerator {
    pub fn generate_unique_id(&mut self) -> u32 {
        let id = self.inner;
        self.inner += 1;
        id
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TyParseError {
    ArrayMissingSize,
    ArraySizeNotConst,
    ArraySizeOutOfBounds,
    ArrayHasBody,
    NotATy,
    NonGlobalTy,
    /// only returned if primitives are specifically asked for
    NonPrimitive,
}

#[derive(Debug, Clone, Copy, PartialEq)]
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
        size: u64,
        sub_ty: Idx<TyWithRange>,
        range: TextRange,
    },
    Pointer {
        sub_ty: Idx<TyWithRange>,
        range: TextRange,
    },
    Distinct {
        uid: u32,
        ty: Idx<TyWithRange>,
    },
    Type {
        range: TextRange,
    },
    Named {
        path: PathWithRange,
    },
    Void {
        range: Option<TextRange>,
    },
}

impl TyWithRange {
    pub fn primitive_id(&self) -> Option<u64> {
        const INT_BIT: u64 = 1 << 63;
        const SIGNED_BIT: u64 = 1 << 62;
        const BOOL_BIT: u64 = 1 << 61;
        const STRING_BIT: u64 = 1 << 60;
        const TYPE_ID_BIT: u64 = 1 << 59;

        match self {
            TyWithRange::Unknown => Some(0),
            TyWithRange::Void { .. } => Some(0),
            TyWithRange::IInt { bit_width, .. } => Some(INT_BIT ^ SIGNED_BIT ^ (*bit_width as u64)),
            TyWithRange::UInt { bit_width, .. } => Some(INT_BIT ^ (*bit_width as u64)),
            TyWithRange::Bool { .. } => Some(BOOL_BIT),
            TyWithRange::String { .. } => Some(STRING_BIT),
            TyWithRange::Array { .. } => None,
            TyWithRange::Pointer { .. } => None,
            TyWithRange::Type { .. } => Some(TYPE_ID_BIT),
            TyWithRange::Distinct { .. } => None,
            TyWithRange::Named { .. } => None,
        }
    }

    pub fn parse(
        ty: Option<ast::Expr>,
        uid_gen: &mut UIDGenerator,
        twr_arena: &mut Arena<TyWithRange>,
        interner: &mut Interner,
        tree: &SyntaxTree,
        primitives_only: bool,
    ) -> Result<Self, (TyParseError, TextRange)> {
        let ty = match ty {
            Some(ty) => ty,
            None => return Ok(TyWithRange::Unknown),
        };

        match ty {
            ast::Expr::Array(array_ty) => {
                if let Some(body) = array_ty.body(tree) {
                    return Err((TyParseError::ArrayHasBody, body.range(tree)));
                }

                let brackets = array_ty.size(tree).unwrap();

                let size = match brackets.size(tree) {
                    Some(ast::Expr::IntLiteral(int_literal)) => {
                        match int_literal
                            .value(tree)
                            .and_then(|int| int.text(tree).parse::<u64>().ok())
                        {
                            Some(size) => size,
                            None => {
                                return Err((
                                    TyParseError::ArraySizeOutOfBounds,
                                    int_literal.range(tree),
                                ))
                            }
                        }
                    }
                    Some(_) => return Err((TyParseError::ArraySizeNotConst, brackets.range(tree))),
                    None => {
                        return Err((TyParseError::ArrayMissingSize, brackets.range(tree)));
                    }
                };
                let sub_ty = Self::parse(
                    array_ty.ty(tree).and_then(|array_ty| array_ty.expr(tree)),
                    uid_gen,
                    twr_arena,
                    interner,
                    tree,
                    primitives_only,
                )?;

                Ok(TyWithRange::Array {
                    size,
                    sub_ty: twr_arena.alloc(sub_ty),
                    range: array_ty.range(tree),
                })
            }
            ast::Expr::Ref(ref_expr) => {
                let sub_ty = Self::parse(
                    ref_expr.expr(tree),
                    uid_gen,
                    twr_arena,
                    interner,
                    tree,
                    primitives_only,
                )?;

                Ok(TyWithRange::Pointer {
                    sub_ty: twr_arena.alloc(sub_ty),
                    range: ref_expr.range(tree),
                })
            }
            ast::Expr::VarRef(var_ref) => {
                let path = match var_ref.name(tree) {
                    Some(path) => path,
                    None => return Ok(TyWithRange::Unknown),
                };

                let ident = match path.top_level_name(tree) {
                    Some(ident) => ident,
                    None => return Ok(TyWithRange::Unknown),
                };

                if let Some(var_name_token) = path.nested_name(tree) {
                    if primitives_only {
                        return Err((TyParseError::NonPrimitive, var_ref.range(tree)));
                    }

                    let module_name_token = ident;

                    let module_name = interner.intern(module_name_token.text(tree));
                    let var_name = interner.intern(var_name_token.text(tree));

                    let fqn = Fqn {
                        module: Name(module_name),
                        name: Name(var_name),
                    };

                    Ok(TyWithRange::Named {
                        path: PathWithRange::OtherModule {
                            fqn,
                            module_range: module_name_token.range(tree),
                            name_range: var_name_token.range(tree),
                        },
                    })
                } else {
                    let key = interner.intern(ident.text(tree));
                    let range = ident.range(tree);

                    match Self::from_key(key, range) {
                        Some(primitive) => Ok(primitive),
                        None => {
                            if primitives_only {
                                Err((TyParseError::NonPrimitive, var_ref.range(tree)))
                            } else {
                                Ok(TyWithRange::Named {
                                    path: PathWithRange::ThisModule {
                                        name: Name(key),
                                        range,
                                    },
                                })
                            }
                        }
                    }
                }
            }
            ast::Expr::Distinct(distinct) => {
                let ty = Self::parse(
                    distinct.ty(tree).and_then(|ty| ty.expr(tree)),
                    uid_gen,
                    twr_arena,
                    interner,
                    tree,
                    primitives_only,
                )?;

                Ok(TyWithRange::Distinct {
                    uid: uid_gen.generate_unique_id(),
                    ty: twr_arena.alloc(ty),
                })
            }
            _ => Err((TyParseError::NotATy, ty.range(tree))),
        }
    }

    pub fn from_key(key: Key, range: TextRange) -> Option<Self> {
        Some(if key == Key::void() {
            TyWithRange::Void { range: Some(range) }
        } else if key == Key::isize() {
            TyWithRange::IInt {
                bit_width: u32::MAX,
                range,
            }
        } else if key == Key::i128() {
            TyWithRange::IInt {
                bit_width: 128,
                range,
            }
        } else if key == Key::i64() {
            TyWithRange::IInt {
                bit_width: 64,
                range,
            }
        } else if key == Key::i32() {
            TyWithRange::IInt {
                bit_width: 32,
                range,
            }
        } else if key == Key::i16() {
            TyWithRange::IInt {
                bit_width: 16,
                range,
            }
        } else if key == Key::i8() {
            TyWithRange::IInt {
                bit_width: 8,
                range,
            }
        } else if key == Key::usize() {
            TyWithRange::UInt {
                bit_width: u32::MAX,
                range,
            }
        } else if key == Key::u128() {
            TyWithRange::UInt {
                bit_width: 128,
                range,
            }
        } else if key == Key::u64() {
            TyWithRange::UInt {
                bit_width: 64,
                range,
            }
        } else if key == Key::u32() {
            TyWithRange::UInt {
                bit_width: 32,
                range,
            }
        } else if key == Key::u16() {
            TyWithRange::UInt {
                bit_width: 16,
                range,
            }
        } else if key == Key::u8() {
            TyWithRange::UInt {
                bit_width: 8,
                range,
            }
        } else if key == Key::bool() {
            TyWithRange::Bool { range }
        } else if key == Key::string() {
            TyWithRange::String { range }
        } else if key == Key::r#type() {
            TyWithRange::Type { range }
        } else {
            return None;
        })
    }

    pub fn display(&self, twr_arena: &Arena<TyWithRange>, interner: &Interner) -> String {
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
            Self::Array { size, sub_ty, .. } => {
                format!(
                    "[{size}]{}",
                    twr_arena[*sub_ty].display(twr_arena, interner)
                )
            }
            Self::Pointer { sub_ty, .. } => {
                format!("^{}", twr_arena[*sub_ty].display(twr_arena, interner))
            }
            Self::Type { .. } => "type".to_string(),
            Self::Distinct { uid, ty } => {
                format!(
                    "distinct'{} {}",
                    uid,
                    twr_arena[*ty].display(twr_arena, interner)
                )
            }
            Self::Named { path } => path.path().display(interner),
            Self::Void { .. } => "void".to_string(),
        }
    }
}

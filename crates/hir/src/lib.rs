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

        let components = relative_path.components().collect::<Vec<_>>();
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
pub enum TyParseError {
    ArrayMissingSize,
    ArraySizeNotConst,
    ArraySizeOutOfBounds,
    ArrayHasBody,
    NotATy,
    /// only returned if only primitives are asked for
    NonPrimitive,
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
    Array {
        size: u64,
        sub_ty: Idx<TyWithRange>,
        range: TextRange,
    },
    Pointer {
        mutable: bool,
        sub_ty: Idx<TyWithRange>,
        range: TextRange,
    },
    Distinct {
        uid: u32,
        ty: Idx<TyWithRange>,
        range: TextRange,
    },
    Function {
        params: Vec<Idx<TyWithRange>>,
        return_ty: Idx<TyWithRange>,
        range: TextRange,
    },
    Struct {
        fields: Vec<(Option<Name>, Idx<TyWithRange>)>,
        range: TextRange,
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
    pub fn range(&self) -> Option<TextRange> {
        match self {
            TyWithRange::Unknown => None,
            TyWithRange::IInt { range, .. }
            | TyWithRange::UInt { range, .. }
            | TyWithRange::Float { range, .. }
            | TyWithRange::Bool { range }
            | TyWithRange::String { range }
            | TyWithRange::Array { range, .. }
            | TyWithRange::Pointer { range, .. }
            | TyWithRange::Distinct { range, .. }
            | TyWithRange::Function { range, .. }
            | TyWithRange::Struct { range, .. }
            | TyWithRange::Type { range } => Some(*range),
            TyWithRange::Void { range } => *range,
            TyWithRange::Named { path } => match path {
                PathWithRange::ThisModule(NameWithRange { range, .. }) => Some(*range),
                PathWithRange::OtherModule {
                    module_range,
                    name_range,
                    ..
                } => Some(module_range.cover(*name_range)),
            },
        }
    }

    pub fn primitive_id(&self) -> Option<u64> {
        const INT_BIT: u64 = 1 << 63;
        const FLOAT_BIT: u64 = 1 << 62;
        const SIGNED_BIT: u64 = 1 << 61;
        const BOOL_BIT: u64 = 1 << 60;
        const STRING_BIT: u64 = 1 << 59;
        const TYPE_ID_BIT: u64 = 1 << 58;

        match self {
            TyWithRange::Unknown => Some(0),
            TyWithRange::Void { .. } => Some(0),
            TyWithRange::IInt { bit_width, .. } => Some(INT_BIT ^ SIGNED_BIT ^ (*bit_width as u64)),
            TyWithRange::UInt { bit_width, .. } => Some(INT_BIT ^ (*bit_width as u64)),
            TyWithRange::Float { bit_width, .. } => Some(FLOAT_BIT ^ (*bit_width as u64)),
            TyWithRange::Bool { .. } => Some(BOOL_BIT),
            TyWithRange::String { .. } => Some(STRING_BIT),
            TyWithRange::Array { .. } => None,
            TyWithRange::Pointer { .. } => None,
            TyWithRange::Type { .. } => Some(TYPE_ID_BIT),
            TyWithRange::Distinct { .. } => None,
            TyWithRange::Function { .. } => None,
            TyWithRange::Struct { .. } => None,
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
                    mutable: ref_expr.mutable(tree).is_some(),
                    sub_ty: twr_arena.alloc(sub_ty),
                    range: ref_expr.range(tree),
                })
            }
            ast::Expr::VarRef(var_ref) => {
                let ident = match var_ref.name(tree) {
                    Some(path) => path,
                    None => return Ok(TyWithRange::Unknown),
                };

                let key = interner.intern(ident.text(tree));
                let range = ident.range(tree);

                match Self::from_key(key, range) {
                    Some(primitive) => Ok(primitive),
                    None => {
                        if primitives_only {
                            Err((TyParseError::NonPrimitive, var_ref.range(tree)))
                        } else {
                            Ok(TyWithRange::Named {
                                path: PathWithRange::ThisModule(NameWithRange {
                                    name: Name(key),
                                    range,
                                }),
                            })
                        }
                    }
                }
            }
            // ast::Expr::Path(path) => {
            //     if primitives_only {
            //         return Err((TyParseError::NonPrimitive, path.range(tree)));
            //     }

            //     match path.previous_part(tree) {
            //         Some(ast::Expr::VarRef(var_ref)) => {
            //             let module = var_ref.name(tree).unwrap();
            //             let module_name = interner.intern(module.text(tree));

            //             let global = match path.field_name(tree) {
            //                 Some(name) => name,
            //                 None => return Ok(TyWithRange::Unknown),
            //             };
            //             let global_name = interner.intern(global.text(tree));

            //             let fqn = Fqn {
            //                 file_name: module_name,
            //                 name: Name(global_name),
            //             };

            //             Ok(TyWithRange::Named {
            //                 path: PathWithRange::OtherModule {
            //                     fqn,
            //                     module_range: module.range(tree),
            //                     name_range: global.range(tree),
            //                 },
            //             })
            //         }
            //         _ => Err((TyParseError::NotATy, ty.range(tree))),
            //     }
            // }
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
                    range: distinct.range(tree),
                })
            }
            ast::Expr::Lambda(lambda) => {
                let mut params = Vec::new();

                if let Some(param_list) = lambda.param_list(tree) {
                    for param in param_list.params(tree) {
                        // let name = param
                        //     .name(tree)
                        //     .map(|ident| Name(interner.intern(ident.text(tree))));

                        let ty = Self::parse(
                            param.ty(tree).and_then(|ty| ty.expr(tree)),
                            uid_gen,
                            twr_arena,
                            interner,
                            tree,
                            primitives_only,
                        )?;

                        params.push(twr_arena.alloc(ty));
                    }
                }

                let return_ty = Self::parse(
                    lambda.return_ty(tree).and_then(|ty| ty.expr(tree)),
                    uid_gen,
                    twr_arena,
                    interner,
                    tree,
                    primitives_only,
                )?;

                Ok(TyWithRange::Function {
                    params,
                    return_ty: twr_arena.alloc(return_ty),
                    range: lambda.range(tree),
                })
            }
            ast::Expr::StructDecl(struct_decl) => {
                let mut fields = Vec::new();

                for field in struct_decl.fields(tree) {
                    let name = field
                        .name(tree)
                        .map(|ident| Name(interner.intern(ident.text(tree))));

                    let ty = Self::parse(
                        field.ty(tree).and_then(|ty| ty.expr(tree)),
                        uid_gen,
                        twr_arena,
                        interner,
                        tree,
                        primitives_only,
                    )?;

                    fields.push((name, twr_arena.alloc(ty)));
                }

                Ok(TyWithRange::Struct {
                    fields,
                    range: struct_decl.range(tree),
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
        } else if key == Key::f64() {
            TyWithRange::Float {
                bit_width: 64,
                range,
            }
        } else if key == Key::f32() {
            TyWithRange::Float {
                bit_width: 32,
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

    pub fn display(
        &self,
        twr_arena: &Arena<TyWithRange>,
        project_root: &std::path::Path,
        interner: &Interner,
    ) -> String {
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
            Self::Float { bit_width, .. } => format!("f{}", bit_width),
            Self::Bool { .. } => "bool".to_string(),
            Self::String { .. } => "string".to_string(),
            Self::Array { size, sub_ty, .. } => {
                format!(
                    "[{size}]{}",
                    twr_arena[*sub_ty].display(twr_arena, project_root, interner)
                )
            }
            Self::Pointer { sub_ty, .. } => {
                format!(
                    "^{}",
                    twr_arena[*sub_ty].display(twr_arena, project_root, interner)
                )
            }
            Self::Type { .. } => "type".to_string(),
            Self::Distinct { uid, ty, .. } => {
                format!(
                    "distinct'{} {}",
                    uid,
                    twr_arena[*ty].display(twr_arena, project_root, interner)
                )
            }
            Self::Named { path } => path.path().to_string(project_root, interner),
            Self::Function {
                params, return_ty, ..
            } => {
                let mut res = "(".to_string();

                for (idx, param) in params.iter().enumerate() {
                    res.push_str(&twr_arena[*param].display(twr_arena, project_root, interner));

                    if idx != params.len() - 1 {
                        res.push_str(", ");
                    }
                }
                res.push_str(") -> ");

                res.push_str(&twr_arena[*return_ty].display(twr_arena, project_root, interner));

                res
            }
            Self::Struct { fields, .. } => {
                let mut res = "struct {".to_string();

                for (idx, (name, ty)) in fields.iter().enumerate() {
                    if let Some(name) = name {
                        res.push_str(interner.lookup(name.0));
                        res.push_str(": ");
                    }

                    res.push_str(&twr_arena[*ty].display(twr_arena, project_root, interner));

                    if idx != fields.len() - 1 {
                        res.push_str(", ");
                    }
                }
                res.push('}');

                res
            }
            Self::Void { .. } => "void".to_string(),
        }
    }
}

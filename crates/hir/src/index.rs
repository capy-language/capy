use std::collections::hash_map::Entry;

use ast::{AstNode, AstToken, Ident};
use interner::{Interner, Key};
use la_arena::{Arena, Idx};
use rustc_hash::FxHashMap;
use syntax::SyntaxTree;
use text_size::TextRange;

use crate::{Name, TyParseError, TyWithRange, UIDGenerator};

#[derive(Clone)]
pub struct Index {
    pub(crate) definitions: FxHashMap<Name, Definition>,
    pub(crate) range_info: FxHashMap<Name, RangeInfo>,
}

impl Index {
    pub fn is_empty(&self) -> bool {
        self.definitions.is_empty()
    }

    pub fn functions(&self) -> impl Iterator<Item = (Name, &Function)> {
        self.definitions
            .iter()
            .filter_map(|(name, definition)| match definition {
                Definition::Function(f) => Some((*name, f)),
                _ => None,
            })
    }

    pub fn globals(&self) -> impl Iterator<Item = (Name, &Global)> {
        self.definitions
            .iter()
            .filter_map(|(name, definition)| match definition {
                Definition::Global(g) => Some((*name, g)),
                _ => None,
            })
    }

    pub fn get_definition(&self, name: Name) -> Option<&Definition> {
        self.definitions.get(&name)
    }

    pub fn range_info(&self, name: Name) -> &RangeInfo {
        &self.range_info[&name]
    }

    pub fn definition_names(&self) -> impl Iterator<Item = Name> + '_ {
        self.definitions.keys().copied()
    }

    pub fn function_names(&self) -> impl Iterator<Item = Name> + '_ {
        self.definitions.iter().filter_map(|(name, def)| match def {
            Definition::Function(_) => Some(*name),
            _ => None,
        })
    }

    pub fn global_names(&self) -> impl Iterator<Item = Name> + '_ {
        self.definitions.iter().filter_map(|(name, def)| match def {
            Definition::Global(_) => Some(*name),
            _ => None,
        })
    }

    pub fn ranges(&self) -> impl Iterator<Item = (Name, &RangeInfo)> + '_ {
        self.range_info.iter().map(|(n, r)| (*n, r))
    }

    pub fn shrink_to_fit(&mut self) {
        let Self {
            definitions,
            range_info,
        } = self;
        definitions.shrink_to_fit();
        range_info.shrink_to_fit();
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Definition {
    Function(Function),
    Global(Global),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Function {
    pub params: Vec<Param>,
    pub return_ty: Idx<TyWithRange>,
    pub ty_annotation: Idx<TyWithRange>,
    pub is_extern: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Global {
    pub ty: Idx<TyWithRange>,
}

#[derive(Debug, Clone)]
pub struct RangeInfo {
    pub whole: TextRange,
    pub name: TextRange,
    pub value: TextRange,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: Option<Name>,
    pub ty: Idx<TyWithRange>,
}

pub fn index(
    root: ast::Root,
    tree: &SyntaxTree,
    uid_gen: &mut UIDGenerator,
    twr_arena: &mut Arena<TyWithRange>,
    interner: &mut Interner,
) -> (Index, Vec<IndexingDiagnostic>) {
    let mut ctx = Ctx {
        index: Index {
            definitions: FxHashMap::default(),
            range_info: FxHashMap::default(),
        },
        diagnostics: Vec::new(),
        tree,
        uid_gen,
        twr_arena,
        interner,
    };

    for def in root.defs(tree) {
        ctx.index_def(def);
    }

    ctx.index.shrink_to_fit();

    (ctx.index, ctx.diagnostics)
}

struct Ctx<'a> {
    index: Index,
    diagnostics: Vec<IndexingDiagnostic>,
    tree: &'a SyntaxTree,
    uid_gen: &'a mut UIDGenerator,
    twr_arena: &'a mut Arena<TyWithRange>,
    interner: &'a mut Interner,
}

impl Ctx<'_> {
    fn parse_ty(&mut self, ty: Option<ast::Ty>) -> TyWithRange {
        self.parse_ty_expr(ty.and_then(|ty| ty.expr(self.tree)))
    }

    fn parse_ty_expr(&mut self, ty: Option<ast::Expr>) -> TyWithRange {
        match TyWithRange::parse(
            ty,
            self.uid_gen,
            self.twr_arena,
            self.interner,
            self.tree,
            false,
        ) {
            Ok(ty) => ty,
            Err((why, range)) => {
                self.diagnostics.push(IndexingDiagnostic {
                    kind: IndexingDiagnosticKind::TyParseError(why),
                    range,
                });
                TyWithRange::Unknown
            }
        }
    }

    fn index_def(&mut self, def: ast::Define) {
        let (result, value_range) = match def.value(self.tree) {
            Some(ast::Expr::Lambda(lambda)) => (
                self.index_lambda(def.name(self.tree), def.ty(self.tree), lambda),
                lambda.range(self.tree),
            ),
            Some(expr) => (self.index_global(def), expr.range(self.tree)),
            _ => return,
        };

        let (definition, name, name_token) = match result {
            IndexDefinitionResult::Ok {
                definition,
                name,
                name_token,
            } => (definition, name, name_token),
            IndexDefinitionResult::NoName => return,
        };

        match self.index.definitions.entry(name) {
            Entry::Occupied(_) => self.diagnostics.push(IndexingDiagnostic {
                kind: IndexingDiagnosticKind::AlreadyDefined { name: name.0 },
                range: name_token.range(self.tree),
            }),
            Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(definition);
                self.index.range_info.insert(
                    name,
                    RangeInfo {
                        whole: def.range(self.tree),
                        name: name_token.range(self.tree),
                        value: value_range,
                    },
                );
            }
        }
    }

    fn index_lambda(
        &mut self,
        name_token: Option<Ident>,
        ty_annotation: Option<ast::Ty>,
        lambda: ast::Lambda,
    ) -> IndexDefinitionResult {
        let name_token = match name_token {
            Some(ident) => ident,
            None => return IndexDefinitionResult::NoName,
        };
        let name = Name(self.interner.intern(name_token.text(self.tree)));

        let ty_annotation = self.parse_ty(ty_annotation);
        let ty_annotation = self.twr_arena.alloc(ty_annotation);

        let mut params = Vec::new();
        let mut param_type_ranges = Vec::new();

        if let Some(param_list) = lambda.param_list(self.tree) {
            for param in param_list.params(self.tree) {
                let name = param
                    .name(self.tree)
                    .map(|ident| Name(self.interner.intern(ident.text(self.tree))));

                let ty = param.ty(self.tree);
                param_type_ranges.push(ty.map(|type_| type_.range(self.tree)));

                let ty = self.parse_ty(ty);

                params.push(Param {
                    name,
                    ty: self.twr_arena.alloc(ty),
                });
            }
        }

        let return_ty = lambda
            .return_ty(self.tree)
            .map_or(TyWithRange::Void { range: None }, |ty| {
                self.parse_ty(Some(ty))
            });

        IndexDefinitionResult::Ok {
            definition: Definition::Function(Function {
                params,
                return_ty: self.twr_arena.alloc(return_ty),
                ty_annotation,
                is_extern: lambda.r#extern(self.tree).is_some(),
            }),
            name,
            name_token,
        }
    }

    fn index_global(&mut self, var_def: ast::Define) -> IndexDefinitionResult {
        let name_token = match var_def.name(self.tree) {
            Some(ident) => ident,
            None => return IndexDefinitionResult::NoName,
        };
        let name = Name(self.interner.intern(name_token.text(self.tree)));

        // if var_def.ty(self.tree).is_none() {
        //     self.diagnostics.push(IndexingDiagnostic {
        //         kind: IndexingDiagnosticKind::MissingTy { name: name.0 },
        //         range: if let Some(colon) = var_def.colon(self.tree) {
        //             colon.range_after(self.tree)
        //         } else {
        //             name_token.range_after(self.tree)
        //         },
        //     });
        // }
        let ty = self.parse_ty(var_def.ty(self.tree));

        IndexDefinitionResult::Ok {
            definition: Definition::Global(Global {
                ty: self.twr_arena.alloc(ty),
            }),
            name,
            name_token,
        }
    }
}

enum IndexDefinitionResult {
    Ok {
        definition: Definition,
        name: Name,
        name_token: Ident,
    },
    NoName,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IndexingDiagnostic {
    pub kind: IndexingDiagnosticKind,
    pub range: TextRange,
}

#[derive(Debug, Clone, PartialEq)]
pub enum IndexingDiagnosticKind {
    AlreadyDefined { name: Key },
    TyParseError(TyParseError),
}

impl Index {
    pub fn debug(&self, twr_arena: &Arena<TyWithRange>, interner: &Interner) -> String {
        let mut s = String::new();

        let mut definitions = self.definitions.iter().collect::<Vec<_>>();
        definitions.sort_unstable_by_key(|(name, _)| *name);

        for (name, definition) in definitions {
            s.push_str(interner.lookup(name.0));
            s.push_str(" : ");

            match definition {
                Definition::Function(function) => {
                    let ty_annotation = &twr_arena[function.ty_annotation];

                    s.push_str(&ty_annotation.display(twr_arena, interner));

                    s.push_str(" : ");

                    s.push('(');

                    for (idx, Param { name, ty }) in function.params.iter().enumerate() {
                        if let Some(name) = name {
                            s.push_str(interner.lookup(name.0));
                        } else {
                            s.push('?');
                        }

                        s.push_str(": ");

                        s.push_str(&twr_arena[*ty].display(twr_arena, interner));

                        if idx < function.params.len() - 1 {
                            s.push_str(", ");
                        }
                    }

                    s.push_str(") -> ");

                    s.push_str(&twr_arena[function.return_ty].display(twr_arena, interner));

                    if function.is_extern {
                        s.push_str(" extern");
                    }
                }
                Definition::Global(global) => {
                    s.push_str(&twr_arena[global.ty].display(twr_arena, interner));
                    s.push_str(" : global");
                }
            }

            s.push('\n');
        }

        s
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::{expect, Expect};

    fn check<const N: usize>(
        input: &str,
        expect: Expect,
        expected_diagnostics: impl Fn(
            &mut Interner,
        ) -> [(IndexingDiagnosticKind, std::ops::Range<u32>); N],
    ) {
        let mut interner = Interner::default();
        let mut uid_gen = UIDGenerator::default();
        let mut twr_arena = Arena::default();

        let tokens = lexer::lex(input);
        let tree = parser::parse_source_file(&tokens, input).into_syntax_tree();
        let root = ast::Root::cast(tree.root(), &tree).unwrap();
        let (index, actual_diagnostics) =
            index(root, &tree, &mut uid_gen, &mut twr_arena, &mut interner);

        expect.assert_eq(&index.debug(&twr_arena, &interner));

        let expected_diagnostics: Vec<_> = expected_diagnostics(&mut interner)
            .into_iter()
            .map(|(kind, range)| IndexingDiagnostic {
                kind,
                range: TextRange::new(range.start.into(), range.end.into()),
            })
            .collect();

        assert_eq!(expected_diagnostics, actual_diagnostics);
    }

    #[test]
    fn empty() {
        check("", expect![""], |_| [])
    }

    #[test]
    fn simple_function() {
        check(
            r#"
                foo :: () {}
            "#,
            expect![[r"
                foo : ? : () -> void
            "]],
            |_| [],
        )
    }

    #[test]
    fn function_with_params() {
        check(
            r#"
                foo :: (x: i32, y: string) {}
            "#,
            expect![[r"
                foo : ? : (x: i32, y: string) -> void
            "]],
            |_| [],
        )
    }

    #[test]
    fn function_with_return_ty() {
        check(
            r#"
                foo :: (x: i32, y: string) -> bool {}
            "#,
            expect![[r"
                foo : ? : (x: i32, y: string) -> bool
            "]],
            |_| [],
        )
    }

    #[test]
    fn global_without_ty_annotation() {
        check(
            r#"
                foo :: 25;
            "#,
            expect![
                r"
                foo : ? : global
            "
            ],
            |_| [],
        )
    }

    #[test]
    fn global_with_ty_annotation() {
        check(
            r#"
                foo : i32 : 25;
            "#,
            expect![[r"
                foo : i32 : global
            "]],
            |_| [],
        )
    }

    #[test]
    fn function_with_ty_annotation() {
        check(
            r#"
                foo : i32 : () {}
            "#,
            expect![[r"
                foo : i32 : () -> void
            "]],
            |_| [],
        )
    }

    #[test]
    fn function_with_missing_param_name() {
        check(
            r#"
                foo :: (: i32) {}
            "#,
            expect![[r"
                foo : ? : (?: i32) -> void
            "]],
            |_| [],
        )
    }

    #[test]
    fn function_with_missing_param_ty() {
        check(
            r#"
                foo :: (x) {}
            "#,
            expect![[r"
                foo : ? : (x: ?) -> void
            "]],
            |_| [],
        )
    }

    #[test]
    fn function_with_missing_return_ty() {
        check(
            r#"
                foo :: () -> {}
            "#,
            expect![[r"
                foo : ? : () -> void
            "]],
            |_| [],
        )
    }

    #[test]
    fn definition_with_the_same_name() {
        check(
            r#"
                foo :: () {};
                foo :: (x: i32) {};
                foo :: 5;
            "#,
            expect![[r"
                foo : ? : () -> void
            "]],
            |i| {
                [
                    (
                        IndexingDiagnosticKind::AlreadyDefined {
                            name: i.intern("foo"),
                        },
                        47..50,
                    ),
                    (
                        IndexingDiagnosticKind::AlreadyDefined {
                            name: i.intern("foo"),
                        },
                        83..86,
                    ),
                ]
            },
        )
    }

    #[test]
    fn named_ty() {
        check(
            r#"
                imaginary :: distinct i32;
                foo :: (x: imaginary) {}
            "#,
            expect![[r"
                imaginary : ? : global
                foo : ? : (x: imaginary) -> void
            "]],
            |_| [],
        )
    }

    #[test]
    fn path_ty() {
        check(
            r#"
                foo :: (x: other_file.imaginary) {}
            "#,
            expect![[r"
                foo : ? : (x: ?) -> void
            "]],
            |_| {
                [(
                    IndexingDiagnosticKind::TyParseError(TyParseError::NotATy),
                    28..48,
                )]
            },
        )
    }

    #[test]
    fn take_array_with_body() {
        check(
            r#"
                foo :: (x: [3]i32{ 0, 0, 0 }) {}
            "#,
            expect![[r"
                foo : ? : (x: ?) -> void
            "]],
            |_| {
                [(
                    IndexingDiagnosticKind::TyParseError(TyParseError::ArrayHasBody),
                    34..45,
                )]
            },
        )
    }

    #[test]
    fn take_array_missing_size() {
        check(
            r#"
                foo :: (x: []i32) {}
            "#,
            expect![[r"
                foo : ? : (x: ?) -> void
            "]],
            |_| {
                [(
                    IndexingDiagnosticKind::TyParseError(TyParseError::ArrayMissingSize),
                    28..30,
                )]
            },
        )
    }

    #[test]
    fn take_array_non_const_size() {
        check(
            r#"
                foo :: (x: [_]i32) {}
            "#,
            expect![[r"
                foo : ? : (x: ?) -> void
            "]],
            |_| {
                [(
                    IndexingDiagnosticKind::TyParseError(TyParseError::ArraySizeNotConst),
                    29..30,
                )]
            },
        )
    }

    #[test]
    fn take_array_out_of_bounds_size() {
        check(
            r#"
                foo :: (x: [18446744073709551616]i32) {}
            "#,
            expect![[r"
                foo : ? : (x: ?) -> void
            "]],
            |_| {
                [(
                    IndexingDiagnosticKind::TyParseError(TyParseError::ArraySizeOutOfBounds),
                    29..49,
                )]
            },
        )
    }

    #[test]
    fn extern_function() {
        check(
            r#"
                printf :: (s: string, n: i32) extern;
            "#,
            expect![[r"
                printf : ? : (s: string, n: i32) -> void extern
            "]],
            |_| [],
        )
    }
}

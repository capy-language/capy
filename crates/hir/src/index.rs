use std::collections::hash_map::Entry;

use ast::{AstNode, AstToken, Ident};
use interner::{Interner, Key};
use la_arena::Arena;
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
    pub return_ty: TyWithRange,
    pub is_extern: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Global {
    pub ty: TyWithRange,
}

#[derive(Debug, Clone)]
pub struct RangeInfo {
    pub whole: TextRange,
    pub name: TextRange,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: Option<Name>,
    pub ty: TyWithRange,
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
        if matches!(def, ast::Define::Variable(_)) {
            ctx.diagnostics.push(IndexingDiagnostic {
                kind: IndexingDiagnosticKind::NonBindingAtRoot,
                range: def.range(tree),
            })
        }
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
        let result = match def.value(self.tree) {
            Some(ast::Expr::Lambda(lambda)) => {
                self.index_lambda(def.name(self.tree), def.ty(self.tree), lambda)
            }
            Some(_) => self.index_global(def),
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
                    },
                );
            }
        }
    }

    fn index_lambda(
        &mut self,
        name_token: Option<Ident>,
        type_annotation: Option<ast::Ty>,
        lambda: ast::Lambda,
    ) -> IndexDefinitionResult {
        let name_token = match name_token {
            Some(ident) => ident,
            None => return IndexDefinitionResult::NoName,
        };
        let name = Name(self.interner.intern(name_token.text(self.tree)));

        //(self.lower_type(Some(type_)), Some(type_.range(self.tree)))
        if let Some(type_) = type_annotation {
            self.diagnostics.push(IndexingDiagnostic {
                kind: IndexingDiagnosticKind::FunctionTy,
                range: type_.range(self.tree),
            })
        }

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

                params.push(Param { name, ty });
            }
        }

        let return_type = lambda
            .return_ty(self.tree)
            .map_or(TyWithRange::Void { range: None }, |ty| {
                self.parse_ty(Some(ty))
            });

        IndexDefinitionResult::Ok {
            definition: Definition::Function(Function {
                params,
                return_ty: return_type,
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
            definition: Definition::Global(Global { ty }),
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
    NonBindingAtRoot,
    AlreadyDefined { name: Key },
    MissingTy { name: Key },
    FunctionTy,
    TyParseError(TyParseError),
}

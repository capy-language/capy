use std::collections::hash_map::Entry;

use ast::{AstNode, AstToken, Ident};
use interner::{Interner, Key};
use rustc_hash::FxHashMap;
use syntax::SyntaxTree;
use text_size::TextRange;

use crate::{Name, TyWithRange};

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
    interner: &mut Interner,
) -> (Index, Vec<IndexingDiagnostic>) {
    let mut ctx = Ctx {
        index: Index {
            definitions: FxHashMap::default(),
            range_info: FxHashMap::default(),
        },
        diagnostics: Vec::new(),
        tree,
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
    interner: &'a mut Interner,
}

impl Ctx<'_> {
    fn index_def(&mut self, def: ast::VarDef) {
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

                let type_ = param.ty(self.tree);
                param_type_ranges.push(type_.map(|type_| type_.range(self.tree)));

                let type_ = TyWithRange::parse(type_, self.interner, self.tree);

                params.push(Param { name, ty: type_ });
            }
        }

        let return_type = lambda
            .return_ty(self.tree)
            .map_or(TyWithRange::Void { range: None }, |ty| {
                TyWithRange::parse(Some(ty), self.interner, self.tree)
            });

        IndexDefinitionResult::Ok {
            definition: Definition::Function(Function {
                params,
                return_ty: return_type,
            }),
            name,
            name_token,
        }
    }

    fn index_global(&mut self, var_def: ast::VarDef) -> IndexDefinitionResult {
        let name_token = match var_def.name(self.tree) {
            Some(ident) => ident,
            None => return IndexDefinitionResult::NoName,
        };
        let name = Name(self.interner.intern(name_token.text(self.tree)));

        if var_def.ty(self.tree).is_none() {
            self.diagnostics.push(IndexingDiagnostic {
                kind: IndexingDiagnosticKind::MissingTy { name: name.0 },
                range: if let Some(colon) = var_def.colon(self.tree) {
                    colon.range_after(self.tree)
                } else {
                    name_token.range_after(self.tree)
                },
            });
        }
        let ty = TyWithRange::parse(var_def.ty(self.tree), self.interner, self.tree);

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
    AlreadyDefined { name: Key },
    MissingTy { name: Key },
    FunctionTy,
}

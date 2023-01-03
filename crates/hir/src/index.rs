use std::collections::hash_map::Entry;

use ast::{Lambda, Ident, AstToken, AstNode};
use interner::{Interner, Key};
use rustc_hash::{FxHashMap, FxHashSet};
use syntax::SyntaxTree;
use text_size::TextRange;

use crate::{Name, Type};

#[derive(Clone)]
pub struct Index {
    pub(crate) definitions: FxHashMap<Name, Definition>,
    pub(crate) range_info: FxHashMap<Name, RangeInfo>,
    types: FxHashSet<ast::Ident>,
}

impl Index {
    pub fn functions(&self) -> impl Iterator<Item = (Name, &Function)> {
        self.definitions.iter().filter_map(|(name, definition)| match definition {
            Definition::Function(f) => Some((*name, f)),
            _ => None,
        })
    }

    pub fn globals(&self) -> impl Iterator<Item = (Name, &Global)> {
        self.definitions.iter().filter_map(|(name, definition)| match definition {
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
        let Self { definitions, range_info, types } = self;
        definitions.shrink_to_fit();
        range_info.shrink_to_fit();
        types.shrink_to_fit();
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
    pub return_type: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Global {
    pub type_: Type,
}

#[derive(Debug, Clone)]
pub struct RangeInfo {
    pub whole: TextRange,
    pub name: TextRange,
    pub types: TypesRangeInfo,
}

#[derive(Debug, Clone)]
pub enum TypesRangeInfo {
    Function { return_type: Option<TextRange>, param_types: Vec<Option<TextRange>> },
    Global { type_range: Option<TextRange> },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: Option<Name>,
    pub type_: Type,
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
            types: FxHashSet::default(),
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
            Some(ast::Expr::Lambda(lambda)) => self.index_lambda(def.name(self.tree), lambda),
            Some(_) => self.index_global(def),
            _ => return,
        };

        let (definition, name, name_token, types_range_info) =
        match result {
            IndexDefinitionResult::Ok { definition, name, name_token, types_range_info } => {
                (definition, name, name_token, types_range_info)
            },
            IndexDefinitionResult::NoName => return,
        };

        match self.index.definitions.entry(name) {
            Entry::Occupied(_) => self.diagnostics.push(IndexingDiagnostic {
                kind: IndexingDiagnosticKind::AlreadyDefined { name: name.0 },
                range: name_token.range(self.tree)
            }),
            Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(definition);
                self.index.range_info.insert(
                    name,
                    RangeInfo { 
                        whole: def.range(self.tree), 
                        name: name_token.range(self.tree), 
                        types: types_range_info, 
                    },
                );
            },
        }
    }

    fn index_lambda(&mut self, name_token: Option<Ident>, lambda: ast::Lambda) -> IndexDefinitionResult {
        let name_token = match name_token {
            Some(ident) => ident,
            None => return IndexDefinitionResult::NoName,
        };
        let name = Name(self.interner.intern(name_token.text(self.tree)));

        let mut params = Vec::new();
        let mut param_type_ranges = Vec::new();

        if let Some(param_list) = lambda.param_list(self.tree) {
            for param in param_list.params(self.tree) {
                let name = param
                    .name(self.tree)
                    .map(|ident| Name(self.interner.intern(ident.text(self.tree))));

                let type_ = param.type_annotation(self.tree);
                param_type_ranges.push(type_.map(|type_| type_.range(self.tree)));

                let type_ = self.lower_type(type_);

                params.push(Param { name, type_ });
            }
        }

        let return_type = lambda.return_type(self.tree);
        let (return_type, return_type_range) = match return_type {
            Some(return_type) => 
                (self.lower_type(Some(return_type)), Some(return_type.range(self.tree))),
            None => (Type::Void, None),
        };
        
        IndexDefinitionResult::Ok { 
            definition: Definition::Function(Function { 
                params, 
                return_type,
            }), 
            name,
            name_token,
            types_range_info: TypesRangeInfo::Function { 
                return_type: return_type_range,
                param_types: param_type_ranges
            }
        }
    }

    fn index_global(&mut self, var_def: ast::VarDef) -> IndexDefinitionResult {
        let name_token = match var_def.name(self.tree) {
            Some(ident) => ident,
            None => return IndexDefinitionResult::NoName,
        };
        let name = Name(self.interner.intern(name_token.text(self.tree)));

        let type_ = var_def.type_annotation(self.tree);
        let (type_, type_range) = match type_ {
            Some(type_) => 
                (self.lower_type(Some(type_)), Some(type_.range(self.tree))),
            None => (Type::Unknown, None),
        };
        
        IndexDefinitionResult::Ok { 
            definition: Definition::Global(Global { 
                type_,
            }), 
            name,
            name_token,
            types_range_info: TypesRangeInfo::Global { 
                type_range,
            }
        }
    }


    fn lower_type(&mut self, type_: Option<ast::Type>) -> Type {
        let ident = match type_.and_then(|type_| type_.path(self.tree)?.top_level_name(self.tree)) {
            Some(ident) => ident,
            None => return Type::Unknown,
        };

        self.index.types.insert(ident);

        let name = Name(self.interner.intern(ident.text(self.tree)));

        if name.0 == Key::void() {
            Type::Void
        } else if name.0 == Key::s32() {
            Type::S32
        } else if name.0 == Key::string() {
            Type::String
        } else {
            Type::Named(name)
        }
    }
}

enum IndexDefinitionResult {
    Ok {
        definition: Definition,
        name: Name,
        name_token: Ident,
        types_range_info: TypesRangeInfo,
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
}
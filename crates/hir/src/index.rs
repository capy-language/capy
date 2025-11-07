use ast::{AstNode, AstToken};
use interner::{Interner, Key};
use rustc_hash::{FxHashMap, FxHashSet};
use syntax::SyntaxTree;
use text_size::{TextRange, TextSize};

use crate::common::*;

#[derive(Clone, Debug)]
pub struct Index {
    pub(crate) definitions: FxHashSet<Name>,
    pub(crate) range_info: FxHashMap<Name, RangeInfo>,
}

impl Index {
    pub fn is_empty(&self) -> bool {
        self.definitions.is_empty()
    }

    pub fn has_definition(&self, name: Name) -> bool {
        self.definitions.contains(&name)
    }

    pub fn definitions(&self) -> impl Iterator<Item = Name> + '_ {
        self.definitions.iter().copied()
    }
    pub fn range_info(&self, name: Name) -> &RangeInfo {
        &self.range_info[&name]
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

#[derive(Debug, Clone)]
pub struct RangeInfo {
    pub whole: TextRange,
    pub name: TextRange,
    pub value: TextRange,
}

pub fn index(
    root: ast::Root,
    tree: &SyntaxTree,
    interner: &mut Interner,
) -> (Index, Vec<IndexingDiagnostic>) {
    let mut ctx = IndexingCtx {
        index: Index {
            definitions: FxHashSet::default(),
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

struct IndexingCtx<'a> {
    index: Index,
    diagnostics: Vec<IndexingDiagnostic>,
    tree: &'a SyntaxTree,
    interner: &'a mut Interner,
}

impl IndexingCtx<'_> {
    fn index_def(&mut self, def: ast::Define) {
        let name_token = match def.name(self.tree) {
            Some(ident) => ident,
            None => return,
        };
        let name = Name(self.interner.intern(name_token.text(self.tree)));
        let name_range = name_token.range(self.tree);

        if self.index.definitions.contains(&name) {
            self.diagnostics.push(IndexingDiagnostic {
                kind: IndexingDiagnosticKind::AlreadyDefined { name: name.0 },
                range: name_range,
            });
        } else {
            if def.value(self.tree).is_none() && def.r#extern(self.tree).is_none() {
                println!("both None");
            }

            self.index.definitions.insert(name);
            self.index.range_info.insert(
                name,
                RangeInfo {
                    whole: def.range(self.tree),
                    name: name_range,
                    // use the range of the value, or the range of the `extern` token
                    value: def
                        .value(self.tree)
                        .map(|value| value.range(self.tree))
                        .or(def.r#extern(self.tree).map(|ext| ext.range(self.tree)))
                        .unwrap_or_else(|| {
                            let whole_end = def.range(self.tree).end();
                            TextRange::new(whole_end, whole_end + TextSize::new(1))
                        }),
                },
            );
        }
    }
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

impl Index {
    pub fn debug(&self, interner: &Interner) -> String {
        let mut s = String::new();

        let mut defs = self.definitions.iter().collect::<Vec<_>>();
        defs.sort_unstable();

        for name in defs {
            s.push_str(interner.lookup(name.0));
            s.push('\n');
        }

        s
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::{Expect, expect};

    fn check<const N: usize>(
        input: &str,
        expect: Expect,
        expected_diagnostics: impl Fn(
            &mut Interner,
        ) -> [(IndexingDiagnosticKind, std::ops::Range<u32>); N],
    ) {
        let mut interner = Interner::default();

        let tokens = lexer::lex(input);
        let tree = parser::parse_source_file(&tokens, input).into_syntax_tree();
        let root = ast::Root::cast(tree.root(), &tree).unwrap();
        let (index, actual_diagnostics) = index(root, &tree, &mut interner);

        expect.assert_eq(&index.debug(&interner));

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
                foo
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
                foo
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
                foo
            "]],
            |_| [],
        )
    }

    #[test]
    fn multiple_definition() {
        check(
            r#"
                foo :: 25;
                bar :: "Hello";
            "#,
            expect![[r"
                foo
                bar
            "]],
            |_| [],
        )
    }

    #[test]
    fn definition_with_the_same_name() {
        check(
            r#"
                foo :: () {};
                foo :: "Hello!";
                foo :: 5;
            "#,
            expect![[r"
                foo
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
                        80..83,
                    ),
                ]
            },
        )
    }
}

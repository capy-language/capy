
use crate::{AstNode, ParenExpr};
use syntax::SyntaxTree;
use text_size::TextRange;

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ValidationDiagnostic {
    pub kind: ValidationDiagnosticKind,
    pub range: TextRange,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ValidationDiagnosticKind {
    UnneededParens,
    NumberLiteralTooLarge,
}

pub fn validate(ast: impl AstNode, tree: &SyntaxTree) -> Vec<ValidationDiagnostic> {
    let mut errors = Vec::new();

    for node in ast.syntax().descendant_nodes(tree) {
        if let Some(paren) = ParenExpr::cast(node, tree) {
            if paren.expr(tree).is_none() {
                errors.push(ValidationDiagnostic { 
                    kind: ValidationDiagnosticKind::UnneededParens, 
                    range: paren.0.range(tree),
                });
            }
        }
    }

    errors
}

#[cfg(test)]
mod tests {
    use crate::Root;

    use super::*;
    use std::ops::Range as StdRange;

    fn check_repl_line<const LEN: usize>(
        input: &str, 
        diagnostics: [(ValidationDiagnosticKind, StdRange<u32>); LEN]
    ) {
        let diagnostics: Vec<_> = diagnostics
            .iter()
            .map(|(kind, range)| ValidationDiagnostic {
                kind: *kind,
                range: {
                    let start = range.start.into();
                    let end = range.end.into();
                    TextRange::new(start, end)
                }
            })
            .collect();

        let tree = parser::parse_repl_line(&lexer::lex(input), input).into_syntax_tree();
        let root = Root::cast(tree.root(), &tree).unwrap();

        assert_eq!(validate(root, &tree), diagnostics);
    }

    #[test]
    fn validate_correct_repl() {
        check_repl_line("a = 42; a - 5 * 10;", []);
    }

    #[test]
    fn validate_correct_source() {
        check_repl_line("a = 42; main = () {};", []);
    }

    #[test]
    fn validate_u32_max() {
        check_repl_line(
            "4294967295",
            [],
        );
    }

    #[test]
    fn validate_unneeded_parens() {
        check_repl_line(
            "( )",
            [(ValidationDiagnosticKind::UnneededParens, (0..3))],
        );
    }
}
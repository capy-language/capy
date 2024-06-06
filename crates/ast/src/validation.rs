use crate::{AstNode, Expr, IfExpr, WhileExpr};
use syntax::SyntaxTree;
use text_size::TextRange;

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ValidationDiagnostic {
    pub kind: ValidationDiagnosticKind,
    pub range: TextRange,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ValidationDiagnosticKind {
    AlwaysTrue,
    AlwaysFalse,
    ParenInCondition,
}

pub fn validate(ast: impl AstNode, tree: &SyntaxTree) -> Vec<ValidationDiagnostic> {
    let mut errors = Vec::new();

    for node in ast.syntax().descendant_nodes(tree) {
        match IfExpr::cast(node, tree)
            .and_then(|if_expr| if_expr.condition(tree))
            .or_else(|| {
                WhileExpr::cast(node, tree)
                    .and_then(|while_expr| while_expr.condition(tree))
                    .and_then(|cond| cond.value(tree))
            }) {
            Some(Expr::Paren(paren_expr)) => {
                errors.push(ValidationDiagnostic {
                    kind: ValidationDiagnosticKind::ParenInCondition,
                    range: paren_expr.range(tree),
                });
            }
            Some(Expr::BoolLiteral(bool_lit)) => {
                if bool_lit.text(tree) == "true" {
                    errors.push(ValidationDiagnostic {
                        kind: ValidationDiagnosticKind::AlwaysTrue,
                        range: node.range(tree),
                    });
                } else {
                    errors.push(ValidationDiagnostic {
                        kind: ValidationDiagnosticKind::AlwaysFalse,
                        range: node.range(tree),
                    });
                }
            }
            _ => {}
        }
    }

    errors
}

#[cfg(test)]
mod tests {
    use crate::Root;

    use super::*;
    use std::ops::Range as StdRange;

    fn check_source_file<const LEN: usize>(
        input: &str,
        diagnostics: [(ValidationDiagnosticKind, StdRange<u32>); LEN],
    ) {
        let diagnostics: Vec<_> = diagnostics
            .iter()
            .map(|(kind, range)| ValidationDiagnostic {
                kind: *kind,
                range: {
                    let start = range.start.into();
                    let end = range.end.into();
                    TextRange::new(start, end)
                },
            })
            .collect();

        let tree = parser::parse_source_file(&lexer::lex(input), input).into_syntax_tree();
        let root = Root::cast(tree.root(), &tree).unwrap();

        assert_eq!(validate(root, &tree), diagnostics);
    }

    fn check_repl_line<const LEN: usize>(
        input: &str,
        diagnostics: [(ValidationDiagnosticKind, StdRange<u32>); LEN],
    ) {
        let diagnostics: Vec<_> = diagnostics
            .iter()
            .map(|(kind, range)| ValidationDiagnostic {
                kind: *kind,
                range: {
                    let start = range.start.into();
                    let end = range.end.into();
                    TextRange::new(start, end)
                },
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
        check_source_file("a = 42; main = () {};", []);
    }

    #[test]
    fn validate_u32_max() {
        check_repl_line("4294967295", []);
    }

    #[test]
    fn validate_if_always_true() {
        check_repl_line(
            "if true {}",
            [(ValidationDiagnosticKind::AlwaysTrue, (0..10))],
        );
    }

    #[test]
    fn validate_if_always_false() {
        check_repl_line(
            "if false {}",
            [(ValidationDiagnosticKind::AlwaysFalse, (0..11))],
        );
    }

    #[test]
    fn validate_while_always_true() {
        check_repl_line(
            "while true {}",
            [(ValidationDiagnosticKind::AlwaysTrue, (0..13))],
        );
    }

    #[test]
    fn validate_while_always_false() {
        check_repl_line(
            "while false {}",
            [(ValidationDiagnosticKind::AlwaysFalse, (0..14))],
        );
    }

    #[test]
    fn validate_parentheses() {
        check_repl_line("(true)", []);
    }

    #[test]
    fn validate_parentheses_in_if() {
        check_repl_line(
            "if (true) {}",
            [(ValidationDiagnosticKind::ParenInCondition, (3..9))],
        );
    }

    #[test]
    fn validate_parentheses_in_while() {
        check_repl_line(
            "while (true) {}",
            [(ValidationDiagnosticKind::ParenInCondition, (6..12))],
        );
    }
}

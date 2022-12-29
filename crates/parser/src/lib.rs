mod event;
mod grammar;
mod parser;
mod sink;
mod source;

use lexer::Lexer;
use self::parser::ParseError;
use source::Source;
use syntax::SyntaxNode;
use rowan::GreenNode;
use self::sink::Sink;

pub fn parse(input: &str) -> Parse {
    let tokens: Vec<_> = Lexer::new(input).collect();
    let source = Source::new(&tokens);
    let parser = parser::Parser::new(source);
    let events = parser.parse();
    let sink = Sink::new(&tokens, events);

    sink.finish()
}

pub struct Parse {
    green_node: GreenNode,
    errors: Vec<ParseError>,
}

impl Parse {
    pub fn debug_tree(&self) -> String {
        let mut s = String::new();

        let tree = format!("{:#?}", self.syntax());

        s.push_str(&tree[0..tree.len() - 1]);

        for error in &self.errors {
            s.push_str(&format!("\n{}", error));
        }

        s
    }

    pub fn syntax(&self) -> SyntaxNode {
        SyntaxNode::new_root(self.green_node.clone())
    }
}

#[cfg(test)]
fn check(input: &str, expected_tree: expect_test::Expect) {
    let parse = parse(input);
    expected_tree.assert_eq(&parse.debug_tree());
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::expect;

    #[test]
    fn parse_nothing() {
        check("", expect![[r#"Root@0..0"#]])
    }

    #[test]
    fn parse_whitespace() {
        check(
            "   ",
            expect![[r#"
            Root@0..3
              Whitespace@0..3 "   ""#]],
        )
    }

    #[test]
    fn parse_comment() {
        check(
            "// hello world!",
            expect![[r#"
            Root@0..15
              Comment@0..15 "// hello world!""#]],
        )
    }

    #[test]
    fn parse_binary_expression_interspersed_with_comments() {
        check(
            "
1
  + 1 // Add one
  + 10 // Add ten",
            expect![[r#"
                Root@0..37
                  Whitespace@0..1 "\n"
                  InfixExpr@1..37
                    InfixExpr@1..22
                      IntLiteral@1..5
                        Number@1..2 "1"
                        Whitespace@2..5 "\n  "
                      Plus@5..6 "+"
                      Whitespace@6..7 " "
                      IntLiteral@7..22
                        Number@7..8 "1"
                        Whitespace@8..9 " "
                        Comment@9..19 "// Add one"
                        Whitespace@19..22 "\n  "
                    Plus@22..23 "+"
                    Whitespace@23..24 " "
                    IntLiteral@24..37
                      Number@24..26 "10"
                      Whitespace@26..27 " "
                      Comment@27..37 "// Add ten"
                error at 27..37: expected ';'"#]],
        );
    }
}


pub mod validation;

use syntax::{SyntaxElement, SyntaxKind, SyntaxNode, SyntaxToken};

#[derive(Debug)]
pub struct Root(SyntaxNode);

impl Root {
    pub fn cast(node: SyntaxNode) -> Option<Self> {
        if node.kind() == SyntaxKind::Root {
            Some(Self(node))
        } else {
            None
        }
    }

    pub fn stmts(&self) -> impl Iterator<Item = Stmt> {
        self.0.children().filter_map(Stmt::cast)
    }
}

#[derive(Debug)]
pub enum Stmt {
    VariableDef(VariableDef),
    Expr(Expr),
}

impl Stmt {
    pub fn cast(node: SyntaxNode) -> Option<Self> {
        let result = match node.kind() {
            SyntaxKind::VariableDef => Self::VariableDef(VariableDef(node)),
            _ => Self::Expr(Expr::cast(node)?),
        };

        Some(result)
    }
}

#[derive(Debug)]
pub struct VariableDef(SyntaxNode);

impl VariableDef {
    pub fn name(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(SyntaxElement::into_token)
            .find(|token| token.kind() == SyntaxKind::Ident)
    }

    pub fn value(&self) -> Option<Expr> {
        self.0.children().find_map(Expr::cast)
    }
}

#[derive(Debug)]
pub enum Expr {
    BinaryExpr(BinaryExpr),
    IntLiteral(IntLiteral),
    StringLiteral(StringLiteral),
    ParenExpr(ParenExpr),
    UnaryExpr(UnaryExpr),
    VariableRef(VariableRef),
    VariableCall(VariableCall),
    BlockExpr(BlockExpr),
    LambdaExpr(LambdaExpr),
}

// * Remember to add new expressions to this function for ast.
impl Expr {
    pub fn cast(node: SyntaxNode) -> Option<Self> {
        let result = match node.kind() {
            SyntaxKind::InfixExpr => Self::BinaryExpr(BinaryExpr(node)),
            SyntaxKind::IntLiteral => Self::IntLiteral(IntLiteral(node)),
            SyntaxKind::StringLiteral => Self::StringLiteral(StringLiteral(node)),
            SyntaxKind::ParenExpr => Self::ParenExpr(ParenExpr(node)),
            SyntaxKind::PrefixExpr => Self::UnaryExpr(UnaryExpr(node)),
            SyntaxKind::VariableRef => Self::VariableRef(VariableRef(node)),
            SyntaxKind::VariableCall => Self::VariableCall(VariableCall(node)),
            SyntaxKind::BlockExpr => Self::BlockExpr(BlockExpr(node)),
            SyntaxKind::LambdaExpr => Self::LambdaExpr(LambdaExpr(node)),
            _ => return None,
        };

        Some(result)
    }
}

#[derive(Debug)]
pub struct BinaryExpr(SyntaxNode);

impl BinaryExpr {
    pub fn lhs(&self) -> Option<Expr> {
        self.0.children().find_map(Expr::cast)
    }

    pub fn rhs(&self) -> Option<Expr> {
        self.0.children().filter_map(Expr::cast).nth(1)
    }

    pub fn op(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(SyntaxElement::into_token)
            .find(|token| {
                matches!(
                    token.kind(),
                    SyntaxKind::Plus | SyntaxKind::Hyphen | SyntaxKind::Asterisk | SyntaxKind::Slash,
                )
            })
    }
}

#[derive(Debug)]
pub struct IntLiteral(SyntaxNode);

impl IntLiteral {
    pub fn cast(node: SyntaxNode) -> Option<Self> {
        if node.kind() == SyntaxKind::IntLiteral {
            Some(Self(node))
        } else {
            None
        }
    }

    pub fn parse(&self) -> Option<u64> {
        self.0.first_token().unwrap().text().parse().ok()
    }
}

#[derive(Debug)]
pub struct StringLiteral(SyntaxNode);

impl StringLiteral {
    pub fn cast(node: SyntaxNode) -> Option<Self> {
        if node.kind() == SyntaxKind::StringLiteral {
            Some(Self(node))
        } else {
            None
        }
    }

    pub fn parse(&self) -> SyntaxToken {
        self.0.first_token().unwrap()
    }
}

#[derive(Debug)]
pub struct ParenExpr(SyntaxNode);

impl ParenExpr {
    pub fn expr(&self) -> Option<Expr> {
        self.0.children().find_map(Expr::cast)
    }
}

#[derive(Debug)]
pub struct UnaryExpr(SyntaxNode);

impl UnaryExpr {
    pub fn expr(&self) -> Option<Expr> {
        self.0.children().find_map(Expr::cast)
    }

    pub fn op(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(SyntaxElement::into_token)
            .find(|token| token.kind() == SyntaxKind::Hyphen ||
                token.kind() == SyntaxKind::Plus)
    }
}

#[derive(Debug)]
pub struct VariableRef(SyntaxNode);

impl VariableRef {
    pub fn name(&self) -> Option<SyntaxToken> {
        self.0.first_token()
    }
}

#[derive(Debug)]
pub struct VariableCall(SyntaxNode);

impl VariableCall {
    pub fn name(&self) -> Option<SyntaxToken> {
        self.0.first_token()
    }

    pub fn args(&self) -> Option<impl Iterator<Item = Expr>> {
        self.0
            .children()
            .find(|node| node.kind() == SyntaxKind::Params)
            .map_or(None, |node| 
                Some(node
                    .children()
                    .filter_map(Expr::cast)))
    }
}

#[derive(Debug)]
pub struct BlockExpr(SyntaxNode);

impl BlockExpr {
    pub fn stmts(&self) -> impl Iterator<Item = Stmt> {
        self.0.children().filter_map(Stmt::cast)
    }
}

#[derive(Debug)]
pub struct LambdaExpr(SyntaxNode);

impl LambdaExpr {
    pub fn params(&self) -> Option<impl Iterator<Item = SyntaxToken>> {
        self.0
            .children()
            .find(|node| node.kind() == SyntaxKind::Params)
            .map_or(None, |node| 
                Some(node
                    .children_with_tokens()
                    .filter_map(SyntaxElement::into_token)
                    .filter(|token| token.kind() == SyntaxKind::Ident)))
    }

    pub fn stmts(&self) -> Option<impl Iterator<Item = Stmt>> {
        self.0
            .children()
            .find(|node| node.kind() == SyntaxKind::BlockExpr)
            .map_or(None, |node| 
                Some(node
                    .children()
                    .filter_map(Stmt::cast)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ast_variable_def_without_name() {
        let root = Root::cast(parser::parse(" = 10;").syntax()).unwrap();
        let ast = root.stmts().next();
        assert!(ast.is_none());
    }

    #[test]
    fn ast_string_literal() {
        let root = Root::cast(parser::parse(r#""";"#).syntax()).unwrap();
        let ast = root.stmts().next();
        assert!(ast.is_some());
    }

    #[test]
    fn ast_block() {
        let root = Root::cast(parser::parse(r#"{42;};"#).syntax()).unwrap();
        let ast = root.stmts().next();
        assert!(ast.is_some());
    }

    #[test]
    fn ast_lambda() {
        let root = Root::cast(parser::parse(r#"(x, y, z) { name = "foo"; };"#).syntax()).unwrap();
        let ast = root.stmts().next();
        assert!(ast.is_some());
    }

    #[test]
    fn ast_call() {
        let root = Root::cast(parser::parse("foo();").syntax()).unwrap();
        let ast = root.stmts().next();
        assert!(ast.is_some());
    }
}
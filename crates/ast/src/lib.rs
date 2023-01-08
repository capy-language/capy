
pub mod validation;

use syntax::{SyntaxNode, SyntaxTree, SyntaxToken, NodeKind, TokenKind};
use text_size::TextRange;

pub trait AstNode: Copy + Sized {
    fn cast(node: SyntaxNode, tree: &SyntaxTree) -> Option<Self>;

    fn syntax(self) -> SyntaxNode;

    fn text(self, tree: &SyntaxTree) -> &str {
        &self.syntax().text(tree)
    }

    fn range(self, tree: &SyntaxTree) -> TextRange {
        self.syntax().range(tree)
    }
}

pub trait AstToken: Sized {
    fn cast(token: SyntaxToken, tree: &SyntaxTree) -> Option<Self>;

    fn syntax(self) -> SyntaxToken;

    fn text(self, tree: &SyntaxTree) -> &str {
        self.syntax().text(tree)
    }

    fn range(self, tree: &SyntaxTree) -> TextRange {
        self.syntax().range(tree)
    }
}

macro_rules! def_ast_node {
    ($kind:ident) => {
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $kind(SyntaxNode);

        impl AstNode for $kind {
            fn cast(node: SyntaxNode, tree: &SyntaxTree) -> Option<Self> {
                if node.kind(tree) == NodeKind::$kind {
                    Some(Self(node))
                } else {
                    None
                }
            }

            fn syntax(self) -> SyntaxNode {
                self.0
            }
        }
    };
}

macro_rules! def_ast_token {
    ($kind:ident) => {
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $kind(SyntaxToken);

        impl AstToken for $kind {
            fn cast(token: SyntaxToken, tree: &SyntaxTree) -> Option<Self> {
                if token.kind(tree) == TokenKind::$kind {
                    Some(Self(token))
                } else {
                    None
                }
            }

            fn syntax(self) -> SyntaxToken {
                self.0
            }
        }
    };
}

def_ast_node!(Root);

impl Root {
    pub fn defs(self, tree: &SyntaxTree) -> impl Iterator<Item = VarDef> + '_ {
        self
            .stmts(tree)
            .filter_map(|stmt| match stmt {
                Stmt::VarDef(def) => Some(def),
                _ => None,
            })
    }

    pub fn stmts(self, tree: &SyntaxTree) -> impl Iterator<Item = Stmt> + '_ {
        nodes(self, tree)
    }
}

def_ast_node!(Lambda);

impl Lambda {
    pub fn param_list(self, tree: &SyntaxTree) -> Option<ParamList> {
        node(self, tree)
    }

    pub fn return_type(self, tree: &SyntaxTree) -> Option<Type> {
        node(self, tree)
    }

    pub fn body(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Stmt {
    VarDef(VarDef),
    Expr(ExprStmt),
}

impl AstNode for Stmt {
    fn cast(node: SyntaxNode, tree: &SyntaxTree) -> Option<Self> {
        match node.kind(tree) {
            NodeKind::VarDef => Some(Self::VarDef(VarDef(node))),
            NodeKind::ExprStmt => Some(Self::Expr(ExprStmt(node))),
            _ => None,
        }
    }

    fn syntax(self) -> SyntaxNode {
        match self {
            Self::VarDef(var_def) => var_def.syntax(),
            Self::Expr(expr) => expr.syntax(),
        }
    }
}

def_ast_node!(VarDef);

impl VarDef {
    pub fn name(self, tree: &SyntaxTree) -> Option<Ident> {
        token(self, tree)
    }

    pub fn type_annotation(self, tree: &SyntaxTree) -> Option<Type> {
        node(self, tree)
    }

    pub fn value(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(ParamList);

impl ParamList {
    pub fn params(self, tree: &SyntaxTree) -> impl Iterator<Item = Param> + '_ {
        nodes(self, tree)
    }
}

def_ast_node!(Param);

impl Param {
    pub fn name(self, tree: &SyntaxTree) -> Option<Ident> {
        token(self, tree)
    }

    pub fn type_annotation(self, tree: &SyntaxTree) -> Option<Type> {
        node(self, tree)
    }
}

def_ast_node!(Type);

impl Type {
    pub fn path(self, tree: &SyntaxTree) -> Option<Path> {
        node(self, tree)
    }
}

def_ast_node!(ExprStmt);

impl ExprStmt {
    pub fn expr(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Expr {
    Binary(BinaryExpr),
    Unary(UnaryExpr),
    IntLiteral(IntLiteral),
    StringLiteral(StringLiteral),
    Ref(Ref),
    Call(Call),
    Block(Block),
    Lambda(Lambda),
}

impl AstNode for Expr {
    fn cast(node: SyntaxNode, tree: &SyntaxTree) -> Option<Self> {
        let result = match node.kind(tree) {
            NodeKind::BinaryExpr => Self::Binary(BinaryExpr(node)),
            NodeKind::UnaryExpr => Self::Unary(UnaryExpr(node)),
            NodeKind::IntLiteral => Self::IntLiteral(IntLiteral(node)),
            NodeKind::StringLiteral => Self::StringLiteral(StringLiteral(node)),
            NodeKind::Ref => Self::Ref(Ref(node)),
            NodeKind::Call => Self::Call(Call(node)),
            NodeKind::Block => Self::Block(Block(node)),
            NodeKind::Lambda => Self::Lambda(Lambda(node)),
            _ => return None,
        };

        Some(result)
    }

    fn syntax(self) -> SyntaxNode {
        match self {
            Self::Binary(binary_expr) => binary_expr.syntax(),
            Self::Unary(unnary_expr) => unnary_expr.syntax(),
            Self::IntLiteral(int_literal) => int_literal.syntax(),
            Self::StringLiteral(string_literal) => string_literal.syntax(),
            Self::Ref(var_ref) => var_ref.syntax(),
            Self::Call(call) => call.syntax(),
            Self::Block(block) => block.syntax(),
            Self::Lambda(lambda) => lambda.syntax(),
        }
    }
}

def_ast_node!(BinaryExpr);

impl BinaryExpr {
    pub fn lhs(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }

    pub fn rhs(self, tree: &SyntaxTree) -> Option<Expr> {
        nodes(self, tree).nth(1)
    }

    pub fn op(self, tree: &SyntaxTree) -> Option<BinaryOp> {
        token(self, tree)
    }
}

def_ast_node!(Block);

impl Block {
    pub fn stmts(self, tree: &SyntaxTree) -> impl Iterator<Item = Stmt> + '_ {
        nodes(self, tree)
    }

    pub fn tail_expr(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(Ref);

impl Ref {
    pub fn name(self, tree: &SyntaxTree) -> Option<Path> {
        node(self, tree)
    }
}

def_ast_node!(Call);

impl Call {
    pub fn name(self, tree: &SyntaxTree) -> Option<Path> {
        node(self, tree)
    }

    pub fn arg_list(self, tree: &SyntaxTree) -> Option<ArgList> {
        node(self, tree)
    }
}

def_ast_node!(Path);

impl Path {
    pub fn top_level_name(self, tree: &SyntaxTree) -> Option<Ident> {
        token(self, tree)
    }

    pub fn nested_name(self, tree: &SyntaxTree) -> Option<Ident> {
        tokens(self, tree).nth(1)
    }
}

def_ast_node!(ArgList);

impl ArgList {
    pub fn args(self, tree: &SyntaxTree) -> impl Iterator<Item = Arg> + '_ {
        nodes(self, tree)
    }
}

def_ast_node!(Arg);

impl Arg {
    pub fn value(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(IntLiteral);

impl IntLiteral {
    pub fn value(self, tree: &SyntaxTree) -> Option<Int> {
        token(self, tree)
    }
}

def_ast_node!(StringLiteral);

impl StringLiteral {
    pub fn components(self, tree: &SyntaxTree) -> impl Iterator<Item = StringComponent> + '_ {
        tokens(self, tree)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinaryOp {
    Add(Plus),
    Sub(Hyphen),
    Mul(Asterisk),
    Div(Slash),
}

impl AstToken for BinaryOp {
    fn cast(token: SyntaxToken, tree: &SyntaxTree) -> Option<Self> {
        match token.kind(tree) {
            TokenKind::Plus => Some(Self::Add(Plus(token))),
            TokenKind::Hyphen => Some(Self::Sub(Hyphen(token))),
            TokenKind::Asterisk => Some(Self::Mul(Asterisk(token))),
            TokenKind::Slash => Some(Self::Div(Slash(token))),
            _ => None,
        }
    }

    fn syntax(self) -> SyntaxToken {
        match self {
            Self::Add(plus) => plus.syntax(),
            Self::Sub(hyphen) => hyphen.syntax(),
            Self::Mul(asterisk) => asterisk.syntax(),
            Self::Div(slash) => slash.syntax(),
        }
    }
}

def_ast_node!(UnaryExpr);

impl UnaryExpr {
    pub fn expr(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }

    pub fn op(self, tree: &SyntaxTree) -> Option<UnaryOp> {
        token(self, tree)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    Pos(Plus),
    Neg(Hyphen),
}

impl AstToken for UnaryOp {
    fn cast(token: SyntaxToken, tree: &SyntaxTree) -> Option<Self> {
        match token.kind(tree) {
            TokenKind::Plus => Some(Self::Pos(Plus(token))),
            TokenKind::Hyphen => Some(Self::Neg(Hyphen(token))),
            _ => None,
        }
    }

    fn syntax(self) -> SyntaxToken {
        match self {
            Self::Pos(plus) => plus.syntax(),
            Self::Neg(hyphen) => hyphen.syntax(),
        }
    }
}

def_ast_token!(Plus);
def_ast_token!(Hyphen);
def_ast_token!(Asterisk);
def_ast_token!(Slash);
def_ast_token!(Ident);
def_ast_token!(Int);

pub enum StringComponent {
    Escape(Escape),
    Contents(StringContents),
}

impl AstToken for StringComponent {
    fn cast(token: SyntaxToken, tree: &SyntaxTree) -> Option<Self> {
        match token.kind(tree) {
            TokenKind::Escape => Some(Self::Escape(Escape(token))),
            TokenKind::StringContents => Some(Self::Contents(StringContents(token))),
            _ => None,
        }
    }

    fn syntax(self) -> SyntaxToken {
        match self {
            Self::Escape(escape) => escape.syntax(),
            Self::Contents(contents) => contents.syntax(),
        }
    }
}

def_ast_token!(Escape);
def_ast_token!(StringContents);

fn nodes<Parent: AstNode, Child: AstNode>(node: Parent, tree: &SyntaxTree) -> impl Iterator<Item = Child> + '_ {
    node.syntax().child_nodes(tree).filter_map(|n| Child::cast(n, tree))
}

fn node<Parent: AstNode, Child: AstNode>(node: Parent, tree: &SyntaxTree) -> Option<Child> {
    node.syntax().child_nodes(tree).find_map(|n| Child::cast(n, tree))
}

fn tokens<Node: AstNode, Token: AstToken>(node: Node, tree: &SyntaxTree) -> impl Iterator<Item = Token> + '_ {
    node.syntax().child_tokens(tree).filter_map(|t| Token::cast(t, tree))
}

fn token<Node: AstNode, Token: AstToken>(node: Node, tree: &SyntaxTree) -> Option<Token> {
    node.syntax().child_tokens(tree).find_map(|t| Token::cast(t, tree))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(input: &str) -> (SyntaxTree, Root) {
        let tree = parser::parse_repl_line(&lexer::lex(input), input).into_syntax_tree();
        let root = Root::cast(tree.root(), &tree).unwrap();

        (tree, root)
    }

    #[test]
    fn cast_root() {
        parse("");
    }

    #[test]
    fn get_statements() {
        let (tree, root) = parse("a = b; a;");
        assert_eq!(root.stmts(&tree).count(), 2);
    }

    #[test]
    fn inspect_statement_kind() {
        let (tree, root) = parse("foo = bar; baz * qux;");
        let mut statements = root.stmts(&tree);

        assert!(matches!(statements.next(), Some(Stmt::VarDef(_))));
        assert!(matches!(statements.next(), Some(Stmt::Expr(_))));
        assert!(statements.next().is_none());
    }

    #[test]
    fn get_name_of_var_def() {
        let (tree, root) = parse("foo = 10;");
        let statement = root.stmts(&tree).next().unwrap();

        let var_def = match statement {
            Stmt::VarDef(var_def) => var_def,
            _ => unreachable!(),
        };

        assert_eq!(var_def.name(&tree).unwrap().text(&tree), "foo");
    }

    #[test]
    fn get_value_of_var_def() {
        let (tree, root) = parse("bar = 42;");
        let statement = root.stmts(&tree).next().unwrap();

        let var_def = match statement {
            Stmt::VarDef(var_def) => var_def,
            _ => unreachable!(),
        };

        assert!(matches!(var_def.value(&tree), Some(Expr::IntLiteral(_))));
    }

    #[test]
    fn get_lhs_and_rhs_of_binary_expr() {
        let (tree, root) = parse("foo - 42;");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let binary_expr = match expr {
            Some(Expr::Binary(binary_expr)) => binary_expr,
            _ => unreachable!(),
        };

        assert!(matches!(binary_expr.lhs(&tree), Some(Expr::Ref(_))));
        assert!(matches!(binary_expr.rhs(&tree), Some(Expr::IntLiteral(_))));
    }

    #[test]
    fn get_op_of_binary_expr() {
        let (tree, root) = parse("six * 7;");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let binary_expr = match expr {
            Some(Expr::Binary(binary_expr)) => binary_expr,
            _ => unreachable!(),
        };

        assert!(matches!(binary_expr.op(&tree), Some(BinaryOp::Mul(_))));
    }

    #[test]
    fn get_expr_of_unary_expr() {
        let (tree, root) = parse("-foo;");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let unary_expr = match expr {
            Some(Expr::Unary(unary_expr)) => unary_expr,
            _ => unreachable!(),
        };

        assert!(matches!(unary_expr.expr(&tree), Some(Expr::Ref(_))));
    }

    #[test]
    fn get_op_of_unary_expr() {
        let (tree, root) = parse("+7;");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let unary_expr = match expr {
            Some(Expr::Unary(unary_expr)) => unary_expr,
            _ => unreachable!(),
        };

        assert!(matches!(unary_expr.op(&tree), Some(UnaryOp::Pos(_))));
    }

    #[test]
    fn get_name_of_ref() {
        let (tree, root) = parse("idx;");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let var_ref = match expr {
            Some(Expr::Ref(var_ref)) => var_ref,
            _ => unreachable!(),
        };
        let path = var_ref.name(&tree).unwrap();

        assert_eq!(path.top_level_name(&tree).unwrap().text(&tree), "idx");
        assert!(path.nested_name(&tree).is_none());
    }

    #[test]
    fn get_name_of_call() {
        let (tree, root) = parse("print();");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let call = match expr {
            Some(Expr::Call(call)) => call,
            _ => unreachable!(),
        };
        let path = call.name(&tree).unwrap();

        assert_eq!(path.top_level_name(&tree).unwrap().text(&tree), "print");
        assert!(path.nested_name(&tree).is_none());
    }

    #[test]
    fn get_args_of_call() {
        let (tree, root) = parse("mul(10, 20);");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let call = match expr {
            Some(Expr::Call(call)) => call,
            _ => unreachable!(),
        };

        let mut args = call.arg_list(&tree).unwrap().args(&tree);

        assert_eq!(args.next().unwrap().value(&tree).unwrap().syntax().text(&tree), "10");
        assert_eq!(args.next().unwrap().value(&tree).unwrap().syntax().text(&tree), "20");
        assert!(args.next().is_none());
    }

    #[test]
    fn get_value_of_int_literal() {
        let (tree, root) = parse("92;");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let int_literal = match expr {
            Some(Expr::IntLiteral(int_literal)) => int_literal,
            _ => unreachable!(),
        };

        assert_eq!(int_literal.value(&tree).unwrap().text(&tree), "92");
    }

    #[test]
    fn get_components_of_string_literal() {
        let (tree, root) = parse(r#""\"Hello\"";"#);
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let string_literal = match expr {
            Some(Expr::StringLiteral(string_literal)) => string_literal,
            _ => unreachable!(),
        };

        let mut components = string_literal.components(&tree);

        let escaped_quote = match components.next() {
            Some(StringComponent::Escape(escape)) => escape,
            _ => unreachable!(),
        };
        assert_eq!(escaped_quote.text(&tree), "\\\"");

        let text = match components.next() {
            Some(StringComponent::Contents(contents)) => contents,
            _ => unreachable!(),
        };
        assert_eq!(text.text(&tree), "Hello");

        let escaped_quote = match components.next() {
            Some(StringComponent::Escape(escape)) => escape,
            _ => unreachable!(),
        };
        assert_eq!(escaped_quote.text(&tree), "\\\"");

        assert!(components.next().is_none());
    }

    #[test]
    fn get_block_stmts() {
        let (tree, root) = parse("{ a = 10; b = a * (a - 1); b + 5 };");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let block = match expr {
            Some(Expr::Block(block)) => block,
            _ => unreachable!(),
        };

        let mut statements = block.stmts(&tree);

        assert!(matches!(statements.next(), Some(Stmt::VarDef(_))));
        assert!(matches!(statements.next(), Some(Stmt::VarDef(_))));
        assert!(statements.next().is_none());
    }

    #[test]
    fn get_block_tail() {
        let (tree, root) = parse("{ a = 10; b = a * (a - 1); b + 5 };");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let block = match expr {
            Some(Expr::Block(block)) => block,
            _ => unreachable!(),
        };

        let tail_expr = block.tail_expr(&tree);

        assert!(matches!(tail_expr, Some(Expr::Binary(_))));
    }

    #[test]
    fn get_lambda_params() {
        let (tree, root) = parse("(x: s32, y: s32) {};");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let lambda = match expr {
            Some(Expr::Lambda(lambda)) => lambda,
            _ => unreachable!(),
        };

        let mut params = lambda.param_list(&tree).unwrap().params(&tree);

        let param = params.next().unwrap();
        assert_eq!(param.name(&tree).unwrap().text(&tree), "x");
        assert_eq!(param.type_annotation(&tree).unwrap().path(&tree).unwrap().text(&tree), "s32");

        let param = params.next().unwrap();
        assert_eq!(param.name(&tree).unwrap().text(&tree), "y");
        assert_eq!(param.type_annotation(&tree).unwrap().path(&tree).unwrap().text(&tree), "s32");

        assert!(params.next().is_none());
    }

    #[test]
    fn get_lambda_return_type() {
        let (tree, root) = parse("() -> s32 {};");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let lambda = match expr {
            Some(Expr::Lambda(lambda)) => lambda,
            _ => unreachable!(),
        };

        let path = lambda.return_type(&tree).unwrap().path(&tree).unwrap();

        assert_eq!(path.top_level_name(&tree).unwrap().text(&tree), "s32");
        assert!(path.nested_name(&tree).is_none());
    }

    #[test]
    fn get_lambda_body() {
        let (tree, root) = parse("() {};");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let lambda = match expr {
            Some(Expr::Lambda(lambda)) => lambda,
            _ => unreachable!(),
        };

        let block = match lambda.body(&tree).unwrap() {
            Expr::Block(block) => block,
            _ => unreachable!(),
        };

        assert!(block.stmts(&tree).next().is_none());
    }

}
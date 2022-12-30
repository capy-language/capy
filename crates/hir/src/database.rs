
use crate::{BinaryOp, Expr, Stmt, UnaryOp, ExprIdx};
use la_arena::Arena;
use syntax::SyntaxKind;

#[derive(Debug, Default, PartialEq)]
pub struct Database {
    exprs: Arena<Expr>,
    blocks: Arena<Vec<Stmt>>,
}

impl Database {
    pub(crate) fn lower_stmt(&mut self, ast: ast::Stmt) -> Option<Stmt> {
        let result = match ast {
            ast::Stmt::VariableDef(ast) => Stmt::VariableDef {
                name: ast.name()?.text().into(),
                value: self.lower_expr(ast.value()),
            },
            ast::Stmt::Return(ast) => Stmt::Return { 
                value: ast.value().and_then(|val| Some(self.lower_expr(Some(val)))),
            },
            ast::Stmt::Expr(ast) => Stmt::Expr(self.lower_expr(Some(ast))),
        };

        Some(result)
    }

    pub(crate) fn lower_expr(&mut self, ast: Option<ast::Expr>) -> Expr {
        if let Some(ast) = ast {
            match ast {
                ast::Expr::BinaryExpr(ast) => self.lower_binary(ast),
                ast::Expr::IntLiteral(ast) => Expr::IntLiteral { n: ast.parse() },
                ast::Expr::StringLiteral(ast) => self.lower_string_literal(ast),
                ast::Expr::ParenExpr(ast) => self.lower_expr(ast.expr()),
                ast::Expr::UnaryExpr(ast) => self.lower_unary(ast),
                ast::Expr::VariableRef(ast) => self.lower_variable_ref(ast),
                ast::Expr::VariableCall(ast) => self.lower_variable_call(ast),
                ast::Expr::BlockExpr(ast) => self.lower_block(ast),
                ast::Expr::LambdaExpr(ast) => self.lower_lambda(ast),
            }
        } else {
            Expr::Missing
        }
    }

    fn lower_variable_ref(&mut self, ast: ast::VariableRef) -> Expr {
        Expr::VariableRef {
            var: ast.name().unwrap().text().into(),
        }
    }

    fn lower_variable_call(&mut self, ast: ast::VariableCall) -> Expr {
        let exprs: Option<Vec<Expr>> = ast
            .args()
            .and_then(|exprs| 
                Some(
                    exprs
                    .map(|arg| self.lower_expr(Some(arg)))
                    .collect()));
        if exprs.is_none() || exprs.as_ref().unwrap().is_empty() {
            return Expr::VariableCall {
                var: ast.name().unwrap().text().into(),
                args: None,
            }
        }

        let args: Option<Vec<ExprIdx>> = exprs
            .map_or(None, |args| 
                Some(
                    args
                    .into_iter()
                    .map(|arg| self.exprs.alloc(arg))
                    .collect()));

        Expr::VariableCall {
            var: ast.name().unwrap().text().into(),
            args,
        }
    }

    fn lower_string_literal(&mut self, ast: ast::StringLiteral) -> Expr {
        let token = ast.parse();
        let mut text = token.text().chars();
        text.next();
        text.next_back();

        Expr::StringLiteral {
            s: text.as_str().into(),
        }
    }

    fn lower_binary(&mut self, ast: ast::BinaryExpr) -> Expr {
        let op = match ast.op().unwrap().kind() {
            SyntaxKind::Plus => BinaryOp::Add,
            SyntaxKind::Hyphen => BinaryOp::Sub,
            SyntaxKind::Asterisk => BinaryOp::Mul,
            SyntaxKind::Slash => BinaryOp::Div,
            _ => unreachable!(),
        };

        let lhs = self.lower_expr(ast.lhs());
        let rhs = self.lower_expr(ast.rhs());

        Expr::Binary {
            op,
            lhs: self.exprs.alloc(lhs),
            rhs: self.exprs.alloc(rhs),
        }
    }

    fn lower_unary(&mut self, ast: ast::UnaryExpr) -> Expr {
        let op = match ast.op().unwrap().kind() {
            SyntaxKind::Hyphen => UnaryOp::Neg,
            SyntaxKind::Plus => UnaryOp::Pos,
            _ => unreachable!(),
        };

        let expr = self.lower_expr(ast.expr());

        Expr::Unary {
            op,
            expr: self.exprs.alloc(expr),
        }
    }

    fn lower_block(&mut self, ast: ast::BlockExpr) -> Expr {
        let vec: Vec<Stmt> = ast.stmts().filter_map(|stmt| self.lower_stmt(stmt)).collect();
        Expr::Block {
            stmts: if vec.is_empty() { None } else { Some(self.blocks.alloc(vec)) },
        }
    }

    fn lower_lambda(&mut self, ast: ast::LambdaExpr) -> Expr {
        let params: Option<Vec<smol_str::SmolStr>> = ast
            .params()
            .and_then(|params| 
                Some(
                    params.map(|param| 
                        param.text().into())
                    .collect()));
        let params_empty = params.is_none() || params.as_ref().unwrap().is_empty();

        let stmts_vec: Option<Vec<Stmt>> = ast
            .stmts()
            .and_then(|stmts| 
                Some(
                    stmts.filter_map(|stmt| 
                        self.lower_stmt(stmt))
                    .collect()));
        let stmts_empty = stmts_vec.is_none() || stmts_vec.as_ref().unwrap().is_empty();

        Expr::Lambda {
            params: if params_empty { None } else { params },
            stmts: if stmts_empty { None } else { Some(self.blocks.alloc(stmts_vec.unwrap())) },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(input: &str) -> ast::Root {
        ast::Root::cast(parser::parse(input).syntax()).unwrap()
    }

    fn check_stmt(input: &str, expected_hir: Stmt) {
        let root = parse(input);
        let ast = root.stmts().next().unwrap();
        let hir = Database::default().lower_stmt(ast).unwrap();

        assert_eq!(hir, expected_hir);
    }

    fn check_expr(input: &str, expected_hir: Expr, expected_database: Database) {
        let root = parse(input);
        let first_stmt = root.stmts().next().unwrap();
        let ast = match first_stmt {
            ast::Stmt::Expr(ast) => ast,
            _ => unreachable!(),
        };
        let mut database = Database::default();
        let hir = database.lower_expr(Some(ast));

        assert_eq!(hir, expected_hir);
        assert_eq!(database, expected_database);
    }

    #[test]
    fn lower_variable_def() {
        check_stmt(
            "foo = bar;",
            Stmt::VariableDef {
                name: "foo".into(),
                value: Expr::VariableRef { var: "bar".into() },
            },
        );
    }

    #[test]
    fn lower_paren_expr() {
        check_expr(
            "((((((abc))))))",
            Expr::VariableRef { var: "abc".into() },
            Database::default(),
        );
    }

    #[test]
    fn lower_unary_expr() {
        let mut exprs = Arena::new();
        let blocks = Arena::new();
        let ten = exprs.alloc(Expr::IntLiteral { n: Some(10) });

        check_expr(
            "-10",
            Expr::Unary {
                expr: ten,
                op: UnaryOp::Neg,
            },
            Database { exprs, blocks },
        );
    }

    #[test]
    fn lower_variable_ref() {
        check_expr(
            "foo",
            Expr::VariableRef { var: "foo".into() },
            Database::default(),
        );
    }

    #[test]
    fn lower_string() {
        check_expr(
            r#""foo""#,
            Expr::StringLiteral { s: "foo".into() },
            Database::default(),
        );
    }

    #[test]
    fn lower_empty_string() {
        check_expr(
            r#""""#,
            Expr::StringLiteral { s: "".into() },
            Database::default(),
        );
    }

    #[test]
    fn lower_variable_def_with_string() {
        check_stmt(
            r#"a = "foo""#,
            Stmt::VariableDef {
                name: "a".into(),
                value: Expr::StringLiteral { s: "foo".into() },
            },
        );
    }

    #[test]
    fn lower_variable_def_without_value() {
        check_stmt(
            "a =",
            Stmt::VariableDef {
                name: "a".into(),
                value: Expr::Missing,
            },
        );
    }
    
    #[test]
    fn lower_binary_expr_without_rhs() {
        let mut exprs = Arena::new();
        let blocks = Arena::new();
        let lhs = exprs.alloc(Expr::IntLiteral { n: Some(10) });
        let rhs = exprs.alloc(Expr::Missing);

        check_expr(
            "10 -",
            Expr::Binary {
                lhs,
                rhs,
                op: BinaryOp::Sub,
            },
            Database { exprs, blocks },
        );
    }
    
    #[test]
    fn lower_unary_expr_without_expr() {
        let mut exprs = Arena::new();
        let blocks = Arena::new();
        let expr = exprs.alloc(Expr::Missing);

        check_expr(
            "-",
            Expr::Unary {
                expr,
                op: UnaryOp::Neg,
            },
            Database { exprs, blocks },
        );
    }

    #[test]
    fn lower_empty_block() {
        let exprs = Arena::new();
        let blocks = Arena::new();

        check_expr(
            "{}",
            Expr::Block { stmts: None },
            Database { exprs, blocks },
        );
    }

    #[test]
    fn lower_stmt_block() {
        let exprs = Arena::new();
        let mut blocks = Arena::new();
        let block = blocks.alloc(vec![
            Stmt::Expr(Expr::IntLiteral { n: Some(42) }),
        ]);

        check_expr(
            "{42;}",
            Expr::Block { stmts: Some(block) },
            Database { exprs, blocks },
        );
    }

    #[test]
    fn lower_empty_lambda() {
        let exprs = Arena::new();
        let blocks = Arena::new();

        check_expr(
            "() {}",
            Expr::Lambda { 
                params: None,
                stmts: None,
            },
            Database { exprs, blocks },
        );
    }

    #[test]
    fn lower_lambda_with_parameters() {
        let exprs = Arena::new();
        let blocks = Arena::new();

        check_expr(
            "(argc, argv) {}",
            Expr::Lambda { 
                params: Some(vec!["argc".into(), "argv".into()]),
                stmts: None,
            },
            Database { exprs, blocks },
        );
    }

    #[test]
    fn lower_lambda_with_body() {
        let exprs = Arena::new();
        let mut blocks = Arena::new();
        let block = blocks.alloc(vec![
            Stmt::VariableDef { 
                name: "word".into(), 
                value: Expr::StringLiteral { s: "foo".into() }
            },
            Stmt::VariableDef { 
                name: "magic".into(), 
                value: Expr::IntLiteral { n: Some(42) }
            },
        ]);

        check_expr(
            r#"(argc, argv) { word = "foo"; magic = 42; }"#,
            Expr::Lambda { 
                params: Some(vec!["argc".into(), "argv".into()]),
                stmts: Some(block),
            },
            Database { exprs, blocks },
        );
    }

    #[test]
    fn lower_empty_call() {
        let exprs = Arena::new();
        let blocks = Arena::new();

        check_expr(
            "foo()",
            Expr::VariableCall { 
                var: "foo".into(), 
                args: None
            },
            Database { exprs, blocks },
        );
    }

    #[test]
    fn lower_full_call() {
        let mut exprs = Arena::new();
        let num_2 = exprs.alloc(Expr::IntLiteral { n: Some(2) });
        let num_3 = exprs.alloc(Expr::IntLiteral { n: Some(3) });
        let bar = exprs.alloc(Expr::VariableRef { 
            var: "bar".into() 
        });
        let mul = exprs.alloc(Expr::Binary { 
            op: BinaryOp::Mul, 
            lhs: num_2, 
            rhs: num_3 
        });
        let blocks = Arena::new();

        check_expr(
            "foo(bar, 2 * 3)",
            Expr::VariableCall { 
                var: "foo".into(), 
                args: Some(vec![bar, mul])
            },
            Database { exprs, blocks },
        );
    }

    #[test]
    fn lower_return() {
        check_stmt(
            "return;",
            Stmt::Return { 
                value: None 
            }
        );
    }

    #[test]
    fn lower_return_value() {
        check_stmt(
            "return 5;",
            Stmt::Return { 
                value: Some(Expr::IntLiteral { n: Some(5) })
            }
        );
    }
}
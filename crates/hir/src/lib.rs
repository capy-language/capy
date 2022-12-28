
mod database;
pub use database::Database;

use la_arena::Idx;
use smol_str::SmolStr;

type ExprIdx = Idx<Expr>;

pub fn lower(ast: ast::Root) -> (Database, Vec<Stmt>) {
    let mut db = Database::default();
    let stmts = ast.stmts().filter_map(|stmt| db.lower_stmt(stmt)).collect();
    (db, stmts) 
}

#[derive(Debug, PartialEq)]
pub enum Stmt {
    VariableDef { name: SmolStr, value: Expr },
    Expr(Expr),
}

#[derive(Debug, PartialEq)]
pub enum Expr {
    Binary {
        op: BinaryOp,
        lhs: ExprIdx,
        rhs: ExprIdx,
    },
    Literal {
        n: Option<u64>,
    },
    StringLiteral {
        s: SmolStr,
    },
    Unary {
        op: UnaryOp,
        expr: ExprIdx,
    },
    VariableRef {
        var: SmolStr,
    },
    Missing,
}

#[derive(Debug, PartialEq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Debug, PartialEq)]
pub enum UnaryOp {
    Neg,
    Pos,
}

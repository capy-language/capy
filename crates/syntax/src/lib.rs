use std::mem;

pub type SyntaxBuilder = eventree::SyntaxBuilder<TreeConfig>;
pub type SyntaxElement = eventree::SyntaxElement<TreeConfig>;
pub type SyntaxNode = eventree::SyntaxNode<TreeConfig>;
pub type SyntaxToken = eventree::SyntaxToken<TreeConfig>;
pub type SyntaxTree = eventree::SyntaxTree<TreeConfig>;
pub type SyntaxTreeBuf = eventree::SyntaxTreeBuf<TreeConfig>;
pub type Event = eventree::Event<TreeConfig>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TreeConfig {}

unsafe impl eventree::TreeConfig for TreeConfig {
    type NodeKind = NodeKind;
    type TokenKind = TokenKind;

    fn node_kind_to_raw(node_kind: Self::NodeKind) -> u16 {
        node_kind as u16
    }

    fn token_kind_to_raw(token_kind: Self::TokenKind) -> u16 {
        token_kind as u16
    }

    unsafe fn token_kind_from_raw(raw: u16) -> Self::TokenKind {
        mem::transmute(raw as u8)
    }

    unsafe fn node_kind_from_raw(raw: u16) -> Self::NodeKind {
        mem::transmute(raw as u8)
    }
}

capy_macros::define_token_enum! {
    TokenKind, stripped, "../../tokenizer.txt"
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NodeKind {
    Root,
    VarRef,
    Call,
    ArgList,
    Arg,
    Array,
    ArraySize,
    ArrayBody,
    ArrayItem,
    IndexExpr, // the entire expression of indexing. e.g. `my_array[6]`
    Index,     // the actual index. `6` in `my_array[6]`
    Source,
    Distinct,
    ComptimeExpr,
    Block,
    IfExpr,
    ElseBranch,
    WhileExpr,
    Condition,
    LabelDecl,
    LabelRef,
    IntLiteral,
    FloatLiteral,
    BoolLiteral,
    CharLiteral,
    StringLiteral,
    CastExpr,
    RefExpr,
    DerefExpr,
    BinaryExpr,
    UnaryExpr,
    Binding, // `x :: 5`
    VarDef,  // `x := 5`
    Assign,
    ExprStmt,
    ReturnStmt, // todo: change these to void expressions
    BreakStmt,
    ContinueStmt,
    DeferStmt,
    Lambda,
    ParamList,
    Param,
    StructDecl,    // `struct { foo: i32 }`
    MemberDecl,    // `foo: i32`
    StructLiteral, // `My_Struct { foo: 123 }`
    MemberLiteral, // `foo: 123`
    ImportExpr,
    Ty,
    Path,
    Comment,
    Error,
}

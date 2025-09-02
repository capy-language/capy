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
        unsafe { mem::transmute(raw as u8) }
    }

    unsafe fn node_kind_from_raw(raw: u16) -> Self::NodeKind {
        unsafe { mem::transmute(raw as u8) }
    }
}

capy_macros::define_token_enum! {
    TokenKind, stripped, "../../tokenizer.txt"
}

/// Represents a group of tokens or other nodes.
///
/// For example, StmtExpr might contain an IntLiteral which contains an Int token
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NodeKind {
    Root,
    VarRef,
    Call,
    ArgList,
    Arg,
    Directive,
    ArrayDecl,
    ArraySize,
    ArrayLiteral,
    ArrayBody,
    ArrayItem,
    IndexExpr, // the entire expression of indexing. e.g. `my_array[6]`
    Index,     // the actual index. `6` in `my_array[6]`
    Source,
    Distinct,
    ComptimeExpr,
    ParenExpr,
    Block,
    IfExpr,
    ElseBranch,
    WhileExpr,
    Condition,
    SwitchExpr,
    SwitchArm,
    SwitchArmVariant,
    VariantShorthand,
    DefaultArm,
    LabelDecl,
    LabelRef,
    IntLiteral,
    FloatLiteral,
    BoolLiteral,
    CharLiteral,
    StringLiteral,
    CastExpr,
    RefExpr, // `^foo` or `^mut foo`
    MutExpr, // `mut rawptr` (yes, that's the only thing its used for)
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
    EnumDecl,
    VariantDecl,
    Discriminant,
    OptionalDecl,
    ErrorTy,
    PayloadTy,
    ErrorUnionDecl, // only for `Error_Type!Payload_Type`, the case without an error (`!Payload_Type`) is UnaryExpr
    PropagateExpr,
    ImportExpr,
    Ty,
    Path,
    Comment,
    Error,
}

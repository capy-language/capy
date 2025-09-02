#![allow(clippy::uninlined_format_args)]

pub mod validation;

use syntax::{NodeKind, SyntaxNode, SyntaxToken, SyntaxTree, TokenKind};
use text_size::TextRange;

pub trait AstNode: Copy + Sized {
    fn cast(node: SyntaxNode, tree: &SyntaxTree) -> Option<Self>;

    fn syntax(self) -> SyntaxNode;

    fn text(self, tree: &SyntaxTree) -> &str {
        self.syntax().text(tree)
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
        #[derive(Clone, Copy, PartialEq, Eq)]
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

        impl std::fmt::Debug for $kind {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.debug_tuple(stringify!($kind)).finish()
            }
        }
    };
}

macro_rules! def_ast_token {
    ($kind:ident) => {
        #[derive(Clone, Copy, PartialEq, Eq)]
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

        impl std::fmt::Debug for $kind {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.debug_tuple(stringify!($kind)).finish()
            }
        }
    };
}

macro_rules! def_multi_node {
    (
        $node_name:ident:
        $($node_child_name:ident -> $node_child_node_kind:ident)*
        ;
        $($multi_child_name:ident -> $multi_child_node_kind:ident)*
        ;
        $(fn $fn_name:ident () -> $fn_return_ty:ty)*
    ) => {
        #[derive(Clone, Copy, PartialEq, Eq)]
        pub enum $node_name {
            $($node_child_name($node_child_node_kind),)*
            $($multi_child_name($multi_child_node_kind),)*
        }

        def_multi_node!(@create_impl $node_name $($fn_name -> $fn_return_ty)* ; ($($node_child_name -> $node_child_node_kind),*) @ ($($multi_child_name -> $multi_child_node_kind),*));

        impl AstNode for $node_name {
            fn cast(node: SyntaxNode, tree: &SyntaxTree) -> Option<Self> {
                $(
                    if let Some(inner) = $multi_child_node_kind::cast(node, tree) {
                        return Some(Self::$multi_child_name(inner))
                    }
                )*

                match node.kind(tree) {
                    $(NodeKind::$node_child_node_kind =>
                        Some(Self::$node_child_name($node_child_node_kind(node))),)*
                    _ => None,
                }
            }

            fn syntax(self) -> SyntaxNode {
                match self {
                    $(Self::$node_child_name(node) => node.syntax(),)*
                    $(Self::$multi_child_name(node) => node.syntax(),)*
                }
            }
        }

        impl std::fmt::Debug for $node_name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    $(Self::$node_child_name(node) => f.debug_tuple(stringify!($node_child_name)).field(node).finish(),)*
                    $(Self::$multi_child_name(node) => f.debug_tuple(stringify!($multi_child_name)).field(node).finish(),)*
                }
            }
        }
    };
    (@create_impl $node_name:ident $($fn_name:ident -> $fn_return_ty:ty)* ; $simple:tt @ $multi:tt) => {
        impl $node_name {
            $(
                def_multi_node!(@create_fn $fn_name -> $fn_return_ty ; $simple ; $multi);
            )*
        }
    };
    (
        @create_fn
        $fn_name:ident -> $fn_return_ty:ty
        ;
        ($($node_child_name:ident -> $node_child_node_kind:ident),*)
        ;
        ($($multi_child_name:ident -> $multi_child_node_kind:ident),*)
    ) => {
        #[allow(dead_code)]
        pub fn $fn_name(self, tree: &SyntaxTree) -> $fn_return_ty {
            match self {
                $(Self::$node_child_name(inner) => inner.$fn_name(tree),)*
                $(Self::$multi_child_name(inner) => inner.$fn_name(tree),)*
            }
        }
    };
}

macro_rules! def_multi_token {
    (
        $node_name:ident:
        $($simple_child_name:ident -> $simple_child_token_kind:ident)*
    ) => {
        #[derive(Clone, Copy, PartialEq, Eq)]
        pub enum $node_name {
            $($simple_child_name($simple_child_token_kind),)*
        }

        impl AstToken for $node_name {
            fn cast(token: SyntaxToken, tree: &SyntaxTree) -> Option<Self> {
                match token.kind(tree) {
                    $(TokenKind::$simple_child_token_kind =>
                        Some(Self::$simple_child_name($simple_child_token_kind(token))),)*
                    _ => None,
                }
            }

            fn syntax(self) -> SyntaxToken {
                match self {
                    $(Self::$simple_child_name(node) => node.syntax(),)*
                }
            }
        }

        impl std::fmt::Debug for $node_name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    $(Self::$simple_child_name(node) => f.debug_tuple(stringify!($simple_child_name)).field(node).finish(),)*
                }
            }
        }
    };
}

def_ast_node!(Root);

impl Root {
    pub fn defs(self, tree: &SyntaxTree) -> impl Iterator<Item = Define> + '_ {
        self.stmts(tree).filter_map(|stmt| match stmt {
            Stmt::Define(def) => Some(def),
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

    pub fn return_ty(self, tree: &SyntaxTree) -> Option<Ty> {
        node(self, tree)
    }

    pub fn body(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }

    pub fn r#extern(self, tree: &SyntaxTree) -> Option<Extern> {
        token(self, tree)
    }
}

def_multi_node! {
    Stmt:
    Assign -> Assign
    Expr -> ExprStmt
    Return -> ReturnStmt
    Break -> BreakStmt
    Continue -> ContinueStmt
    Defer -> DeferStmt
    ;
    Define -> Define
    ;
}

def_multi_node! {
    Define:
    Binding -> Binding
    Variable -> VarDef
    ;
    ;
    fn name() -> Option<Ident>
    fn ty() -> Option<Ty>
    fn value() -> Option<Expr>
    fn r#extern() -> Option<Extern>
}

def_ast_node!(Binding);

impl Binding {
    pub fn name(self, tree: &SyntaxTree) -> Option<Ident> {
        token(self, tree)
    }

    pub fn ty(self, tree: &SyntaxTree) -> Option<Ty> {
        node(self, tree)
    }

    pub fn value(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }

    pub fn r#extern(self, tree: &SyntaxTree) -> Option<Extern> {
        token(self, tree)
    }
}

def_ast_node!(VarDef);

impl VarDef {
    pub fn name(self, tree: &SyntaxTree) -> Option<Ident> {
        token(self, tree)
    }

    pub fn ty(self, tree: &SyntaxTree) -> Option<Ty> {
        node(self, tree)
    }

    pub fn value(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }

    pub fn r#extern(self, tree: &SyntaxTree) -> Option<Extern> {
        token(self, tree)
    }
}

def_ast_node!(Assign);

impl Assign {
    pub fn source(self, tree: &SyntaxTree) -> Option<Source> {
        node(self, tree)
    }

    pub fn quick_assign_op(self, tree: &SyntaxTree) -> Option<BinaryOp> {
        token(self, tree)
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

    pub fn ellipsis(self, tree: &SyntaxTree) -> Option<Ellipsis> {
        token(self, tree)
    }

    pub fn ty(self, tree: &SyntaxTree) -> Option<Ty> {
        node(self, tree)
    }
}

def_ast_node!(Ty);

impl Ty {
    /// types are really just expressions
    pub fn expr(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(ExprStmt);

impl ExprStmt {
    pub fn expr(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(ReturnStmt);

impl ReturnStmt {
    pub fn value(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(BreakStmt);

impl BreakStmt {
    pub fn label(self, tree: &SyntaxTree) -> Option<LabelRef> {
        node(self, tree)
    }

    pub fn value(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(ContinueStmt);

impl ContinueStmt {
    pub fn label(self, tree: &SyntaxTree) -> Option<LabelRef> {
        node(self, tree)
    }
}

def_ast_node!(DeferStmt);

impl DeferStmt {
    pub fn expr(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_multi_node! {
    Expr:
    Cast -> CastExpr
    Ref -> RefExpr
    Mut -> MutExpr
    Deref -> DerefExpr
    Binary -> BinaryExpr
    Unary -> UnaryExpr
    IntLiteral -> IntLiteral
    FloatLiteral -> FloatLiteral
    BoolLiteral -> BoolLiteral
    CharLiteral -> CharLiteral
    StringLiteral -> StringLiteral
    StructDecl -> StructDecl
    StructLiteral -> StructLiteral
    EnumDecl -> EnumDecl
    ArrayDecl -> ArrayDecl
    ArrayLiteral -> ArrayLiteral
    IndexExpr -> IndexExpr
    OptionalDecl -> OptionalDecl
    ErrorUnionDecl -> ErrorUnionDecl
    Propagate -> PropagateExpr // `foo.try` propagates nils/errors upward
    VarRef -> VarRef    // `foo` in `foo.bar`
    Path -> Path        // `foo.bar`
    Call -> Call
    Paren -> ParenExpr
    Block -> Block
    If -> IfExpr
    While -> WhileExpr
    Switch -> SwitchExpr
    Distinct -> Distinct
    Lambda -> Lambda
    Comptime -> ComptimeExpr
    Directive -> Directive
    ;
    ;
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

def_ast_node!(CastExpr);

impl CastExpr {
    pub fn ty(self, tree: &SyntaxTree) -> Option<Ty> {
        node(self, tree)
    }

    pub fn expr(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(RefExpr);

impl RefExpr {
    pub fn mutable(self, tree: &SyntaxTree) -> Option<Mut> {
        token(self, tree)
    }

    pub fn expr(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(MutExpr);

impl MutExpr {
    pub fn expr(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(DerefExpr);

impl DerefExpr {
    pub fn pointer(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(PropagateExpr);

impl PropagateExpr {
    pub fn expr(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }

    pub fn dot(self, tree: &SyntaxTree) -> Option<Dot> {
        token(self, tree)
    }

    pub fn r#try(self, tree: &SyntaxTree) -> Option<Try> {
        token(self, tree)
    }
}

def_ast_node!(OptionalDecl);

impl OptionalDecl {
    pub fn ty(self, tree: &SyntaxTree) -> Option<Ty> {
        node(self, tree)
    }
}

def_ast_node!(ErrorTy);

impl ErrorTy {
    pub fn ty(self, tree: &SyntaxTree) -> Option<Ty> {
        node(self, tree)
    }
}

def_ast_node!(PayloadTy);

impl PayloadTy {
    pub fn ty(self, tree: &SyntaxTree) -> Option<Ty> {
        node(self, tree)
    }
}

def_ast_node!(ErrorUnionDecl);

impl ErrorUnionDecl {
    pub fn error_ty(self, tree: &SyntaxTree) -> Option<ErrorTy> {
        node(self, tree)
    }

    pub fn payload_ty(self, tree: &SyntaxTree) -> Option<PayloadTy> {
        node(self, tree)
    }
}

def_ast_node!(Distinct);

impl Distinct {
    pub fn ty(self, tree: &SyntaxTree) -> Option<Ty> {
        node(self, tree)
    }
}

def_ast_node!(ParenExpr);

impl ParenExpr {
    pub fn expr(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(Block);

impl Block {
    pub fn label(self, tree: &SyntaxTree) -> Option<LabelDecl> {
        node(self, tree)
    }

    pub fn stmts(self, tree: &SyntaxTree) -> impl Iterator<Item = Stmt> + '_ {
        nodes(self, tree)
    }

    pub fn tail_expr(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(IfExpr);

impl IfExpr {
    pub fn condition(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }

    pub fn body(self, tree: &SyntaxTree) -> Option<Expr> {
        nodes(self, tree).nth(1)
    }

    pub fn else_branch(self, tree: &SyntaxTree) -> Option<ElseBranch> {
        node(self, tree)
    }
}

def_ast_node!(ElseBranch);

impl ElseBranch {
    pub fn body(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(WhileExpr);

impl WhileExpr {
    pub fn label(self, tree: &SyntaxTree) -> Option<LabelDecl> {
        node(self, tree)
    }

    pub fn condition(self, tree: &SyntaxTree) -> Option<Condition> {
        node(self, tree)
    }

    pub fn body(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(SwitchExpr);

impl SwitchExpr {
    pub fn argument(self, tree: &SyntaxTree) -> Option<Ident> {
        token(self, tree)
    }

    pub fn scrutinee(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }

    pub fn arms(self, tree: &SyntaxTree) -> impl Iterator<Item = SwitchArm> + '_ {
        nodes(self, tree)
    }
}

def_ast_node!(SwitchArm);

impl SwitchArm {
    pub fn variant(self, tree: &SyntaxTree) -> Option<SwitchArmVariant> {
        node(self, tree)
    }

    pub fn body(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_multi_node! {
    SwitchArmVariant:
    Default -> DefaultArm
    Shorthand -> VariantShorthand
    FullyQualified -> Ty
    ;
    ;
}

def_ast_node!(DefaultArm);

def_ast_node!(VariantShorthand);

impl VariantShorthand {
    pub fn name(self, tree: &SyntaxTree) -> Option<Ident> {
        token(self, tree)
    }
}

def_ast_node!(LabelDecl);

impl LabelDecl {
    pub fn name(self, tree: &SyntaxTree) -> Option<Ident> {
        token(self, tree)
    }
}

def_ast_node!(LabelRef);

impl LabelRef {
    pub fn name(self, tree: &SyntaxTree) -> Option<Ident> {
        token(self, tree)
    }
}

def_ast_node!(Condition);

impl Condition {
    pub fn value(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(StructDecl);

impl StructDecl {
    pub fn members(self, tree: &SyntaxTree) -> impl Iterator<Item = MemberDecl> + '_ {
        nodes(self, tree)
    }
}

def_ast_node!(MemberDecl);

impl MemberDecl {
    pub fn name(self, tree: &SyntaxTree) -> Option<Ident> {
        token(self, tree)
    }

    pub fn ty(self, tree: &SyntaxTree) -> Option<Ty> {
        node(self, tree)
    }
}

def_ast_node!(StructLiteral);

impl StructLiteral {
    pub fn ty(self, tree: &SyntaxTree) -> Option<Ty> {
        node(self, tree)
    }

    pub fn members(self, tree: &SyntaxTree) -> impl Iterator<Item = MemberLiteral> + '_ {
        nodes(self, tree)
    }
}

def_ast_node!(MemberLiteral);

impl MemberLiteral {
    pub fn name(self, tree: &SyntaxTree) -> Option<Ident> {
        token(self, tree)
    }

    pub fn value(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(EnumDecl);

impl EnumDecl {
    pub fn variants(self, tree: &SyntaxTree) -> impl Iterator<Item = VariantDecl> + '_ {
        nodes(self, tree)
    }
}

def_ast_node!(VariantDecl);

impl VariantDecl {
    pub fn name(self, tree: &SyntaxTree) -> Option<Ident> {
        token(self, tree)
    }

    pub fn ty(self, tree: &SyntaxTree) -> Option<Ty> {
        node(self, tree)
    }

    pub fn discriminant(self, tree: &SyntaxTree) -> Option<Discriminant> {
        node(self, tree)
    }
}

def_ast_node!(Discriminant);

impl Discriminant {
    pub fn value(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(ArrayDecl);

impl ArrayDecl {
    pub fn size(self, tree: &SyntaxTree) -> Option<ArraySize> {
        node(self, tree)
    }

    pub fn ty(self, tree: &SyntaxTree) -> Option<Ty> {
        node(self, tree)
    }
}

def_ast_node!(ArrayLiteral);

impl ArrayLiteral {
    pub fn ty(self, tree: &SyntaxTree) -> Option<Ty> {
        node(self, tree)
    }

    pub fn items(self, tree: &SyntaxTree) -> impl Iterator<Item = ArrayItem> + '_ {
        nodes(self, tree)
    }
}

def_ast_node!(ArraySize);

impl ArraySize {
    pub fn size(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(ArrayItem);

impl ArrayItem {
    pub fn value(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(IndexExpr);

impl IndexExpr {
    pub fn array(self, tree: &SyntaxTree) -> Option<Source> {
        node(self, tree)
    }

    pub fn index(self, tree: &SyntaxTree) -> Option<Index> {
        node(self, tree)
    }
}

def_ast_node!(Index);

impl Index {
    pub fn value(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(Source);

impl Source {
    pub fn value(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(VarRef);

impl VarRef {
    pub fn name(self, tree: &SyntaxTree) -> Option<Ident> {
        token(self, tree)
    }
}

def_ast_node!(Call);

impl Call {
    pub fn callee(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }

    pub fn arg_list(self, tree: &SyntaxTree) -> Option<ArgList> {
        node(self, tree)
    }
}

def_ast_node!(Directive);

impl Directive {
    pub fn name(self, tree: &SyntaxTree) -> Option<Ident> {
        token(self, tree)
    }

    pub fn arg_list(self, tree: &SyntaxTree) -> Option<ArgList> {
        node(self, tree)
    }
}

def_ast_node!(Path);

impl Path {
    pub fn field_name(self, tree: &SyntaxTree) -> Option<Ident> {
        token(self, tree)
    }

    pub fn previous_part(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
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

def_ast_node!(ComptimeExpr);

impl ComptimeExpr {
    pub fn body(self, tree: &SyntaxTree) -> Option<Expr> {
        node(self, tree)
    }
}

def_ast_node!(IntLiteral);

impl IntLiteral {
    pub fn value(self, tree: &SyntaxTree) -> Option<IntValue> {
        token(self, tree)
    }
}

def_multi_token! {
    IntValue:
    Dec -> Int
    Hex -> Hex
    Bin -> Bin
}

def_ast_node!(FloatLiteral);

impl FloatLiteral {
    pub fn value(self, tree: &SyntaxTree) -> Option<Float> {
        token(self, tree)
    }
}

def_ast_node!(BoolLiteral);

impl BoolLiteral {
    pub fn value(self, tree: &SyntaxTree) -> Option<Bool> {
        token(self, tree)
    }
}

def_ast_node!(StringLiteral);

impl StringLiteral {
    pub fn components(self, tree: &SyntaxTree) -> impl Iterator<Item = StringComponent> + '_ {
        tokens(self, tree)
    }
}

def_ast_node!(CharLiteral);

impl CharLiteral {
    pub fn components(self, tree: &SyntaxTree) -> impl Iterator<Item = StringComponent> + '_ {
        tokens(self, tree)
    }
}

def_multi_token! {
    BinaryOp:
    // math operations
    Add -> Plus
    Sub -> Hyphen
    Mul -> Asterisk
    Div -> Slash
    Mod -> Percent

    // comparison operations
    Lt -> Left
    Gt -> Right
    Le -> LeftEquals
    Ge -> RightEquals
    Eq -> DoubleEquals
    Ne -> BangEquals

    // bitwise operations
    BAnd -> And
    BOr -> Pipe
    Xor -> Tilde
    LShift -> DoubleLeft
    RShift -> DoubleRight

    // logical operations
    LAnd -> DoubleAnd
    LOr -> DoublePipe
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

def_multi_token! {
    UnaryOp:
    // math operations
    Pos -> Plus
    Neg -> Hyphen

    // bitwise operations
    BNot -> Tilde

    // logical operations
    LNot -> Bang
}

def_ast_token!(Mut);
def_ast_token!(Extern);
def_ast_token!(Colon);
def_ast_token!(Plus);
def_ast_token!(Hyphen);
def_ast_token!(Asterisk);
def_ast_token!(Slash);
def_ast_token!(Percent);
def_ast_token!(Left);
def_ast_token!(DoubleLeft);
def_ast_token!(LeftEquals);
def_ast_token!(Right);
def_ast_token!(DoubleRight);
def_ast_token!(RightEquals);
def_ast_token!(DoubleEquals);
def_ast_token!(BangEquals);
def_ast_token!(Tilde);
def_ast_token!(Equals);
def_ast_token!(Bang);
def_ast_token!(And);
def_ast_token!(DoubleAnd);
def_ast_token!(Pipe);
def_ast_token!(DoublePipe);
def_ast_token!(Ident);
def_ast_token!(Int);
def_ast_token!(Hex);
def_ast_token!(Bin);
def_ast_token!(Float);
def_ast_token!(Bool);
def_ast_token!(Ellipsis);
def_ast_token!(Dot);
def_ast_token!(Try);

def_multi_token! {
    StringComponent:
    Escape -> Escape
    Contents -> StringContents
}

def_ast_token!(Escape);
def_ast_token!(StringContents);

fn nodes<Parent: AstNode, Child: AstNode>(
    node: Parent,
    tree: &SyntaxTree,
) -> impl Iterator<Item = Child> + '_ {
    node.syntax()
        .child_nodes(tree)
        .filter_map(|n| Child::cast(n, tree))
}

fn node<Parent: AstNode, Child: AstNode>(node: Parent, tree: &SyntaxTree) -> Option<Child> {
    node.syntax()
        .child_nodes(tree)
        .find_map(|n| Child::cast(n, tree))
}

fn tokens<Node: AstNode, Token: AstToken>(
    node: Node,
    tree: &SyntaxTree,
) -> impl Iterator<Item = Token> + '_ {
    node.syntax()
        .child_tokens(tree)
        .filter_map(|t| Token::cast(t, tree))
}

fn token<Node: AstNode, Token: AstToken>(node: Node, tree: &SyntaxTree) -> Option<Token> {
    node.syntax()
        .child_tokens(tree)
        .find_map(|t| Token::cast(t, tree))
}

#[cfg(test)]
mod tests {
    use super::*;
    use syntax::SyntaxTreeBuf;

    fn parse(input: &str) -> (SyntaxTreeBuf, Root) {
        let parse = parser::parse_repl_line(&lexer::lex(input), input);
        for error in parse.errors() {
            println!("Syntax Error: {:?}", error);
        }
        let tree = parse.into_syntax_tree();
        let root = Root::cast(tree.root(), &tree).unwrap();

        (tree, root)
    }

    fn parse_file(input: &str) -> (SyntaxTreeBuf, Root) {
        let parse = parser::parse_source_file(&lexer::lex(input), input);
        for error in parse.errors() {
            println!("Syntax Error: {:?}", error);
        }
        let tree = parse.into_syntax_tree();
        let root = Root::cast(tree.root(), &tree).unwrap();

        (tree, root)
    }

    #[test]
    fn cast_root() {
        parse("");
    }

    #[test]
    fn get_statements() {
        let (tree, root) = parse("a := b; a;");
        assert_eq!(root.stmts(&tree).count(), 2);
    }

    #[test]
    fn inspect_statement_kind() {
        let (tree, root) = parse("foo := bar; baz * qux;");
        let mut statements = root.stmts(&tree);

        assert!(matches!(statements.next(), Some(Stmt::Define(_))));
        assert!(matches!(statements.next(), Some(Stmt::Expr(_))));
        assert!(statements.next().is_none());
    }

    #[test]
    fn get_name_of_var_def() {
        let (tree, root) = parse("foo := 10;");
        let statement = root.stmts(&tree).next().unwrap();

        let def = match statement {
            Stmt::Define(var_def) => var_def,
            _ => unreachable!(),
        };

        let var_def = match def {
            Define::Variable(var) => var,
            _ => unreachable!(),
        };

        assert_eq!(var_def.name(&tree).unwrap().text(&tree), "foo");
    }

    #[test]
    fn get_named_ty_of_var_def() {
        let (tree, root) = parse("foo : string = 10;");
        let statement = root.stmts(&tree).next().unwrap();

        let def = match statement {
            Stmt::Define(var_def) => var_def,
            _ => unreachable!(),
        };

        let var_def = match def {
            Define::Variable(var) => var,
            _ => unreachable!(),
        };

        let ty_ref = match var_def.ty(&tree).unwrap().expr(&tree) {
            Some(Expr::VarRef(name)) => name,
            _ => unreachable!(),
        };

        assert_eq!(ty_ref.name(&tree).unwrap().text(&tree), "string");
    }

    #[test]
    fn get_array_ty_of_var_def() {
        let (tree, root) = parse("foo : [3]i32 = i32.[1, 2, 3];");
        let statement = root.stmts(&tree).next().unwrap();

        let def = match statement {
            Stmt::Define(var_def) => var_def,
            _ => unreachable!(),
        };

        let var_def = match def {
            Define::Variable(var) => var,
            _ => unreachable!(),
        };

        let array_ty = match var_def.ty(&tree).unwrap().expr(&tree) {
            Some(Expr::ArrayDecl(array)) => array,
            _ => {
                unreachable!()
            }
        };

        let size = array_ty.size(&tree).unwrap().size(&tree);
        assert!(matches!(size, Some(Expr::IntLiteral(_))));
        assert_eq!(size.unwrap().text(&tree), "3");

        let sub_ty = match array_ty.ty(&tree).unwrap().expr(&tree) {
            Some(Expr::VarRef(name)) => name,
            _ => unreachable!(),
        };

        assert_eq!(sub_ty.name(&tree).unwrap().text(&tree), "i32");
    }

    #[test]
    fn get_value_of_var_def() {
        let (tree, root) = parse("bar := 42;");
        let statement = root.stmts(&tree).next().unwrap();

        let def = match statement {
            Stmt::Define(var_def) => var_def,
            _ => unreachable!(),
        };

        let var_def = match def {
            Define::Variable(var) => var,
            _ => unreachable!(),
        };

        assert!(matches!(var_def.value(&tree), Some(Expr::IntLiteral(_))));
    }

    #[test]
    fn get_type_and_value_of_var_decl() {
        let (tree, root) = parse("bar : i32;");
        let statement = root.stmts(&tree).next().unwrap();

        let def = match statement {
            Stmt::Define(var_def) => var_def,
            _ => unreachable!(),
        };

        let var_def = match def {
            Define::Variable(var) => var,
            _ => unreachable!(),
        };

        assert_eq!(var_def.ty(&tree).unwrap().text(&tree), "i32");
        assert!(var_def.value(&tree).is_none());
    }

    #[test]
    fn get_name_of_binding() {
        let (tree, root) = parse("foo :: 10;");
        let statement = root.stmts(&tree).next().unwrap();

        let def = match statement {
            Stmt::Define(var_def) => var_def,
            _ => unreachable!(),
        };

        let binding = match def {
            Define::Binding(var) => var,
            _ => unreachable!(),
        };

        assert_eq!(binding.name(&tree).unwrap().text(&tree), "foo");
    }

    #[test]
    fn get_value_of_binding() {
        let (tree, root) = parse("bar :: 42;");
        let statement = root.stmts(&tree).next().unwrap();

        let def = match statement {
            Stmt::Define(var_def) => var_def,
            _ => unreachable!(),
        };

        let binding = match def {
            Define::Binding(var) => var,
            _ => unreachable!(),
        };

        assert!(matches!(binding.value(&tree), Some(Expr::IntLiteral(_))));
    }

    #[test]
    fn get_extern_of_binding() {
        let (tree, root) = parse_file("global :: extern;");
        let statement = root.stmts(&tree).next().unwrap();

        let def = match statement {
            Stmt::Define(var_def) => var_def,
            _ => unreachable!(),
        };

        let binding = match def {
            Define::Binding(var) => var,
            _ => unreachable!(),
        };

        assert!(binding.r#extern(&tree).is_some());
    }

    #[test]
    fn get_expr_of_assign() {
        let (tree, root) = parse("foo = 10;");
        let statement = root.stmts(&tree).next().unwrap();

        let assign = match statement {
            Stmt::Assign(var_set) => var_set,
            _ => unreachable!(),
        };

        assert!(matches!(
            assign.source(&tree).unwrap().value(&tree),
            Some(Expr::VarRef(_))
        ));
    }

    #[test]
    fn get_value_of_assign() {
        let (tree, root) = parse("bar = 42;");
        let statement = root.stmts(&tree).next().unwrap();

        let assign = match statement {
            Stmt::Assign(assign) => assign,
            _ => unreachable!(),
        };

        assert!(matches!(assign.value(&tree), Some(Expr::IntLiteral(_))));
    }

    #[test]
    fn get_operator_of_quick_assign() {
        let (tree, root) = parse("baz[0] /= 2;");
        let statement = root.stmts(&tree).next().unwrap();

        let assign = match statement {
            Stmt::Assign(var_set) => var_set,
            _ => unreachable!(),
        };

        assert!(matches!(
            assign.source(&tree).unwrap().value(&tree),
            Some(Expr::IndexExpr(_))
        ));
        assert!(matches!(
            assign.quick_assign_op(&tree),
            Some(BinaryOp::Div(_))
        ));
        assert!(matches!(assign.value(&tree), Some(Expr::IntLiteral(_))));
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

        assert!(matches!(binary_expr.lhs(&tree), Some(Expr::VarRef(_))));
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

        assert!(matches!(unary_expr.expr(&tree), Some(Expr::VarRef(_))));
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
    fn array_lit_old_syntax() {
        let (tree, root) = parse(r#"[3] str { "hi", "hullo", "ahoy" }"#);
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let array_expr = match expr {
            Some(Expr::ArrayLiteral(array)) => array,
            _ => unreachable!(),
        };

        assert_eq!(array_expr.ty(&tree).unwrap().text(&tree), "str");

        let mut items = array_expr.items(&tree);

        assert_eq!(items.next().unwrap().text(&tree), r#""hi""#);
        assert_eq!(items.next().unwrap().text(&tree), r#""hullo""#);
        assert_eq!(items.next().unwrap().text(&tree), r#""ahoy""#);
        assert!(items.next().is_none());
    }

    #[test]
    fn get_ty_of_array_lit() {
        let (tree, root) = parse("bool.[true, false]");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let array_expr = match expr {
            Some(Expr::ArrayLiteral(array)) => array,
            _ => unreachable!(),
        };

        assert_eq!(array_expr.ty(&tree).unwrap().text(&tree), "bool");
    }

    #[test]
    fn get_items_of_array_literal() {
        let (tree, root) = parse("i32.[4, 8, 15 / 2, 16, 23, 42]");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let array_expr = match expr {
            Some(Expr::ArrayLiteral(array)) => array,
            _ => unreachable!(),
        };

        let mut items = array_expr.items(&tree);

        assert_eq!(items.next().unwrap().text(&tree), "4");
        assert_eq!(items.next().unwrap().text(&tree), "8");
        assert_eq!(items.next().unwrap().text(&tree), "15 / 2");
        assert_eq!(items.next().unwrap().text(&tree), "16");
        assert_eq!(items.next().unwrap().text(&tree), "23");
        assert_eq!(items.next().unwrap().text(&tree), "42");
        assert!(items.next().is_none());
    }

    #[test]
    fn get_array_of_index() {
        let (tree, root) = parse("my_array[0]");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let index_expr = match expr {
            Some(Expr::IndexExpr(index_expr)) => index_expr,
            _ => unreachable!(),
        };

        let array_ref = match index_expr.array(&tree).unwrap().value(&tree) {
            Some(Expr::VarRef(array_ref)) => array_ref,
            _ => unreachable!(),
        };

        assert_eq!(array_ref.name(&tree).unwrap().text(&tree), "my_array");
    }

    #[test]
    fn get_int_index_of_index() {
        let (tree, root) = parse("list[2]");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let index_expr = match expr {
            Some(Expr::IndexExpr(index_expr)) => index_expr,
            _ => unreachable!(),
        };

        let index_num = match index_expr.index(&tree).unwrap().value(&tree) {
            Some(Expr::IntLiteral(index_index)) => index_index,
            _ => unreachable!(),
        };

        assert_eq!(index_num.value(&tree).unwrap().text(&tree), "2");
    }

    #[test]
    fn get_ref_index_of_index() {
        let (tree, root) = parse("arr[idx]");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let index_expr = match expr {
            Some(Expr::IndexExpr(index_expr)) => index_expr,
            _ => unreachable!(),
        };

        let index_ref = match index_expr.index(&tree).unwrap().value(&tree) {
            Some(Expr::VarRef(index_index)) => index_index,
            _ => unreachable!(),
        };

        assert_eq!(index_ref.name(&tree).unwrap().text(&tree), "idx");
    }

    #[test]
    fn get_name_of_var_ref() {
        let (tree, root) = parse("idx;");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let var_ref = match expr {
            Some(Expr::VarRef(var_ref)) => var_ref,
            _ => unreachable!(),
        };

        assert_eq!(var_ref.name(&tree).unwrap().text(&tree), "idx");
    }

    #[test]
    fn get_full_path_of_var_refs() {
        let (tree, root) = parse("some_place.some_thing_in_there.inception;");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        // last part of the path
        let path = match expr {
            Some(Expr::Path(path)) => path,
            _ => unreachable!(),
        };
        assert_eq!(path.field_name(&tree).unwrap().text(&tree), "inception");

        // middle of the path
        let path = match path.previous_part(&tree) {
            Some(Expr::Path(path)) => path,
            _ => unreachable!(),
        };
        assert_eq!(
            path.field_name(&tree).unwrap().text(&tree),
            "some_thing_in_there"
        );

        // beginning of the path
        let var_ref = match path.previous_part(&tree) {
            Some(Expr::VarRef(path)) => path,
            _ => unreachable!(),
        };
        assert_eq!(var_ref.name(&tree).unwrap().text(&tree), "some_place");
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

        let var_ref = match call.callee(&tree) {
            Some(Expr::VarRef(var_ref)) => var_ref,
            _ => unreachable!(),
        };

        assert_eq!(var_ref.name(&tree).unwrap().text(&tree), "print");
    }

    #[test]
    fn get_expr_of_ref() {
        let (tree, root) = parse("^foo;");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let ref_expr = match expr {
            Some(Expr::Ref(ref_expr)) => ref_expr,
            _ => unreachable!(),
        };

        let var_ref = match ref_expr.expr(&tree) {
            Some(Expr::VarRef(ref_expr)) => ref_expr,
            _ => unreachable!(),
        };

        assert_eq!(var_ref.name(&tree).unwrap().text(&tree), "foo");
        assert!(ref_expr.mutable(&tree).is_none());
    }

    #[test]
    fn get_mut_of_ref() {
        let (tree, root) = parse("^mut foo;");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let ref_expr = match expr {
            Some(Expr::Ref(ref_expr)) => ref_expr,
            _ => unreachable!(),
        };

        let var_ref = match ref_expr.expr(&tree) {
            Some(Expr::VarRef(ref_expr)) => ref_expr,
            _ => unreachable!(),
        };

        assert_eq!(var_ref.name(&tree).unwrap().text(&tree), "foo");
        assert!(ref_expr.mutable(&tree).is_some());
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

        assert_eq!(args.next().unwrap().value(&tree).unwrap().text(&tree), "10");
        assert_eq!(args.next().unwrap().value(&tree).unwrap().text(&tree), "20");
        assert!(args.next().is_none());
    }

    #[test]
    fn get_value_of_decimal_literal() {
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

        let decimal = match int_literal.value(&tree).unwrap() {
            IntValue::Dec(dec) => dec,
            _ => unreachable!(),
        };

        assert_eq!(decimal.text(&tree), "92");
    }

    #[test]
    fn get_value_of_hex_literal() {
        let (tree, root) = parse("0xFeab1;");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let int_literal = match expr {
            Some(Expr::IntLiteral(int_literal)) => int_literal,
            _ => unreachable!(),
        };

        let hex = match int_literal.value(&tree).unwrap() {
            IntValue::Hex(hex) => hex,
            _ => unreachable!(),
        };

        assert_eq!(hex.text(&tree), "0xFeab1");
    }

    #[test]
    fn get_value_of_bin_literal() {
        let (tree, root) = parse("0b111000111;");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let int_literal = match expr {
            Some(Expr::IntLiteral(int_literal)) => int_literal,
            _ => unreachable!(),
        };

        let bin = match int_literal.value(&tree).unwrap() {
            IntValue::Bin(bin) => bin,
            _ => unreachable!(),
        };

        assert_eq!(bin.text(&tree), "0b111000111");
    }

    #[test]
    fn get_value_of_float_literal() {
        let (tree, root) = parse("4.5;");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let float_literal = match expr {
            Some(Expr::FloatLiteral(float_literal)) => float_literal,
            _ => unreachable!(),
        };

        assert_eq!(float_literal.value(&tree).unwrap().text(&tree), "4.5");
    }

    #[test]
    fn get_components_of_string_literal() {
        let (tree, root) = parse(r#""\"Hello\"";"#);
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let string_lit = match expr {
            Some(Expr::StringLiteral(string_literal)) => string_literal,
            _ => unreachable!(),
        };

        let mut components = string_lit.components(&tree);

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
    fn get_components_of_char_literal() {
        // Making sure a char literal only contains one character comes later
        let (tree, root) = parse(r"'\'Hello\'';");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let char_lit = match expr {
            Some(Expr::CharLiteral(char_lit)) => char_lit,
            _ => unreachable!(),
        };

        let mut components = char_lit.components(&tree);

        let c = char_lit.components(&tree).collect::<Vec<_>>();

        println!("{:?}", c);

        let escaped_quote = match components.next() {
            Some(StringComponent::Escape(escape)) => escape,
            _ => unreachable!(),
        };
        assert_eq!(escaped_quote.text(&tree), "\\\'");

        let text = match components.next() {
            Some(StringComponent::Contents(contents)) => contents,
            _ => unreachable!(),
        };
        assert_eq!(text.text(&tree), "Hello");

        let escaped_quote = match components.next() {
            Some(StringComponent::Escape(escape)) => escape,
            _ => unreachable!(),
        };
        assert_eq!(escaped_quote.text(&tree), "\\\'");

        assert!(components.next().is_none());
    }

    #[test]
    fn get_paren_expr() {
        let (tree, root) = parse("(true || false & true | !true);");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let paren = match expr {
            Some(Expr::Paren(paren)) => paren,
            _ => unreachable!(),
        };

        let expr = paren.expr(&tree);

        assert!(matches!(expr, Some(Expr::Binary(_))));
    }

    #[test]
    fn get_paren_empty() {
        let (tree, root) = parse("();");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let paren = match expr {
            Some(Expr::Paren(paren)) => paren,
            _ => unreachable!(),
        };

        let expr = paren.expr(&tree);

        assert!(expr.is_none());
    }

    #[test]
    fn get_block_stmts() {
        let (tree, root) = parse("{ a := 10; b = a * {a - 1}; b + 5 };");
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

        assert!(matches!(statements.next(), Some(Stmt::Define(_))));
        assert!(matches!(statements.next(), Some(Stmt::Assign(_))));
        assert!(statements.next().is_none());
    }

    #[test]
    fn get_block_label() {
        let (tree, root) = parse("`blk { x := 42; x };");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let block = match expr {
            Some(Expr::Block(block)) => block,
            _ => unreachable!(),
        };

        assert_eq!(
            block.label(&tree).unwrap().name(&tree).unwrap().text(&tree),
            "blk"
        );
    }

    #[test]
    fn get_block_tail() {
        let (tree, root) = parse("{ a = 10; b = a * {a - 1}; b + 5 };");
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
    fn get_return_value() {
        let (tree, root) = parse("return 1 + 2;");
        let statement = root.stmts(&tree).next().unwrap();
        let return_stmt = match statement {
            Stmt::Return(return_stmt) => return_stmt,
            _ => unreachable!(),
        };

        assert!(matches!(return_stmt.value(&tree), Some(Expr::Binary(_))));
    }

    #[test]
    fn get_empty_return() {
        let (tree, root) = parse("return;");
        let statement = root.stmts(&tree).next().unwrap();
        let return_stmt = match statement {
            Stmt::Return(return_stmt) => return_stmt,
            _ => unreachable!(),
        };

        assert!(return_stmt.value(&tree).is_none());
    }

    #[test]
    fn get_break_label_and_value() {
        let (tree, root) = parse("break blk` 1 + 2;");
        let statement = root.stmts(&tree).next().unwrap();
        let break_stmt = match statement {
            Stmt::Break(break_stmt) => break_stmt,
            _ => unreachable!(),
        };

        assert!(matches!(break_stmt.value(&tree), Some(Expr::Binary(_))));
        assert_eq!(
            break_stmt
                .label(&tree)
                .unwrap()
                .name(&tree)
                .unwrap()
                .text(&tree),
            "blk"
        );
    }

    #[test]
    fn get_empty_break() {
        let (tree, root) = parse("break;");
        let statement = root.stmts(&tree).next().unwrap();
        let break_stmt = match statement {
            Stmt::Break(break_stmt) => break_stmt,
            _ => unreachable!(),
        };

        assert!(break_stmt.value(&tree).is_none());
        assert!(break_stmt.label(&tree).is_none());
    }

    #[test]
    fn get_continue_label() {
        let (tree, root) = parse("continue blk`;");
        let statement = root.stmts(&tree).next().unwrap();
        let continue_stmt = match statement {
            Stmt::Continue(continue_stmt) => continue_stmt,
            _ => unreachable!(),
        };

        assert_eq!(
            continue_stmt
                .label(&tree)
                .unwrap()
                .name(&tree)
                .unwrap()
                .text(&tree),
            "blk"
        );
    }

    #[test]
    fn get_empty_continue() {
        let (tree, root) = parse("continue;");
        let statement = root.stmts(&tree).next().unwrap();
        let continue_stmt = match statement {
            Stmt::Continue(continue_stmt) => continue_stmt,
            _ => unreachable!(),
        };

        assert!(continue_stmt.label(&tree).is_none());
    }

    #[test]
    fn get_defer_expr() {
        let (tree, root) = parse("defer foo();");
        let statement = root.stmts(&tree).next().unwrap();
        let defer_stmt = match statement {
            Stmt::Defer(defer_stmt) => defer_stmt,
            _ => unreachable!(),
        };

        assert!(matches!(defer_stmt.expr(&tree), Some(Expr::Call(_))));
    }

    #[test]
    fn get_if_condition() {
        let (tree, root) = parse("if true {}");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let if_expr = match expr {
            Some(Expr::If(if_expr)) => if_expr,
            _ => unreachable!(),
        };

        let condition = if_expr.condition(&tree);

        assert!(matches!(condition, Some(Expr::BoolLiteral(_))));
    }

    #[test]
    fn get_if_body() {
        let (tree, root) = parse("if false { foo(); }");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let if_expr = match expr {
            Some(Expr::If(if_expr)) => if_expr,
            _ => unreachable!(),
        };

        let block = match if_expr.body(&tree).unwrap() {
            Expr::Block(block) => block,
            _ => unreachable!(),
        };

        let mut statements = block.stmts(&tree);

        assert!(matches!(statements.next(), Some(Stmt::Expr(_))));
    }

    #[test]
    fn get_else_body() {
        let (tree, root) = parse("if false {} else { x := 42; }");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let if_expr = match expr {
            Some(Expr::If(if_expr)) => if_expr,
            _ => unreachable!(),
        };

        let else_branch = if_expr.else_branch(&tree).unwrap();

        let block = match else_branch.body(&tree).unwrap() {
            Expr::Block(block) => block,
            _ => unreachable!(),
        };

        let mut statements = block.stmts(&tree);

        assert!(matches!(statements.next(), Some(Stmt::Define(_))));
    }

    #[test]
    fn get_else_if_condition() {
        let (tree, root) = parse("if false {} else if true {}");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let if_expr = match expr {
            Some(Expr::If(if_expr)) => if_expr,
            _ => unreachable!(),
        };

        let else_branch = if_expr.else_branch(&tree).unwrap();

        let if_expr = match else_branch.body(&tree).unwrap() {
            Expr::If(if_expr) => if_expr,
            _ => unreachable!(),
        };

        let condition = if_expr.condition(&tree);

        assert!(matches!(condition, Some(Expr::BoolLiteral(_))));
    }

    #[test]
    fn get_while_condition() {
        let (tree, root) = parse("while true {}");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let while_expr = match expr {
            Some(Expr::While(while_expr)) => while_expr,
            _ => unreachable!(),
        };

        let condition = while_expr.condition(&tree).unwrap().value(&tree);

        assert!(matches!(condition, Some(Expr::BoolLiteral(_))));
    }

    #[test]
    fn get_while_body() {
        let (tree, root) = parse("while true { bar(); }");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let while_expr = match expr {
            Some(Expr::While(while_expr)) => while_expr,
            _ => unreachable!(),
        };

        let block = match while_expr.body(&tree).unwrap() {
            Expr::Block(block) => block,
            _ => unreachable!(),
        };

        let mut statements = block.stmts(&tree);

        assert!(matches!(statements.next(), Some(Stmt::Expr(_))));
    }

    #[test]
    fn get_while_label() {
        let (tree, root) = parse("`outer while true { break outer` }");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let while_expr = match expr {
            Some(Expr::While(while_expr)) => while_expr,
            _ => unreachable!(),
        };

        assert_eq!(
            while_expr
                .label(&tree)
                .unwrap()
                .name(&tree)
                .unwrap()
                .text(&tree),
            "outer"
        );
    }

    #[test]
    fn get_loop_condition() {
        let (tree, root) = parse("loop { bar(); }");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let while_expr = match expr {
            Some(Expr::While(while_expr)) => while_expr,
            _ => unreachable!(),
        };

        assert!(while_expr.condition(&tree).is_none());
    }

    #[test]
    fn get_loop_label() {
        let (tree, root) = parse("`outer loop { break outer` }");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let while_expr = match expr {
            Some(Expr::While(while_expr)) => while_expr,
            _ => unreachable!(),
        };

        assert_eq!(
            while_expr
                .label(&tree)
                .unwrap()
                .name(&tree)
                .unwrap()
                .text(&tree),
            "outer"
        );
    }

    #[test]
    fn get_lambda_params() {
        let (tree, root) = parse("(x: i32, y: i32) {};");
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
        assert!(param.ellipsis(&tree).is_none());
        assert_eq!(param.ty(&tree).unwrap().text(&tree), "i32");

        let param = params.next().unwrap();
        assert_eq!(param.name(&tree).unwrap().text(&tree), "y");
        assert!(param.ellipsis(&tree).is_none());
        assert_eq!(param.ty(&tree).unwrap().text(&tree), "i32");

        assert!(params.next().is_none());
    }

    #[test]
    fn get_variadic_lambda_params() {
        let (tree, root) = parse("(x: i32, y: ...f32) {};");
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
        assert!(param.ellipsis(&tree).is_none());
        assert_eq!(param.ty(&tree).unwrap().text(&tree), "i32");

        let param = params.next().unwrap();
        assert_eq!(param.name(&tree).unwrap().text(&tree), "y");
        assert!(param.ellipsis(&tree).is_some());
        assert_eq!(param.ty(&tree).unwrap().text(&tree), "f32");

        assert!(params.next().is_none());
    }

    #[test]
    fn get_lambda_return_ty() {
        let (tree, root) = parse("() -> i32 {};");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let lambda = match expr {
            Some(Expr::Lambda(lambda)) => lambda,
            _ => unreachable!(),
        };

        let var_ref = match lambda.return_ty(&tree).unwrap().expr(&tree) {
            Some(Expr::VarRef(ty_ref)) => ty_ref,
            _ => unreachable!(),
        };

        assert_eq!(var_ref.name(&tree).unwrap().text(&tree), "i32");
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

    #[test]
    fn get_lambda_extern() {
        let (tree, root) = parse("() extern;");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let lambda = match expr {
            Some(Expr::Lambda(lambda)) => lambda,
            _ => unreachable!(),
        };

        assert!(lambda.body(&tree).is_none());
        assert!(lambda.r#extern(&tree).is_some());
    }

    #[test]
    fn no_lambda_body() {
        let (tree, root) = parse("() -> void;");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let lambda = match expr {
            Some(Expr::Lambda(lambda)) => lambda,
            _ => unreachable!(),
        };

        assert!(lambda.body(&tree).is_none());
    }

    #[test]
    fn get_lambda_builtin() {
        let (tree, root) = parse("() #builtin(\"bar\");");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let lambda = match expr {
            Some(Expr::Lambda(lambda)) => lambda,
            _ => unreachable!(),
        };

        let directive = match lambda.body(&tree).unwrap() {
            Expr::Directive(block) => block,
            _ => unreachable!(),
        };

        assert_eq!(directive.name(&tree).unwrap().text(&tree), "builtin");

        let mut arg_list = directive.arg_list(&tree).unwrap().args(&tree);
        assert_eq!(arg_list.next().unwrap().text(&tree), "\"bar\"");
        assert_eq!(arg_list.next(), None);
    }

    #[test]
    fn struct_decl_get_fields() {
        let (tree, root) = parse("struct { foo: i32, bar: string };");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let struct_decl = match expr {
            Some(Expr::StructDecl(struct_decl)) => struct_decl,
            _ => unreachable!(),
        };

        let mut fields = struct_decl.members(&tree);

        let field = fields.next();
        assert!(field.is_some());
        assert_eq!(field.unwrap().name(&tree).unwrap().text(&tree), "foo");
        assert_eq!(field.unwrap().ty(&tree).unwrap().text(&tree), "i32");

        let field = fields.next();
        assert!(field.is_some());
        assert_eq!(field.unwrap().name(&tree).unwrap().text(&tree), "bar");
        assert_eq!(field.unwrap().ty(&tree).unwrap().text(&tree), "string");

        assert!(fields.next().is_none());
    }

    #[test]
    fn struct_literal() {
        let (tree, root) = parse(r#"Some_Record_Type.{ foo = 123, bar = "hello" };"#);
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let struct_lit = match expr {
            Some(Expr::StructLiteral(struct_lit)) => struct_lit,
            _ => unreachable!(),
        };

        assert_eq!(
            struct_lit.ty(&tree).unwrap().text(&tree),
            "Some_Record_Type"
        );

        let mut fields = struct_lit.members(&tree);

        let field = fields.next();
        assert!(field.is_some());
        assert_eq!(field.unwrap().name(&tree).unwrap().text(&tree), "foo");
        assert!(matches!(
            field.unwrap().value(&tree),
            Some(Expr::IntLiteral(_))
        ));

        let field = fields.next();
        assert!(field.is_some());
        assert_eq!(field.unwrap().name(&tree).unwrap().text(&tree), "bar");
        assert!(matches!(
            field.unwrap().value(&tree),
            Some(Expr::StringLiteral(_))
        ));

        assert!(fields.next().is_none());
    }

    #[test]
    fn enum_decl_get_variants() {
        let (tree, root) = parse("enum { Ok, Hello | 1 + 2, Err: i32, Print: str | 42 };");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let enum_decl = match expr {
            Some(Expr::EnumDecl(enum_decl)) => enum_decl,
            _ => unreachable!(),
        };

        let mut variants = enum_decl.variants(&tree);

        let variant = variants.next();
        assert!(variant.is_some());
        assert_eq!(variant.unwrap().name(&tree).unwrap().text(&tree), "Ok");
        assert_eq!(variant.unwrap().ty(&tree), None);
        assert_eq!(variant.unwrap().discriminant(&tree), None);

        let variant = variants.next();
        assert!(variant.is_some());
        assert_eq!(variant.unwrap().name(&tree).unwrap().text(&tree), "Hello");
        assert_eq!(variant.unwrap().ty(&tree), None);
        assert!(matches!(
            variant.unwrap().discriminant(&tree).unwrap().value(&tree),
            Some(Expr::Binary { .. })
        ));

        let variant = variants.next();
        assert!(variant.is_some());
        assert_eq!(variant.unwrap().name(&tree).unwrap().text(&tree), "Err");
        assert_eq!(variant.unwrap().ty(&tree).unwrap().text(&tree), "i32");
        assert_eq!(variant.unwrap().discriminant(&tree), None);

        let variant = variants.next();
        assert!(variant.is_some());
        assert_eq!(variant.unwrap().name(&tree).unwrap().text(&tree), "Print");
        assert_eq!(variant.unwrap().ty(&tree).unwrap().text(&tree), "str");
        assert_eq!(
            variant
                .unwrap()
                .discriminant(&tree)
                .unwrap()
                .value(&tree)
                .unwrap()
                .text(&tree),
            "42"
        );

        assert!(variants.next().is_none());
    }

    #[test]
    fn anonymous_struct_literal() {
        let (tree, root) = parse(r#".{ a = true, b = 0.0, c = 'z' };"#);
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let struct_lit = match expr {
            Some(Expr::StructLiteral(struct_lit)) => struct_lit,
            _ => unreachable!(),
        };

        assert!(struct_lit.ty(&tree).is_none());

        let mut fields = struct_lit.members(&tree);

        let field = fields.next();
        assert!(field.is_some());
        assert_eq!(field.unwrap().name(&tree).unwrap().text(&tree), "a");
        assert!(matches!(
            field.unwrap().value(&tree),
            Some(Expr::BoolLiteral(_))
        ));

        let field = fields.next();
        assert!(field.is_some());
        assert_eq!(field.unwrap().name(&tree).unwrap().text(&tree), "b");
        assert!(matches!(
            field.unwrap().value(&tree),
            Some(Expr::FloatLiteral(_))
        ));

        let field = fields.next();
        assert!(field.is_some());
        assert_eq!(field.unwrap().name(&tree).unwrap().text(&tree), "c");
        assert!(matches!(
            field.unwrap().value(&tree),
            Some(Expr::CharLiteral(_))
        ));

        assert!(fields.next().is_none());
    }

    #[test]
    fn comptime_get_block() {
        let (tree, root) = parse("comptime { 2 + 2 }");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let comptime_expr = match expr {
            Some(Expr::Comptime(comptime_expr)) => comptime_expr,
            _ => unreachable!(),
        };

        let block = match comptime_expr.body(&tree) {
            Some(Expr::Block(block)) => block,
            _ => unreachable!(),
        };

        let binary = match block.tail_expr(&tree) {
            Some(Expr::Binary(binary)) => binary,
            _ => unreachable!(),
        };

        assert_eq!(binary.text(&tree), "2 + 2");
    }

    #[test]
    fn cast() {
        let (tree, root) = parse("u32.(4.2)");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let cast_expr = match expr {
            Some(Expr::Cast(cast_expr)) => cast_expr,
            _ => unreachable!(),
        };

        assert_eq!(
            cast_expr
                .ty(&tree)
                .unwrap()
                .expr(&tree)
                .unwrap()
                .text(&tree),
            "u32"
        );
        assert_eq!(cast_expr.expr(&tree).unwrap().text(&tree), "4.2");
    }

    #[test]
    fn switch() {
        // todo: do better tests for the arm variants
        let (tree, root) =
            parse("switch foo in bar { .Cow => 5, .Pig => \"hello\", .Chicken => foo }");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let switch_expr = match expr {
            Some(Expr::Switch(switch_expr)) => switch_expr,
            _ => panic!(),
        };

        assert_eq!(switch_expr.argument(&tree).unwrap().text(&tree), "foo");
        assert_eq!(switch_expr.scrutinee(&tree).unwrap().text(&tree), "bar");

        let mut switch_arms = switch_expr.arms(&tree);

        let arm = switch_arms.next().unwrap();
        let SwitchArmVariant::Shorthand(shorthand) = arm.variant(&tree).unwrap() else {
            panic!();
        };
        assert_eq!(shorthand.name(&tree).unwrap().text(&tree), "Cow");
        assert_eq!(arm.body(&tree).unwrap().text(&tree), "5");
        assert!(matches!(arm.body(&tree).unwrap(), Expr::IntLiteral(_)));

        let arm = switch_arms.next().unwrap();
        let SwitchArmVariant::Shorthand(shorthand) = arm.variant(&tree).unwrap() else {
            panic!();
        };
        assert_eq!(shorthand.name(&tree).unwrap().text(&tree), "Pig");
        assert_eq!(arm.body(&tree).unwrap().text(&tree), "\"hello\"");
        assert!(matches!(arm.body(&tree).unwrap(), Expr::StringLiteral(_)));

        let arm = switch_arms.next().unwrap();
        let SwitchArmVariant::Shorthand(shorthand) = arm.variant(&tree).unwrap() else {
            panic!();
        };
        assert_eq!(shorthand.name(&tree).unwrap().text(&tree), "Chicken");
        assert_eq!(arm.body(&tree).unwrap().text(&tree), "foo");
        assert!(matches!(arm.body(&tree).unwrap(), Expr::VarRef(_)));

        assert!(switch_arms.next().is_none());
    }

    #[test]
    fn mut_expr() {
        let (tree, root) = parse("mut foo");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let mut_expr = match expr {
            Some(Expr::Mut(mut_expr)) => mut_expr,
            _ => unreachable!(),
        };

        let var_ref = match mut_expr.expr(&tree) {
            Some(Expr::VarRef(ref_expr)) => ref_expr,
            _ => unreachable!(),
        };

        assert_eq!(var_ref.name(&tree).unwrap().text(&tree), "foo");
    }

    #[test]
    fn compiler_directives() {
        let (tree, root) = parse("#foo(10, 20);");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let directive = match expr {
            Some(Expr::Directive(directive)) => directive,
            _ => unreachable!(),
        };

        assert_eq!(directive.name(&tree).unwrap().text(&tree), "foo");

        let mut args = directive.arg_list(&tree).unwrap().args(&tree);

        assert_eq!(args.next().unwrap().value(&tree).unwrap().text(&tree), "10");
        assert_eq!(args.next().unwrap().value(&tree).unwrap().text(&tree), "20");
        assert!(args.next().is_none());
    }

    #[test]
    fn optional() {
        let (tree, root) = parse("?u64");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let Some(Expr::OptionalDecl(decl)) = expr else {
            unreachable!()
        };

        assert_eq!(decl.ty(&tree).unwrap().text(&tree), "u64");
    }

    #[test]
    fn optional_no_type() {
        let (tree, root) = parse("?");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let Some(Expr::OptionalDecl(decl)) = expr else {
            unreachable!()
        };

        assert_eq!(decl.ty(&tree), None);
    }

    #[test]
    fn error_union() {
        let (tree, root) = parse("str!u64");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let Some(Expr::ErrorUnionDecl(decl)) = expr else {
            unreachable!()
        };

        assert_eq!(
            decl.error_ty(&tree).unwrap().ty(&tree).unwrap().text(&tree),
            "str"
        );
        assert_eq!(
            decl.payload_ty(&tree)
                .unwrap()
                .ty(&tree)
                .unwrap()
                .text(&tree),
            "u64"
        );
    }

    #[test]
    fn error_union_missing_payload() {
        let (tree, root) = parse("str!");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let Some(Expr::ErrorUnionDecl(decl)) = expr else {
            unreachable!()
        };

        assert_eq!(
            decl.error_ty(&tree).unwrap().ty(&tree).unwrap().text(&tree),
            "str"
        );
        assert_eq!(decl.payload_ty(&tree), None);
    }

    #[test]
    fn propagate() {
        let (tree, root) = parse("foo.try");
        let statement = root.stmts(&tree).next().unwrap();
        let expr = match statement {
            Stmt::Expr(expr_stmt) => expr_stmt.expr(&tree),
            _ => unreachable!(),
        };

        let Some(Expr::Propagate(prop)) = expr else {
            unreachable!()
        };

        assert_eq!(prop.expr(&tree).unwrap().text(&tree), "foo");
    }
}

use syntax::TokenKind;

use crate::{parser::marker::Marker, token_set::TokenSet, ExpectedSyntax};

use super::*;

pub(super) fn parse_expr(
    p: &mut Parser,
    expected_syntax_name: &'static str,
) -> Option<CompletedMarker> {
    parse_expr_bp(p, 0, TokenSet::NONE, expected_syntax_name)
}

#[allow(unused)]
pub(super) fn parse_expr_with_recovery_set(
    p: &mut Parser,
    expected_syntax_name: &'static str,
    recovery_set: TokenSet,
) -> Option<CompletedMarker> {
    parse_expr_bp(p, 0, recovery_set, expected_syntax_name)
}

pub(super) fn parse_ty(
    p: &mut Parser,
    expected_syntax_name: &'static str,
    recovery_set: TokenSet,
) -> Option<CompletedMarker> {
    let cm = parse_lhs(p, recovery_set, expected_syntax_name)?;
    let cm = parse_post_operators(p, recovery_set, cm, true, true);

    let m = cm.precede(p);
    Some(m.complete(p, NodeKind::Ty))
}

// this is used so that certain postfix operators are applied after prefix operators.
//
// notably, this allows `^foo^` to be parsed as `(^foo)^`
fn parse_expr_for_prefix(
    p: &mut Parser,
    recovery_set: TokenSet,
    expected_syntax_name: &'static str,
) -> Option<CompletedMarker> {
    let cm = parse_lhs(p, recovery_set, expected_syntax_name)?;
    Some(parse_post_operators(p, recovery_set, cm, true, false))
}

// bp stands for binding power
// look at online resources for more
fn parse_expr_bp(
    p: &mut Parser,
    minimum_bp: u8,
    recovery_set: TokenSet,
    expected_syntax_name: &'static str,
) -> Option<CompletedMarker> {
    let mut lhs = parse_lhs(p, recovery_set, expected_syntax_name)?;

    loop {
        lhs = parse_post_operators(p, recovery_set, lhs, false, false);

        let (left_bp, right_bp) = if p.at(TokenKind::DoublePipe) {
            (1, 2)
        } else if p.at(TokenKind::DoubleAnd) {
            (3, 4)
        } else if p.at_set(TokenSet::new([
            TokenKind::Left,
            TokenKind::LeftEquals,
            TokenKind::Right,
            TokenKind::RightEquals,
            TokenKind::DoubleEquals,
            TokenKind::BangEquals,
        ])) {
            (5, 6)
        } else if p.at_set(TokenSet::new([
            TokenKind::Plus,
            TokenKind::Hyphen,
            TokenKind::Pipe,
            TokenKind::Tilde,
        ])) {
            (7, 8)
        } else if p.at_set(TokenSet::new([
            TokenKind::Asterisk,
            TokenKind::Slash,
            TokenKind::Percent,
            TokenKind::And,
            TokenKind::DoubleLeft,
            TokenKind::DoubleRight,
        ])) {
            (9, 10)
        } else {
            break;
        };

        if left_bp < minimum_bp {
            break;
        }

        p.bump(); // bump operator

        let m = lhs.precede(p);
        parse_expr_bp(p, right_bp, recovery_set, "operand");
        lhs = m.complete(p, NodeKind::BinaryExpr);
    }

    Some(lhs)
}

fn parse_lhs(
    p: &mut Parser,
    recovery_set: TokenSet,
    expected_syntax_name: &'static str,
) -> Option<CompletedMarker> {
    let _guard = p.expected_syntax_name(expected_syntax_name);

    // println!("parse_lhs @ {:?}", p.peek());

    const LOOP_TOKENS: TokenSet = TokenSet::new([TokenKind::While, TokenKind::Loop]);
    const PREFIX_TOKENS: TokenSet = TokenSet::new([
        TokenKind::Hyphen,
        TokenKind::Plus,
        TokenKind::Bang,
        TokenKind::Tilde,
    ]);

    let cm = if p.at(TokenKind::Int) || p.at(TokenKind::Hex) || p.at(TokenKind::Bin) {
        parse_int_literal(p)
    } else if p.at(TokenKind::Float) {
        parse_float_literal(p)
    } else if p.at(TokenKind::Bool) {
        parse_bool_literal(p)
    } else if p.at(TokenKind::DoubleQuote) {
        parse_string_literal(p)
    } else if p.at(TokenKind::SingleQuote) {
        parse_char_literal(p)
    } else if p.at(TokenKind::Ident) {
        parse_var_ref(p)
    } else if p.at(TokenKind::Caret) {
        parse_ref(p, recovery_set)
    } else if p.at(TokenKind::Mut) {
        parse_mut(p, recovery_set)
    } else if p.at(TokenKind::Distinct) {
        parse_distinct(p, recovery_set)
    } else if p.at_set(TokenSet::new([TokenKind::Import, TokenKind::Mod])) {
        parse_import_or_mod(p)
    } else if p.at(TokenKind::Comptime) {
        parse_comptime(p)
    } else if p.at(TokenKind::Struct) {
        parse_struct_decl(p, recovery_set)
    } else if p.at(TokenKind::Enum) {
        parse_enum_decl(p, recovery_set)
    } else if p.at_set(PREFIX_TOKENS) {
        parse_prefix_expr(p, recovery_set)
    } else if p.at(TokenKind::If) {
        parse_if(
            p,
            recovery_set.union(TokenSet::new([TokenKind::If, TokenKind::Else])),
        )
    } else if p.at_set(LOOP_TOKENS) {
        parse_loop(p, None, recovery_set)
    } else if p.at(TokenKind::Switch) {
        parse_switch(p, recovery_set)
    } else if p.at(TokenKind::LParen) {
        parse_lambda(p, recovery_set)
    } else if p.at(TokenKind::LBrack) {
        parse_array_decl(p, recovery_set)
    } else if p.at(TokenKind::LBrace) {
        parse_block(p, None, recovery_set)
    } else if p.at(TokenKind::Dot) && p.at_ahead(1, TokenSet::new([TokenKind::LParen])) {
        parse_cast(p, None, recovery_set)
    } else if p.at(TokenKind::Dot) && p.at_ahead(1, TokenSet::new([TokenKind::LBrack])) {
        parse_array_literal(p, None, recovery_set, None)
    } else if p.at(TokenKind::Dot) && p.at_ahead(1, TokenSet::new([TokenKind::LBrace])) {
        parse_struct_literal(p, None, recovery_set)
    } else if p.at(TokenKind::Backtick) {
        let label = p.start();
        p.bump();

        let _guard = p.expected_syntax_name("label name");
        p.expect_with_no_skip(TokenKind::Ident);

        let label = label.complete(p, NodeKind::LabelDecl);

        if p.at_set(LOOP_TOKENS) {
            parse_loop(p, Some(label), recovery_set)
        } else if p.at(TokenKind::LBrace) {
            parse_block(p, Some(label), recovery_set)
        } else {
            let _guard = p.expected_syntax_name("block");
            p.error_with_no_skip();

            return parse_lhs(p, recovery_set, expected_syntax_name);
        }
    } else {
        // println!("error {:?} {} {:?}", p.peek(), p.at_eof(), p.peek_range());
        return p.error_with_recovery_set(recovery_set);
    };

    Some(cm)
}

// `no_derefs` disallows `foo^` expressions
// `no_dot_instantiation` disallows `foo.()`, `foo.{}`, and `foo.[]` expressions
fn parse_post_operators(
    p: &mut Parser,
    recovery_set: TokenSet,
    cm: CompletedMarker,
    no_derefs: bool,
    no_dot_instantiation: bool,
) -> CompletedMarker {
    let mut cm = cm;

    // the ONLY reason this is included is to recover when parsing older syntax
    if matches!(cm.kind(), NodeKind::VarRef)
        && !recovery_set.contains(TokenKind::LBrace)
        && p.at(TokenKind::LBrace)
    {
        let ty_cm = cm.precede(p).complete(p, NodeKind::Ty);
        cm = parse_struct_literal(p, Some(ty_cm), recovery_set);
    }

    loop {
        match p.kind() {
            Some(TokenKind::LBrack) => {
                if p.at_ahead(2, TokenSet::new([TokenKind::Comma])) {
                    let ty_cm = cm.precede(p).complete(p, NodeKind::Ty);
                    cm = parse_array_literal(p, Some(ty_cm), recovery_set, None)
                } else {
                    let indexing_expr = cm.precede(p).complete(p, NodeKind::Source).precede(p);
                    p.bump();

                    let real_index = p.start();
                    parse_expr(p, "array index");
                    real_index.complete(p, NodeKind::Index);

                    p.expect_with_no_skip(TokenKind::RBrack);

                    cm = indexing_expr.complete(p, NodeKind::IndexExpr);
                }
            }
            Some(TokenKind::LParen) => {
                let call = cm.precede(p);

                let arg_list_m = p.start();

                p.bump();

                // collect arguments
                loop {
                    if p.at(TokenKind::RParen) {
                        break;
                    }
                    if let Some(arg_m) = expr::parse_expr(p, "argument") {
                        arg_m.precede(p).complete(p, NodeKind::Arg);
                    }

                    if p.at_eof() || p.at_default_recovery_set() {
                        break;
                    }

                    if !p.at(TokenKind::RParen) {
                        p.expect_with_no_skip(TokenKind::Comma);
                    }
                }

                p.expect(TokenKind::RParen);

                arg_list_m.complete(p, NodeKind::ArgList);

                cm = call.complete(p, NodeKind::Call);
            }
            Some(TokenKind::Caret) if !no_derefs => {
                let deref = cm.precede(p);
                p.bump();
                cm = deref.complete(p, NodeKind::DerefExpr);
            }
            // this is included so that old syntax is still correctly parsed
            // and an error can be reported
            Some(TokenKind::As) if !no_derefs => {
                let cast = cm.precede(p);
                p.bump();

                parse_ty(p, "cast type", recovery_set);

                cm = cast.complete(p, NodeKind::CastExpr);

                let end_token = p.token_idx.saturating_sub(1).max(cm.start_token_idx());

                p.mark_old_unexpected(
                    NodeKind::CastExpr,
                    cm.start_token_idx(),
                    end_token,
                    crate::ExpectedSyntax::Named("`.( )` cast syntax"),
                );
            }
            Some(TokenKind::Dot) => {
                if p.at_ahead(1, TokenSet::new([TokenKind::LParen])) {
                    if no_dot_instantiation {
                        break;
                    }
                    let ty_cm = cm.precede(p).complete(p, NodeKind::Ty);
                    cm = parse_cast(p, Some(ty_cm), recovery_set)
                } else if p.at_ahead(1, TokenSet::new([TokenKind::LBrace])) {
                    if no_dot_instantiation {
                        break;
                    }
                    let ty_cm = cm.precede(p).complete(p, NodeKind::Ty);
                    cm = parse_struct_literal(p, Some(ty_cm), recovery_set)
                } else if p.at_ahead(1, TokenSet::new([TokenKind::LBrack])) {
                    if no_dot_instantiation {
                        break;
                    }
                    let ty_cm = cm.precede(p).complete(p, NodeKind::Ty);
                    cm = parse_array_literal(p, Some(ty_cm), recovery_set, None)
                } else {
                    let path = cm.precede(p);
                    p.bump();

                    if p.at(TokenKind::Ident) {
                        p.bump();
                    } else {
                        let _guard = p.expected_syntax_name("field name");
                        p.error_with_no_skip();
                    }

                    cm = path.complete(p, NodeKind::Path);
                }
            }
            _ => break,
        }
    }

    // same as above.
    // i kinda forgot why i included two of these here but i'm sure it's important
    if matches!(cm.kind(), NodeKind::Path | NodeKind::VarRef)
        && !recovery_set.contains(TokenKind::LBrace)
        && p.at(TokenKind::LBrace)
    {
        let ty_cm = cm.precede(p).complete(p, NodeKind::Ty);
        cm = parse_struct_literal(p, Some(ty_cm), recovery_set);
    }

    cm
}

fn parse_int_literal(p: &mut Parser) -> CompletedMarker {
    assert!(p.at(TokenKind::Int) || p.at(TokenKind::Hex) || p.at(TokenKind::Bin));
    let m = p.start();
    p.bump();
    m.complete(p, NodeKind::IntLiteral)
}

fn parse_float_literal(p: &mut Parser) -> CompletedMarker {
    assert!(p.at(TokenKind::Float));
    let m = p.start();
    p.bump();
    m.complete(p, NodeKind::FloatLiteral)
}

fn parse_bool_literal(p: &mut Parser) -> CompletedMarker {
    assert!(p.at(TokenKind::Bool));
    let m = p.start();
    p.bump();
    m.complete(p, NodeKind::BoolLiteral)
}

pub(crate) fn parse_string_literal(p: &mut Parser) -> CompletedMarker {
    assert!(p.at(TokenKind::DoubleQuote));
    let m = p.start();
    p.bump();

    while p.at(TokenKind::StringContents) || p.at(TokenKind::Escape) {
        p.bump();
    }

    p.expect(TokenKind::DoubleQuote);
    m.complete(p, NodeKind::StringLiteral)
}

pub(crate) fn parse_char_literal(p: &mut Parser) -> CompletedMarker {
    assert!(p.at(TokenKind::SingleQuote));
    let m = p.start();
    p.bump();

    while p.at(TokenKind::StringContents) || p.at(TokenKind::Escape) {
        p.bump();
    }

    p.expect(TokenKind::SingleQuote);
    m.complete(p, NodeKind::CharLiteral)
}

fn parse_ref(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    assert!(p.at(TokenKind::Caret));
    let m = p.start();
    p.bump();

    if p.at(TokenKind::Mut) {
        p.bump();
    }

    parse_expr_for_prefix(p, recovery_set, "operand");

    m.complete(p, NodeKind::RefExpr)
}

fn parse_mut(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    let start_idx = p.token_idx;

    assert!(p.at(TokenKind::Mut));
    let m = p.start();
    p.bump();

    let expr = parse_expr_for_prefix(p, recovery_set, "operand");

    // anything other than `mut rawptr` will produce an error
    if !expr.is_some_and(|expr| {
        expr.kind() == NodeKind::VarRef && p.text(expr.start_token_idx()) == "rawptr"
    }) {
        p.mark_old_missing(start_idx, ExpectedSyntax::Unnamed(TokenKind::Caret));
    }

    m.complete(p, NodeKind::MutExpr)
}

fn parse_distinct(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    assert!(p.at(TokenKind::Distinct));
    let m = p.start();
    p.bump();

    parse_ty(p, "type", recovery_set);

    m.complete(p, NodeKind::Distinct)
}

fn parse_import_or_mod(p: &mut Parser) -> CompletedMarker {
    assert!(p.at_set(TokenSet::new([TokenKind::Import, TokenKind::Mod])));
    let m = p.start();
    p.bump();

    if p.at(TokenKind::DoubleQuote) {
        expr::parse_string_literal(p);
    } else {
        let _guard = p.expected_syntax_name("file name string");
        p.error();
    }

    m.complete(p, NodeKind::ImportExpr)
}

fn parse_var_ref(p: &mut Parser) -> CompletedMarker {
    assert!(p.at(TokenKind::Ident));
    let m = p.start();

    p.bump();

    m.complete(p, NodeKind::VarRef)
}

fn parse_prefix_expr(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    assert!(p.at_set(TokenSet::new([
        TokenKind::Hyphen,
        TokenKind::Plus,
        TokenKind::Bang,
        TokenKind::Tilde
    ])));

    let m = p.start();

    // Eat the operator’s token.
    p.bump();
    parse_expr_for_prefix(p, recovery_set, "operand");
    m.complete(p, NodeKind::UnaryExpr)
}

fn parse_lambda(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    assert!(p.at(TokenKind::LParen));

    // detect if this lambda is really a parenthetical expression
    'detect_paren: {
        let mut depth = 1;
        let saved_idx = p.token_idx;

        let mut had_param_tokens = false;
        let mut had_non_param_tokens = false;

        // this is a hard distinction to make, the main telltale is if the lambda has a return type or
        // if it has a body
        loop {
            p.token_idx += 1;

            if depth == 0 {
                break;
            }

            let Some(kind) = p.peek() else {
                p.token_idx = saved_idx;
                if !had_param_tokens && had_non_param_tokens {
                    return parse_paren(p, recovery_set);
                } else {
                    break 'detect_paren;
                }
            };

            // only the top level of a parameter list could have these tokens
            const PARAM_ONLY: TokenSet = TokenSet::new([TokenKind::Colon, TokenKind::Comma]);

            if depth == 1 && kind != TokenKind::RParen {
                if PARAM_ONLY.contains(kind) {
                    had_param_tokens = true;
                } else {
                    had_non_param_tokens = true;
                }
            }

            match kind {
                TokenKind::LParen | TokenKind::LBrack | TokenKind::LBrace => {
                    depth += 1;
                }
                TokenKind::RParen | TokenKind::RBrack | TokenKind::RBrace => {
                    depth -= 1;
                }
                _ => {}
            }
        }

        // the top level of the parentheses contained no idents, colons, or commas
        if !had_param_tokens && had_non_param_tokens {
            p.token_idx = saved_idx;
            return parse_paren(p, recovery_set);
        }

        if had_param_tokens {
            p.token_idx = saved_idx;
            break 'detect_paren;
        }

        let Some(kind) = p.peek() else {
            p.token_idx = saved_idx;
            return parse_paren(p, recovery_set);
        };

        const AFTER_PARAMS: TokenSet =
            TokenSet::new([TokenKind::Arrow, TokenKind::LBrace, TokenKind::Extern]);

        if !AFTER_PARAMS.contains(kind) {
            p.token_idx = saved_idx;
            return parse_paren(p, recovery_set);
        } else {
            p.token_idx = saved_idx;
        }
    }

    let m = p.start();

    let param_list_m = p.start();

    p.bump();

    loop {
        if p.at(TokenKind::RParen) {
            break;
        }

        let param_m = p.start();
        {
            let _guard = p.expected_syntax_name("parameter name");
            p.expect(TokenKind::Ident);
        }

        p.expect_with_no_skip(TokenKind::Colon);

        parse_ty(
            p,
            "parameter type",
            TokenSet::new([TokenKind::Comma, TokenKind::RParen]),
        );

        param_m.complete(p, NodeKind::Param);

        if p.at_eof() || p.at_default_recovery_set() {
            break;
        }

        if !p.at(TokenKind::RParen) {
            p.expect_with_no_skip(TokenKind::Comma);
        }
    }
    p.expect_with_recovery_set(
        TokenKind::RParen,
        TokenSet::new([TokenKind::Arrow, TokenKind::LBrace]),
    );

    param_list_m.complete(p, NodeKind::ParamList);

    const BODY: TokenSet = TokenSet::new([TokenKind::LBrace, TokenKind::Extern]);

    if !p.at_set(BODY) {
        p.expect_with_no_skip(TokenKind::Arrow);

        if !p.at_set(BODY) {
            parse_ty(
                p,
                "return type",
                recovery_set.union(TokenSet::new([TokenKind::LBrace])),
            );
        } else {
            let _guard = p.expected_syntax_name("return type");
            p.error_with_no_skip();
        }
    }

    if p.at(TokenKind::LBrace) {
        parse_block(p, None, recovery_set);
    } else if p.at(TokenKind::Extern) {
        p.bump();
    }

    m.complete(p, NodeKind::Lambda)
}

fn parse_paren(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    assert!(p.at(TokenKind::LParen));

    let m = p.start();
    p.bump();

    if p.at(TokenKind::RParen) {
        p.bump();
        return m.complete(p, NodeKind::ParenExpr);
    }

    parse_expr_with_recovery_set(p, "expression", recovery_set);

    p.expect_with_no_skip(TokenKind::RParen);
    m.complete(p, NodeKind::ParenExpr)
}

fn parse_cast(
    p: &mut Parser,
    previous_ty: Option<CompletedMarker>,
    recovery_set: TokenSet,
) -> CompletedMarker {
    if let Some(previous_ty) = previous_ty {
        assert_eq!(previous_ty.kind(), NodeKind::Ty);
    } else {
        let _guard = p.expected_syntax_name("type");
        p.error_with_no_skip();
    }

    let at_dot = p.at(TokenKind::Dot);
    let next_paren = p.at_ahead(1, TokenSet::new([TokenKind::LParen]));

    assert!(at_dot && next_paren);

    let m = previous_ty
        .map(|ty| ty.precede(p))
        .unwrap_or_else(|| p.start());

    // we already asserted before, so this is safe
    p.bump();
    p.bump();

    if !p.at(TokenKind::RParen) {
        parse_expr_with_recovery_set(
            p,
            "cast value",
            recovery_set.union(TokenSet::new([TokenKind::Comma, TokenKind::RParen])),
        );
    }

    p.expect_with_recovery_set(TokenKind::RParen, recovery_set);

    m.complete(p, NodeKind::CastExpr)
}

fn parse_struct_decl(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    assert!(p.at(TokenKind::Struct));

    let m = p.start();

    p.bump();

    if p.at(TokenKind::LBrace) {
        p.bump();
    } else {
        let _guard = p.expected_syntax_name("struct body");
        p.error_with_recovery_set(recovery_set);

        return m.complete(p, NodeKind::StructDecl);
    }

    loop {
        if p.at(TokenKind::RBrace) {
            break;
        }

        let field_m = p.start();
        let _guard = p.expected_syntax_name("field name");
        p.expect(TokenKind::Ident);

        p.expect_with_no_skip(TokenKind::Colon);

        parse_ty(
            p,
            "field type",
            recovery_set.union(TokenSet::new([TokenKind::Comma, TokenKind::RBrace])),
        );

        field_m.complete(p, NodeKind::MemberDecl);

        if p.at_eof() || p.at_default_recovery_set() {
            break;
        }

        if !p.at(TokenKind::RBrace) {
            p.expect_with_no_skip(TokenKind::Comma);
        }
    }
    p.expect(TokenKind::RBrace);

    m.complete(p, NodeKind::StructDecl)
}

fn parse_struct_literal(
    p: &mut Parser,
    previous_ty: Option<CompletedMarker>,
    recovery_set: TokenSet,
) -> CompletedMarker {
    if let Some(previous_ty) = previous_ty {
        assert_eq!(previous_ty.kind(), NodeKind::Ty);
    }

    let at_dot = p.at(TokenKind::Dot);
    let at_lbrace = p.at(TokenKind::LBrace);
    let next_lbrace = p.at_ahead(1, TokenSet::new([TokenKind::LBrace]));

    if at_dot {
        assert!(next_lbrace);
    } else {
        assert!(at_lbrace);
    }

    let m = previous_ty
        .map(|ty| ty.precede(p))
        .unwrap_or_else(|| p.start());

    p.expect_with_no_skip(TokenKind::Dot);
    p.bump();

    loop {
        if p.at(TokenKind::RBrace) {
            break;
        }

        let field_m = p.start();
        let _guard = p.expected_syntax_name("field name");
        p.expect_with_no_skip(TokenKind::Ident);

        if p.at(TokenKind::Colon) {
            p.expect(TokenKind::Equals);
        } else {
            p.expect_with_no_skip(TokenKind::Equals);
        }

        parse_expr_with_recovery_set(
            p,
            "field value",
            recovery_set.union(TokenSet::new([TokenKind::Comma, TokenKind::RBrace])),
        );

        field_m.complete(p, NodeKind::MemberLiteral);

        if p.at_eof() || p.at_default_recovery_set() {
            break;
        }

        if !p.at(TokenKind::RBrace) {
            p.expect_with_no_skip(TokenKind::Comma);
        }
    }
    p.expect_with_recovery_set(TokenKind::RBrace, recovery_set);

    m.complete(p, NodeKind::StructLiteral)
}

fn parse_enum_decl(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    assert!(p.at(TokenKind::Enum));

    let m = p.start();

    p.bump();

    if p.at(TokenKind::LBrace) {
        p.bump();
    } else {
        let _guard = p.expected_syntax_name("enum body");
        p.error_with_recovery_set(recovery_set);

        return m.complete(p, NodeKind::EnumDecl);
    }

    loop {
        if p.at(TokenKind::RBrace) {
            break;
        }

        let variant_m = p.start();
        let _guard = p.expected_syntax_name("variant name");
        p.expect(TokenKind::Ident);

        if p.at(TokenKind::Colon) {
            p.bump();

            parse_ty(
                p,
                "variant type",
                recovery_set.union(TokenSet::new([TokenKind::Comma, TokenKind::RBrace])),
            );
        }

        if p.at(TokenKind::Pipe) {
            let discriminant_m = p.start();
            p.bump();

            parse_expr(p, "custom discriminant");

            discriminant_m.complete(p, NodeKind::Discriminant);
        }

        variant_m.complete(p, NodeKind::VariantDecl);

        if p.at_eof() || p.at_default_recovery_set() {
            break;
        }

        if !p.at(TokenKind::RBrace) {
            p.expect_with_no_skip(TokenKind::Comma);
        }
    }
    p.expect(TokenKind::RBrace);

    m.complete(p, NodeKind::EnumDecl)
}

/// `array_decl` is ONLY used by `parse_array_decl` to pass it's previously created marker.
/// This allows the array literal to completely replace the array declaration.
///
/// If previous_ty is set to None, this will be treated as an untyped array literal
/// `.[1, 2, 3]`
fn parse_array_literal(
    p: &mut Parser,
    previous_ty: Option<CompletedMarker>,
    recovery_set: TokenSet,
    array_decl: Option<Marker>,
) -> CompletedMarker {
    if let Some(previous_ty) = previous_ty {
        assert_eq!(previous_ty.kind(), NodeKind::Ty);
    }

    let at_dot = p.at(TokenKind::Dot);
    let at_lbrace = p.at(TokenKind::LBrace);
    let at_lbrack = p.at(TokenKind::LBrack);
    let next_lbrack = p.at_ahead(1, TokenSet::new([TokenKind::LBrack]));

    if at_dot {
        assert!(next_lbrack);
    } else {
        assert!(at_lbrace || at_lbrack);
    }

    let m = array_decl
        .or_else(|| previous_ty.map(|ty| ty.precede(p)))
        .unwrap_or_else(|| p.start());

    const DEFAULT_NO_BRACES: TokenSet = crate::parser::DEFAULT_RECOVERY_SET
        .without(TokenKind::LBrace)
        .without(TokenKind::RBrace);

    p.expect_with_no_skip(TokenKind::Dot);
    // if we are `at_lbrace` this will report an error
    p.expect_with_recovery_set_no_default(TokenKind::LBrack, DEFAULT_NO_BRACES);

    loop {
        if p.at(TokenKind::RBrack) || p.at(TokenKind::RBrace) {
            break;
        }

        if let Some(item) = parse_expr_with_recovery_set(p, "array item", recovery_set) {
            item.precede(p).complete(p, NodeKind::ArrayItem);
        }

        if p.at_eof() || p.at_default_recovery_set() {
            break;
        }

        if !p.at(TokenKind::RBrack) && !p.at(TokenKind::RBrace) {
            p.expect_with_no_skip(TokenKind::Comma);
        }
    }
    p.expect_with_recovery_set_no_default(TokenKind::RBrack, DEFAULT_NO_BRACES);

    m.complete(p, NodeKind::ArrayLiteral)
}

fn parse_array_decl(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    assert!(p.at(TokenKind::LBrack));

    let array = p.start();

    let size = p.start();
    let size_start = p.token_idx;
    p.bump();

    if !p.at(TokenKind::RBrack) {
        parse_expr(p, "array size");
    }

    p.expect_with_recovery_set(
        TokenKind::RBrack,
        recovery_set.union(TokenSet::new([TokenKind::LBrace])),
    );

    size.complete(p, NodeKind::ArraySize);
    let size_end = p.token_idx;

    let ty = parse_ty(
        p,
        "array type",
        recovery_set.union(TokenSet::new([TokenKind::LBrace])),
    );

    // make sure someone isn't using the wrong syntax
    match ty {
        Some(ty) if !recovery_set.contains(TokenKind::LBrace) && p.at(TokenKind::LBrace) => {
            p.mark_old_unexpected(
                NodeKind::ArraySize,
                size_start,
                size_end,
                crate::ExpectedSyntax::Named("nothing"),
            );
            parse_array_literal(p, Some(ty), recovery_set, Some(array))
        }
        _ => {
            let array_decl = array.complete(p, NodeKind::ArrayDecl);

            if !recovery_set.contains(TokenKind::LParen)
                && p.at(TokenKind::Dot)
                && p.at_ahead(1, TokenSet::new([TokenKind::LParen]))
            {
                let array_ty = array_decl.precede(p).complete(p, NodeKind::Ty);
                parse_cast(p, Some(array_ty), recovery_set)
            } else {
                array_decl
            }
        }
    }
}

fn parse_if(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    assert!(p.at(TokenKind::If));

    let m = p.start();
    p.bump();

    parse_expr_with_recovery_set(
        p,
        "condition",
        recovery_set.union(TokenSet::new([TokenKind::LBrace])),
    );

    if p.at(TokenKind::LBrace) {
        parse_block(p, None, recovery_set);
    } else {
        let _guard = p.expected_syntax_name("if body");
        p.error_with_recovery_set(recovery_set);
    }

    if p.at(TokenKind::Else) {
        let else_m = p.start();
        p.bump();

        if p.at(TokenKind::If) {
            parse_if(p, recovery_set);
        } else if p.at(TokenKind::LBrace) {
            parse_block(p, None, recovery_set);
        } else {
            let _guard = p.expected_syntax_name("else body");
            p.error_with_recovery_set(recovery_set);
        }

        else_m.complete(p, NodeKind::ElseBranch);
    }

    m.complete(p, NodeKind::IfExpr)
}

fn parse_loop(
    p: &mut Parser,
    label: Option<CompletedMarker>,
    recovery_set: TokenSet,
) -> CompletedMarker {
    let at_while = p.at(TokenKind::While);
    let at_loop = p.at(TokenKind::Loop);
    assert!(at_while || at_loop);

    let m = if let Some(label) = label {
        label.precede(p)
    } else {
        p.start()
    };

    p.bump();

    if at_while {
        let m = p.start();
        parse_expr_with_recovery_set(
            p,
            "condition",
            recovery_set.union(TokenSet::new([TokenKind::LBrace])),
        );
        m.complete(p, NodeKind::Condition);
    }

    if p.at(TokenKind::LBrace) {
        parse_block(p, None, recovery_set);
    } else {
        let _guard = if at_while {
            p.expected_syntax_name("while body")
        } else {
            p.expected_syntax_name("loop body")
        };
        p.error_with_recovery_set(recovery_set);
    }

    m.complete(p, NodeKind::WhileExpr)
}

fn parse_switch(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    assert!(p.at(TokenKind::Switch));

    let m = p.start();
    p.bump();

    if p.at(TokenKind::Ident)
        && (p.at_ahead(1, TokenSet::new([TokenKind::In])) || p.at_eof_ahead(1))
    {
        // todo: pick better syntax name
        let _guard = p.expected_syntax_name("switch parameter name");
        p.expect(TokenKind::Ident);

        p.expect_with_recovery_set(
            TokenKind::In,
            recovery_set.union(TokenSet::new([TokenKind::LBrace])),
        );
    }

    // todo: pick better syntax name
    parse_expr_with_recovery_set(
        p,
        "enum value",
        recovery_set.union(TokenSet::new([TokenKind::LBrace])),
    );

    if p.at(TokenKind::LBrace) {
        p.bump();

        loop {
            if p.at(TokenKind::RBrace) {
                break;
            }

            let arm_m = p.start();
            {
                let _guard = p.expected_syntax_name("enum variant name");
                p.expect(TokenKind::Ident);
            }

            p.expect_with_no_skip(TokenKind::FatArrow);

            let at_lbrace = p.at(TokenKind::LBrace);
            parse_expr_with_recovery_set(p, "switch arm", recovery_set);

            arm_m.complete(p, NodeKind::SwitchArm);

            if p.at_eof() || p.at_default_recovery_set() {
                break;
            }

            if (at_lbrace && p.at(TokenKind::Comma)) || (!at_lbrace && !p.at(TokenKind::RBrace)) {
                p.expect_with_no_skip(TokenKind::Comma);
            }
        }

        p.expect_with_recovery_set(TokenKind::RBrace, recovery_set);
    } else {
        let _guard = p.expected_syntax_name("switch body");
        p.error_with_recovery_set(recovery_set);
    }

    m.complete(p, NodeKind::SwitchExpr)
}

fn parse_comptime(p: &mut Parser) -> CompletedMarker {
    assert!(p.at(TokenKind::Comptime));

    let m = p.start();
    p.bump();

    parse_expr(p, "comptime body");

    m.complete(p, NodeKind::ComptimeExpr)
}

fn parse_block(
    p: &mut Parser,
    label: Option<CompletedMarker>,
    recovery_set: TokenSet,
) -> CompletedMarker {
    assert!(p.at(TokenKind::LBrace));

    let m = if let Some(label) = label {
        label.precede(p)
    } else {
        p.start()
    };

    p.bump();

    while !p.at(TokenKind::RBrace) && !p.at_eof() {
        stmt::parse_stmt(p, false);
    }

    p.expect_with_recovery_set(TokenKind::RBrace, recovery_set);

    m.complete(p, NodeKind::Block)
}

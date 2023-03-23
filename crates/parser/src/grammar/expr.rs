use syntax::TokenKind;

use crate::{
    grammar::{path::parse_path, ty::parse_ty},
    token_set::TokenSet,
};

use super::*;

pub(super) fn parse_expr(
    p: &mut Parser,
    expected_syntax_name: &'static str,
) -> Option<CompletedMarker> {
    parse_expr_bp(p, 0, TokenSet::NONE, expected_syntax_name)
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
        let (left_bp, right_bp) = if p.at(TokenKind::Plus) || p.at(TokenKind::Hyphen) {
            (1, 2)
        } else if p.at(TokenKind::Asterisk) || p.at(TokenKind::Slash) {
            (3, 4)
        } else if p.at(TokenKind::DoubleEquals) || p.at(TokenKind::BangEquals) {
            (5, 6)
        } else if p.at(TokenKind::Less)
            || p.at(TokenKind::LessEquals)
            || p.at(TokenKind::Greater)
            || p.at(TokenKind::GreaterEquals)
        {
            (7, 8)
        } else if p.at(TokenKind::DoublePipe) {
            (9, 10)
        } else if p.at(TokenKind::DoubleAnd) {
            (11, 12)
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

    let cm = if p.at(TokenKind::Int) {
        parse_int_literal(p)
    } else if p.at(TokenKind::Bool) {
        parse_bool_literal(p)
    } else if p.at(TokenKind::Quote) {
        parse_string_literal(p)
    } else if p.at(TokenKind::Ident) {
        parse_ref_or_call(p)
    } else if p.at(TokenKind::Hyphen) || p.at(TokenKind::Plus) || p.at(TokenKind::Bang) {
        return Some(parse_prefix_expr(p, recovery_set));
    } else if p.at(TokenKind::If) {
        parse_if(
            p,
            recovery_set.union(TokenSet::new([TokenKind::If, TokenKind::Else])),
        )
    } else if p.at(TokenKind::While) || p.at(TokenKind::Loop) {
        return Some(parse_loop(p, recovery_set));
    } else if p.at(TokenKind::LParen) {
        return Some(parse_lambda(p, recovery_set));
    } else if p.at(TokenKind::LBrack) {
        return Some(parse_array(p, recovery_set));
    } else if p.at(TokenKind::LBrace) {
        parse_block(p, recovery_set)
    } else {
        return p.error_with_recovery_set(recovery_set);
    };

    // todo: this should go into the binary expr fn, but that would require a slight refactor of the type system
    if p.at(TokenKind::As) {
        let new_cm = cm.precede(p);
        p.bump();

        let _guard = p.expected_syntax_name("cast type");
        ty::parse_ty(p, recovery_set);

        Some(new_cm.complete(p, NodeKind::CastExpr))
    } else {
        Some(cm)
    }
}

fn parse_int_literal(p: &mut Parser) -> CompletedMarker {
    assert!(p.at(TokenKind::Int));
    let m = p.start();
    p.bump();
    m.complete(p, NodeKind::IntLiteral)
}

fn parse_bool_literal(p: &mut Parser) -> CompletedMarker {
    assert!(p.at(TokenKind::Bool));
    let m = p.start();
    p.bump();
    m.complete(p, NodeKind::BoolLiteral)
}

fn parse_string_literal(p: &mut Parser) -> CompletedMarker {
    assert!(p.at(TokenKind::Quote));
    let m = p.start();
    p.bump();

    while p.at(TokenKind::StringContents) || p.at(TokenKind::Escape) {
        p.bump();
    }

    p.expect(TokenKind::Quote);
    m.complete(p, NodeKind::StringLiteral)
}

fn parse_ref_or_call(p: &mut Parser) -> CompletedMarker {
    assert!(p.at(TokenKind::Ident));
    let m = p.start();
    parse_path(p, TokenSet::NONE);

    if p.at(TokenKind::LParen) {
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

            if p.at_eof() {
                break;
            }

            if !p.at(TokenKind::RParen) {
                p.expect_with_no_skip(TokenKind::Comma);
            }
        }

        p.expect(TokenKind::RParen);

        arg_list_m.complete(p, NodeKind::ArgList);
        m.complete(p, NodeKind::Call)
    } else {
        m.complete(p, NodeKind::Ref)
    }
}

fn parse_prefix_expr(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    let minus = p.at(TokenKind::Hyphen);
    let plus = p.at(TokenKind::Plus);
    let bang = p.at(TokenKind::Bang);
    assert!(minus || plus || bang);

    let m = p.start();

    let right_bp = if plus || minus || bang {
        13
    } else {
        unreachable!()
    };

    // Eat the operator’s token.
    p.bump();
    parse_expr_bp(p, right_bp, recovery_set, "operand");
    m.complete(p, NodeKind::UnaryExpr)
}

// const LAMBDA_EXPECTED: TokenSet = TokenSet::new([
//     TokenKind::Ident,
//     TokenKind::Dot,
//     TokenKind::Colon,
//     TokenKind::Whitespace,
// ]);

fn parse_lambda(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    assert!(p.at(TokenKind::LParen));

    let m = p.start();

    let param_list_m = p.start();

    p.bump();

    loop {
        if p.at(TokenKind::RParen) {
            break;
        }

        let param_m = p.start();
        let _guard = p.expected_syntax_name("parameter name");
        p.expect_with_no_skip(TokenKind::Ident);

        p.expect_with_no_skip(TokenKind::Colon);

        let _guard = p.expected_syntax_name("parameter type");
        parse_ty(p, TokenSet::new([TokenKind::Comma, TokenKind::RParen]));

        param_m.complete(p, NodeKind::Param);

        if p.at_eof() {
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

    p.expect_with_no_skip(TokenKind::Arrow);

    if p.at(TokenKind::Ident) {
        let _guard = p.expected_syntax_name("return type");
        parse_ty(p, recovery_set.union(TokenSet::new([TokenKind::LBrace])));
    }

    if p.at(TokenKind::LBrace) {
        parse_block(p, recovery_set);
    } else {
        let _guard = p.expected_syntax_name("lambda body");
        p.error();
    }

    m.complete(p, NodeKind::Lambda)
}

fn parse_if(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    assert!(p.at(TokenKind::If));

    let m = p.start();
    p.bump();

    parse_expr(p, "condition");

    if p.at(TokenKind::LBrace) {
        parse_block(p, recovery_set);
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
            parse_block(p, recovery_set);
        } else {
            let _guard = p.expected_syntax_name("else body");
            p.error_with_recovery_set(recovery_set);
        }

        else_m.complete(p, NodeKind::ElseBranch);
    }

    m.complete(p, NodeKind::IfExpr)
}

fn parse_loop(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    let at_while = p.at(TokenKind::While);
    let at_loop = p.at(TokenKind::Loop);
    assert!(at_while || at_loop);

    let m = p.start();
    p.bump();

    if at_while {
        parse_expr(p, "condition");
    }

    if p.at(TokenKind::LBrace) {
        parse_block(p, recovery_set);
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

fn parse_block(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    assert!(p.at(TokenKind::LBrace));

    let m = p.start();
    p.bump();

    while !p.at(TokenKind::RBrace) && !p.at_eof() {
        stmt::parse_stmt(p);
    }

    p.expect_with_recovery_set(TokenKind::RBrace, recovery_set);

    m.complete(p, NodeKind::Block)
}

fn parse_array(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    assert!(p.at(TokenKind::LBrack));

    let m = p.start();
    p.bump();

    // todo: better errors in the situation `arr := [3]i32{ 1, 2, 3 };`

    p.expect_with_recovery_set(
        TokenKind::RBrack,
        recovery_set.union(TokenSet::new([TokenKind::LBrace])),
    );

    let _guard = p.expected_syntax_name("array type");
    ty::parse_ty(p, recovery_set);

    if p.at(TokenKind::LBrace) {
        p.bump();

        loop {
            let item_m = p.start();
            parse_expr(p, "item");
            item_m.complete(p, NodeKind::ArrayItem);

            if p.at(TokenKind::RBrace) || p.at_eof() {
                break;
            } else {
                p.expect_with_no_skip(TokenKind::Comma);
            }
        }

        p.expect_with_recovery_set(TokenKind::RBrace, recovery_set);
    } else {
        let _guard = p.expected_syntax_name("array body");
        p.error_with_recovery_set(recovery_set);
    }

    m.complete(p, NodeKind::Array)
}

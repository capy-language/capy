use syntax::TokenKind;

use crate::token_set::TokenSet;

use super::*;

pub(super) fn parse_expr(
    p: &mut Parser,
    expected_syntax_name: &'static str,
) -> Option<CompletedMarker> {
    // let bt = backtrace::Backtrace::force_capture();
    // println!("parse_expr {}", bt);
    // println!("parse_expr {:?} {:?}", p.peek(), p.peek_range());
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
    parse_lhs(p, recovery_set, expected_syntax_name).map(|expr| {
        let m = expr.precede(p);
        m.complete(p, NodeKind::Ty)
    })
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
        let (left_bp, right_bp) = if p.at(TokenKind::DoublePipe) {
            (1, 2)
        } else if p.at(TokenKind::DoubleAnd) {
            (3, 4)
        } else if p.at_set(TokenSet::new([
            TokenKind::Less,
            TokenKind::LessEquals,
            TokenKind::Greater,
            TokenKind::GreaterEquals,
            TokenKind::DoubleEquals,
            TokenKind::BangEquals,
        ])) {
            (5, 6)
        } else if p.at(TokenKind::Plus) || p.at(TokenKind::Hyphen) {
            (7, 8)
        } else if p.at(TokenKind::Asterisk) || p.at(TokenKind::Slash) || p.at(TokenKind::Percent) {
            (9, 10)
        } else {
            break; // make sure parse_prefix_expr has a higher binding power than 10
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

    let mut cm = if p.at(TokenKind::Int) {
        parse_int_literal(p)
    } else if p.at(TokenKind::Float) {
        parse_float_literal(p)
    } else if p.at(TokenKind::Bool) {
        parse_bool_literal(p)
    } else if p.at(TokenKind::Quote) {
        parse_string_literal(p)
    } else if p.at(TokenKind::Ident) {
        parse_var_ref(p)
    } else if p.at(TokenKind::Caret) {
        parse_ref(p, recovery_set)
    } else if p.at(TokenKind::Distinct) {
        parse_distinct(p, recovery_set)
    } else if p.at(TokenKind::Import) {
        parse_import(p)
    } else if p.at(TokenKind::Comptime) {
        parse_comptime(p, recovery_set)
    } else if p.at(TokenKind::Struct) {
        parse_struct_def(p, recovery_set)
    } else if p.at(TokenKind::Hyphen) || p.at(TokenKind::Plus) || p.at(TokenKind::Bang) {
        parse_prefix_expr(p, recovery_set)
    } else if p.at(TokenKind::If) {
        parse_if(
            p,
            recovery_set.union(TokenSet::new([TokenKind::If, TokenKind::Else])),
        )
    } else if p.at(TokenKind::While) || p.at(TokenKind::Loop) {
        parse_loop(p, recovery_set)
    } else if p.at(TokenKind::LParen) {
        parse_lambda(p, recovery_set)
    } else if p.at(TokenKind::LBrack) {
        parse_array(p, recovery_set)
    } else if p.at(TokenKind::LBrace) {
        parse_block(p, recovery_set)
    } else {
        // println!("error {:?} {} {:?}", p.peek(), p.at_eof(), p.peek_range());
        return p.error_with_recovery_set(recovery_set);
    };

    loop {
        match p.kind() {
            Some(TokenKind::LBrack) => {
                let indexing_expr = cm.precede(p).complete(p, NodeKind::Source).precede(p);
                p.bump();

                let real_index = p.start();
                parse_expr(p, "array index");
                real_index.complete(p, NodeKind::Index);

                p.expect_with_no_skip(TokenKind::RBrack);

                cm = indexing_expr.complete(p, NodeKind::IndexExpr);
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

                    // todo: this might just be replaceable with at_default_recovery_set
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
            Some(TokenKind::Caret) => {
                let deref = cm.precede(p);
                p.bump();
                cm = deref.complete(p, NodeKind::DerefExpr);
            }
            Some(TokenKind::As) => {
                let cast = cm.precede(p);
                p.bump();

                parse_ty(p, "cast type", recovery_set);

                cm = cast.complete(p, NodeKind::CastExpr);
            }
            Some(TokenKind::Dot) => {
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
            _ => break,
        }
    }

    if matches!(cm.kind(), NodeKind::Path | NodeKind::VarRef)
        && !recovery_set.contains(TokenKind::LBrace)
        && p.at(TokenKind::LBrace)
    {
        let ty_cm = cm.precede(p).complete(p, NodeKind::Ty);
        cm = parse_struct_literal(p, ty_cm, recovery_set);
    }

    Some(cm)
}

fn parse_int_literal(p: &mut Parser) -> CompletedMarker {
    assert!(p.at(TokenKind::Int));
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
    assert!(p.at(TokenKind::Quote));
    let m = p.start();
    p.bump();

    while p.at(TokenKind::StringContents) || p.at(TokenKind::Escape) {
        p.bump();
    }

    p.expect(TokenKind::Quote);
    m.complete(p, NodeKind::StringLiteral)
}

fn parse_ref(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    assert!(p.at(TokenKind::Caret));
    let m = p.start();
    p.bump();

    if p.at(TokenKind::Mut) {
        p.bump();
    }

    parse_expr_bp(p, 14, recovery_set, "operand");

    m.complete(p, NodeKind::RefExpr)
}

fn parse_distinct(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    assert!(p.at(TokenKind::Distinct));
    let m = p.start();
    p.bump();

    parse_ty(p, "type", recovery_set);

    m.complete(p, NodeKind::Distinct)
}

fn parse_import(p: &mut Parser) -> CompletedMarker {
    assert!(p.at(TokenKind::Import));
    let m = p.start();
    p.bump();

    if p.at(TokenKind::Quote) {
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
    let minus = p.at(TokenKind::Hyphen);
    let plus = p.at(TokenKind::Plus);
    let bang = p.at(TokenKind::Bang);
    assert!(minus || plus || bang);

    let m = p.start();

    let right_bp = if plus || minus || bang {
        11
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
        p.expect(TokenKind::Ident);

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

    const BEGINNING_OF_BLOCK: TokenSet = TokenSet::new([TokenKind::LBrace, TokenKind::Extern]);

    if !p.at_set(BEGINNING_OF_BLOCK) {
        p.expect_with_no_skip(TokenKind::Arrow);

        if !p.at_set(BEGINNING_OF_BLOCK) {
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
        parse_block(p, recovery_set);
    } else if p.at(TokenKind::Extern) {
        p.bump();
    }

    m.complete(p, NodeKind::Lambda)
}

fn parse_struct_def(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    assert!(p.at(TokenKind::Struct));

    let m = p.start();

    p.bump();

    if p.at(TokenKind::LBrace) {
        p.bump();
    } else {
        let _guard = p.expected_syntax_name("struct body");
        p.error_with_recovery_set(recovery_set);

        return m.complete(p, NodeKind::StructDeclaration);
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

        field_m.complete(p, NodeKind::FieldDeclaration);

        if p.at_eof() || p.at_default_recovery_set() {
            break;
        }

        if !p.at(TokenKind::RBrace) {
            p.expect_with_no_skip(TokenKind::Comma);
        }
    }
    p.expect(TokenKind::RBrace);

    m.complete(p, NodeKind::StructDeclaration)
}

fn parse_struct_literal(
    p: &mut Parser,
    previous: CompletedMarker,
    recovery_set: TokenSet,
) -> CompletedMarker {
    assert!(p.at(TokenKind::LBrace));
    assert_eq!(previous.kind(), NodeKind::Ty);

    let m = previous.precede(p);

    if p.at(TokenKind::LBrace) {
        p.bump();
    } else {
        let _guard = p.expected_syntax_name("struct instance body");
        p.error_with_recovery_set(recovery_set);

        return m.complete(p, NodeKind::StructDeclaration);
    }

    loop {
        if p.at(TokenKind::RBrace) {
            break;
        }

        let field_m = p.start();
        let _guard = p.expected_syntax_name("field name");
        p.expect(TokenKind::Ident);

        p.expect_with_no_skip(TokenKind::Colon);

        parse_expr_with_recovery_set(
            p,
            "field value",
            recovery_set.union(TokenSet::new([TokenKind::Comma, TokenKind::RBrace])),
        );

        field_m.complete(p, NodeKind::FieldLiteral);

        if p.at_eof() || p.at_default_recovery_set() {
            break;
        }

        if !p.at(TokenKind::RBrace) {
            p.expect_with_no_skip(TokenKind::Comma);
        }
    }
    p.expect(TokenKind::RBrace);

    m.complete(p, NodeKind::StructLiteral)
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
        let m = p.start();
        parse_expr_with_recovery_set(
            p,
            "condition",
            recovery_set.union(TokenSet::new([TokenKind::LBrace])),
        );
        m.complete(p, NodeKind::Condition);
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

fn parse_comptime(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    assert!(p.at(TokenKind::Comptime));

    let m = p.start();
    p.bump();

    if !p.at(TokenKind::LBrace) {
        let _guard = p.expected_syntax_name("comptime block");
        p.error_with_no_skip();
    } else {
        parse_block(p, recovery_set);
    }

    m.complete(p, NodeKind::ComptimeExpr)
}

fn parse_block(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    assert!(p.at(TokenKind::LBrace));

    let m = p.start();
    p.bump();

    while !p.at(TokenKind::RBrace) && !p.at_eof() {
        stmt::parse_stmt(p, false);
    }

    p.expect_with_recovery_set(TokenKind::RBrace, recovery_set);

    m.complete(p, NodeKind::Block)
}

fn parse_array(p: &mut Parser, recovery_set: TokenSet) -> CompletedMarker {
    assert!(p.at(TokenKind::LBrack));

    let array = p.start();

    let size = p.start();
    p.bump();

    if !p.at(TokenKind::RBrack) {
        parse_expr(p, "array size");
    }

    p.expect_with_recovery_set(
        TokenKind::RBrack,
        recovery_set.union(TokenSet::new([TokenKind::LBrace])),
    );

    size.complete(p, NodeKind::ArraySize);

    parse_ty(
        p,
        "array type",
        recovery_set.union(TokenSet::new([TokenKind::LBrace])),
    );

    if !recovery_set.contains(TokenKind::LBrace) && p.at(TokenKind::LBrace) {
        let body = p.start();

        p.bump();

        if p.at(TokenKind::RBrace) {
            let _guard = p.expected_syntax_name("item");
            p.error_with_no_skip();
        }

        loop {
            if p.at(TokenKind::RBrace) || p.at_eof() {
                break;
            }

            if let Some(item) = parse_expr(p, "item") {
                item.precede(p).complete(p, NodeKind::ArrayItem);
            }

            if p.at(TokenKind::Comma) {
                p.expect_with_no_skip(TokenKind::Comma);
            } else {
                break;
            }
        }

        p.expect_with_recovery_set(TokenKind::RBrace, recovery_set);

        body.complete(p, NodeKind::ArrayBody);
    }

    // println!("done {:?} {:?}", p.peek(), p.peek_range());

    array.complete(p, NodeKind::Array)
}

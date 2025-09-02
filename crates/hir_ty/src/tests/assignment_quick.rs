use super::*;

use expect_test::expect;

#[test]
fn quick_assign() {
    check(
        r#"
            main :: () {
                foo := 5;

                foo += 1;
                foo -= 2;
                foo *= 3;
                foo /= 4;
            }
        "#,
        expect![[r#"
            main::main : () -> void
            0 : {uint}
            1 : {uint}
            2 : {uint}
            3 : {uint}
            4 : {uint}
            5 : {uint}
            6 : {uint}
            7 : {uint}
            8 : {uint}
            9 : void
            10 : () -> void
            l0 : {uint}
        "#]],
        |_| [],
    )
}

#[test]
fn quick_assign_reinfer() {
    check(
        r#"
            main :: () {
                foo := 5;

                foo += 1 + 2;
                foo -= 2 + 3;
                foo *= u64.(3);
                foo /= 4;
            }
        "#,
        // todo: there shouldn't be a uint
        expect![[r#"
            main::main : () -> void
            0 : u64
            1 : u64
            2 : u64
            3 : u64
            4 : u64
            5 : u64
            6 : u64
            7 : u64
            8 : u64
            9 : u64
            10 : u64
            12 : u64
            13 : u64
            14 : u64
            15 : void
            16 : () -> void
            l0 : u64
        "#]],
        |_| [],
    )
}

#[test]
fn quick_assign_cannot_perform() {
    check(
        r#"
            main :: () {
                foo := 5;

                foo += 1;
                foo -= 2;
                foo *= false;
                foo /= 4;
            }
        "#,
        expect![[r#"
            main::main : () -> void
            0 : {uint}
            1 : {uint}
            2 : {uint}
            3 : {uint}
            4 : {uint}
            5 : {uint}
            6 : bool
            7 : {uint}
            8 : {uint}
            9 : void
            10 : () -> void
            l0 : {uint}
        "#]],
        |_| {
            [(
                TyDiagnosticKind::BinaryOpMismatch {
                    op: hir::BinaryOp::Mul,
                    first: Ty::UInt(0).into(),
                    second: Ty::Bool.into(),
                },
                121..134,
                None,
            )]
        },
    )
}

#[test]
fn quick_assign_mismatch() {
    check(
        r#"
            main :: () {
                foo : u64 = 5;

                foo += 1;
                foo -= 2;
                foo *= i64.(3);
                foo /= 4;
            }
        "#,
        expect![[r#"
            main::main : () -> void
            1 : u64
            2 : u64
            3 : u64
            4 : u64
            5 : u64
            6 : u64
            7 : i64
            9 : i64
            10 : u64
            11 : u64
            12 : void
            13 : () -> void
            l0 : u64
        "#]],
        |_| {
            [(
                TyDiagnosticKind::BinaryOpMismatch {
                    op: hir::BinaryOp::Mul,
                    first: Ty::UInt(64).into(),
                    second: Ty::IInt(64).into(),
                },
                126..141,
                None,
            )]
        },
    )
}

#[test]
fn quick_assign_struct_field() {
    check(
        r#"
            main :: () {
                foo := .{ a = 5 };

                foo.a += 1;
                foo.a -= 2;
                foo.a *= 3;
                foo.a /= 4;

                bar : struct { a: i64 } = foo;
            }
        "#,
        expect![[r#"
            main::main : () -> void
            0 : i64
            1 : struct'0 {a: i64}
            2 : struct'0 {a: i64}
            3 : i64
            4 : i64
            5 : struct'0 {a: i64}
            6 : i64
            7 : i64
            8 : struct'0 {a: i64}
            9 : i64
            10 : i64
            11 : struct'0 {a: i64}
            12 : i64
            13 : i64
            16 : struct'0 {a: i64}
            17 : void
            18 : () -> void
            l0 : struct'0 {a: i64}
            l1 : struct'0 {a: i64}
        "#]],
        |_| [],
    )
}

#[test]
fn quick_assign_array() {
    check(
        r#"
            main :: () {
                foo := .[ 5, 4, 3, 2, 1];

                foo[0] += 1;
                foo[0] -= 2;
                foo[0] *= 3;
                foo[0] /= 4;

                // for type inference
                bar : [5]i64 = foo;
            }
        "#,
        expect![[r#"
            main::main : () -> void
            0 : i64
            1 : i64
            2 : i64
            3 : i64
            4 : i64
            5 : [5]i64
            6 : [5]i64
            7 : usize
            8 : i64
            9 : i64
            10 : [5]i64
            11 : usize
            12 : i64
            13 : i64
            14 : [5]i64
            15 : usize
            16 : i64
            17 : i64
            18 : [5]i64
            19 : usize
            20 : i64
            21 : i64
            22 : usize
            25 : [5]i64
            26 : void
            27 : () -> void
            l0 : [5]i64
            l1 : [5]i64
        "#]],
        |_| [],
    )
}

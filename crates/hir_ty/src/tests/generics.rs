use super::*;

use expect_test::expect;

#[test]
fn generic_changing_local_types() {
    check(
        r#"
            add_unknown_numbers :: (comptime Int_Type: type) {
                x : Int_Type = 10;
                y : Int_Type = 10;

                x + y;
            }

            main :: () {
                add_unknown_numbers(i32);
                add_unknown_numbers(i64);
                add_unknown_numbers(bool);
            }
        "#,
        expect![[r#"
            main::add_unknown_numbers<0> : main::add_unknown_numbers<0>(type) -> void
              9 : main::add_unknown_numbers<0>(type) -> void
            main::add_unknown_numbers<1> : main::add_unknown_numbers<1>(type) -> void
              9 : main::add_unknown_numbers<1>(type) -> void
            main::add_unknown_numbers<2> : main::add_unknown_numbers<2>(type) -> void
              9 : main::add_unknown_numbers<2>(type) -> void
            main::lambda#add_unknown_numbers<0> : main::add_unknown_numbers<0>(type) -> void
              1 : type
              2 : i32
              3 : type
              4 : i32
              5 : i32
              6 : i32
              7 : i32
              8 : void
              9 : main::add_unknown_numbers<0>(type) -> void
              l0 : i32
              l1 : i32
            main::lambda#add_unknown_numbers<1> : main::add_unknown_numbers<1>(type) -> void
              1 : type
              2 : i64
              3 : type
              4 : i64
              5 : i64
              6 : i64
              7 : i64
              8 : void
              9 : main::add_unknown_numbers<1>(type) -> void
              l0 : i64
              l1 : i64
            main::lambda#add_unknown_numbers<2> : main::add_unknown_numbers<2>(type) -> void
              1 : type
              2 : {uint}
              3 : type
              4 : {uint}
              5 : bool
              6 : bool
              7 : bool
              8 : void
              9 : main::add_unknown_numbers<2>(type) -> void
              l0 : bool
              l1 : bool
            main::main : main::main() -> void
              20 : main::main() -> void
            main::lambda#main : main::main() -> void
              10 : main::add_unknown_numbers<0>(type) -> void
              11 : type
              12 : void
              13 : main::add_unknown_numbers<1>(type) -> void
              14 : type
              15 : void
              16 : main::add_unknown_numbers<2>(type) -> void
              17 : type
              18 : void
              19 : void
              20 : main::main() -> void
        "#]],
        |_| {
            [
                (
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::Bool.into()),
                        found: Ty::UInt(0).into(),
                    },
                    95..97,
                    None,
                ),
                (
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::Bool.into()),
                        found: Ty::UInt(0).into(),
                    },
                    130..132,
                    None,
                ),
                (
                    TyDiagnosticKind::BinaryOpMismatch {
                        op: hir::BinaryOp::Add,
                        first: Ty::Bool.into(),
                        second: Ty::Bool.into(),
                    },
                    151..156,
                    None,
                ),
            ]
        },
    );
}

#[test]
fn generic_arg_not_const() {
    check(
        r#"
            add_unknown_numbers :: (comptime Int_Type: type) {
                x : Int_Type = 10;
                y : Int_Type = 10;

                x + y;
            }

            main :: () {
                Type := i32;

                add_unknown_numbers(Type);
            }
        "#,
        expect![[r#"
            main::main : main::main() -> void
              15 : main::main() -> void
            main::lambda#main : main::main() -> void
              10 : type
              11 : main::add_unknown_numbers<?>
              12 : type
              13 : <unknown>
              14 : void
              15 : main::main() -> void
              l2 : type
        "#]],
        |i| {
            [(
                TyDiagnosticKind::ComptimeArgNotConst {
                    param_name: i.intern("Int_Type"),
                    param_ty: Ty::Type.into(),
                },
                264..268,
                None,
            )]
        },
    );
}

#[test]
fn generic_type_generator() {
    check(
        r#"
            StackVec :: (comptime T: type, comptime len: usize) -> type {
                struct {
                    arr: [len] T,
                }
            }

            main :: () {
                IntVec :: comptime StackVec(i32, 5);
                foo : IntVec;
                foo : comptime StackVec(bool, 10);
                foo : comptime StackVec(struct { age: i64, cool: bool }, 100);
                foo : StackVec(str, 32);
            }
        "#,
        expect![[r#"
            main::StackVec<0> : main::StackVec<0>(type, usize) -> type
              8 : main::StackVec<0>(type, usize) -> type
            main::StackVec<2> : main::StackVec<2>(type, usize) -> type
              8 : main::StackVec<2>(type, usize) -> type
            main::StackVec<4> : main::StackVec<4>(type, usize) -> type
              8 : main::StackVec<4>(type, usize) -> type
            main::StackVec<6> : main::StackVec<6>(type, usize) -> type
              8 : main::StackVec<6>(type, usize) -> type
            main::lambda#StackVec<0> : main::StackVec<0>(type, usize) -> type
              3 : usize
              4 : type
              6 : type
              7 : type
              8 : main::StackVec<0>(type, usize) -> type
            main::lambda#StackVec<2> : main::StackVec<2>(type, usize) -> type
              3 : usize
              4 : type
              6 : type
              7 : type
              8 : main::StackVec<2>(type, usize) -> type
            main::lambda#StackVec<4> : main::StackVec<4>(type, usize) -> type
              3 : usize
              4 : type
              6 : type
              7 : type
              8 : main::StackVec<4>(type, usize) -> type
            main::lambda#StackVec<6> : main::StackVec<6>(type, usize) -> type
              3 : usize
              4 : type
              6 : type
              7 : type
              8 : main::StackVec<6>(type, usize) -> type
            main::main : main::main() -> void
              32 : main::main() -> void
            main::lambda#main : main::main() -> void
              9 : main::StackVec<0>(type, usize) -> type
              10 : type
              11 : usize
              12 : type
              13 : type
              15 : main::StackVec<2>(type, usize) -> type
              16 : type
              17 : usize
              18 : type
              19 : type
              20 : main::StackVec<4>(type, usize) -> type
              23 : type
              24 : usize
              25 : type
              26 : type
              27 : main::StackVec<6>(type, usize) -> type
              28 : type
              29 : usize
              30 : type
              31 : void
              32 : main::main() -> void
              l0 : type
              l1 : struct'0 {arr: [5]i32}
              l2 : struct'0 {arr: [10]bool}
              l3 : struct'0 {arr: [100]struct'1 {age: i64, cool: bool}}
              l4 : <unknown>
        "#]],
        |_| [(TyDiagnosticKind::CantUseAsTy, 427..444, None)],
    );
}

#[test]
fn generic_changing_parameter_types() {
    check(
        r#"
            add :: (comptime T: type, left: T, right: T) -> T {
                left + right
            }

            main :: () {
                add(i32, 2, 4);
            }
        "#,
        expect![[r#"
            main::add<0> : main::add<0>(type, i32, i32) -> i32
              1 : type
              2 : type
              3 : type
              8 : main::add<0>(type, i32, i32) -> i32
            main::lambda#add<0> : main::add<0>(type, i32, i32) -> i32
              1 : type
              2 : type
              3 : type
              4 : i32
              5 : i32
              6 : i32
              7 : i32
              8 : main::add<0>(type, i32, i32) -> i32
            main::main : main::main() -> void
              15 : main::main() -> void
            main::lambda#main : main::main() -> void
              9 : main::add<0>(type, i32, i32) -> i32
              10 : type
              11 : i32
              12 : i32
              13 : i32
              14 : void
              15 : main::main() -> void
        "#]],
        |_| [],
    );
}

#[test]
fn generic_type_generator_in_other_file() {
    check(
        r#"
            #- vec.capy
            StackVec :: (comptime T: type, comptime len: usize) -> type {
                struct {
                    arr: [len] T,
                }
            }

            #- main.capy
            vec :: #import("vec.capy");

            main :: () {
                IntVec :: comptime vec.StackVec(i32, 5);
                foo : IntVec;
                foo : comptime vec.StackVec(bool, 10);
                foo : comptime vec.StackVec(struct { age: i64, cool: bool }, 100);
                foo : vec.StackVec(str, 32);
            }
        "#,
        expect![[r#"
            vec::StackVec<0> : vec::StackVec<0>(type, usize) -> type
              8 : vec::StackVec<0>(type, usize) -> type
            vec::StackVec<2> : vec::StackVec<2>(type, usize) -> type
              8 : vec::StackVec<2>(type, usize) -> type
            vec::StackVec<4> : vec::StackVec<4>(type, usize) -> type
              8 : vec::StackVec<4>(type, usize) -> type
            vec::StackVec<6> : vec::StackVec<6>(type, usize) -> type
              8 : vec::StackVec<6>(type, usize) -> type
            vec::lambda#StackVec<0> : vec::StackVec<0>(type, usize) -> type
              3 : usize
              4 : type
              6 : type
              7 : type
              8 : vec::StackVec<0>(type, usize) -> type
            vec::lambda#StackVec<2> : vec::StackVec<2>(type, usize) -> type
              3 : usize
              4 : type
              6 : type
              7 : type
              8 : vec::StackVec<2>(type, usize) -> type
            vec::lambda#StackVec<4> : vec::StackVec<4>(type, usize) -> type
              3 : usize
              4 : type
              6 : type
              7 : type
              8 : vec::StackVec<4>(type, usize) -> type
            vec::lambda#StackVec<6> : vec::StackVec<6>(type, usize) -> type
              3 : usize
              4 : type
              6 : type
              7 : type
              8 : vec::StackVec<6>(type, usize) -> type
            main::vec : file vec
              0 : file vec
            main::main : main::main() -> void
              28 : main::main() -> void
            main::lambda#main : main::main() -> void
              1 : file vec
              2 : vec::StackVec<0>(type, usize) -> type
              3 : type
              4 : usize
              5 : type
              6 : type
              8 : file vec
              9 : vec::StackVec<2>(type, usize) -> type
              10 : type
              11 : usize
              12 : type
              13 : type
              14 : file vec
              15 : vec::StackVec<4>(type, usize) -> type
              18 : type
              19 : usize
              20 : type
              21 : type
              22 : file vec
              23 : vec::StackVec<6>(type, usize) -> type
              24 : type
              25 : usize
              26 : type
              27 : void
              28 : main::main() -> void
              l0 : type
              l1 : struct'0 {arr: [5]i32}
              l2 : struct'0 {arr: [10]bool}
              l3 : struct'0 {arr: [100]struct'1 {age: i64, cool: bool}}
              l4 : <unknown>
        "#]],
        |_| [(TyDiagnosticKind::CantUseAsTy, 313..334, None)],
    );
}

#[test]
fn generic_changing_parameter_types_in_other_file() {
    check(
        r#"
            #- math.capy
            add :: (comptime T: type, left: T, right: T) -> T {
                left + right
            }

            #- main.capy
            math :: #import("math.capy");

            main :: () {
                math.add(i32, 2, 4);
            }
        "#,
        expect![[r#"
            math::add<0> : math::add<0>(type, i32, i32) -> i32
              1 : type
              2 : type
              3 : type
              8 : math::add<0>(type, i32, i32) -> i32
            math::lambda#add<0> : math::add<0>(type, i32, i32) -> i32
              1 : type
              2 : type
              3 : type
              4 : i32
              5 : i32
              6 : i32
              7 : i32
              8 : math::add<0>(type, i32, i32) -> i32
            main::math : file math
              0 : file math
            main::main : main::main() -> void
              8 : main::main() -> void
            main::lambda#main : main::main() -> void
              1 : file math
              2 : math::add<0>(type, i32, i32) -> i32
              3 : type
              4 : i32
              5 : i32
              6 : i32
              7 : void
              8 : main::main() -> void
        "#]],
        |_| [],
    );
}

use super::*;

use expect_test::expect;

#[test]
fn lambda_ret_expected_error_union() {
    check(
        r#"
            do_work :: (task_number: u64) -> str!u64 {
                if task_number == 3 {
                    return "task 3 is not supported!";
                }

                return task_number * 2;
            }
        "#,
        expect![[r#"
            main::do_work : main::do_work(u64) -> str!u64
              14 : main::do_work(u64) -> str!u64
            main::lambda#do_work : main::do_work(u64) -> str!u64
              4 : u64
              5 : u64
              6 : bool
              7 : str
              8 : noeval
              9 : void
              10 : u64
              11 : u64
              12 : u64
              13 : str!u64
              14 : main::do_work(u64) -> str!u64
        "#]],
        |_| [],
    )
}

#[test]
fn block_ret_expected_error_union() {
    check(
        r#"
            do_work :: (task_number: u64) {
                result : str!u64 = `blk: {
                    if task_number == 3 {
                        break "task 3 is not supported!";
                    }

                    break task_number * 2;
                };
            }
        "#,
        expect![[r#"
            main::do_work : main::do_work(u64) -> void
              15 : main::do_work(u64) -> void
            main::lambda#do_work : main::do_work(u64) -> void
              4 : u64
              5 : u64
              6 : bool
              7 : str
              8 : noeval
              9 : void
              10 : u64
              11 : u64
              12 : u64
              13 : str!u64
              14 : void
              15 : main::do_work(u64) -> void
              l0 : str!u64
        "#]],
        |_| [],
    )
}

#[test]
fn block_ret_unexpected_error_union() {
    check(
        r#"
            do_work :: (task_number: u64) {
                result := `blk: {
                    if task_number == 3 {
                        break "task 3 is not supported!";
                    }

                    break task_number * 2;
                };
            }
        "#,
        expect![[r#"
            main::do_work : main::do_work(u64) -> void
              12 : main::do_work(u64) -> void
            main::lambda#do_work : main::do_work(u64) -> void
              1 : u64
              2 : u64
              3 : bool
              4 : str
              5 : noeval
              6 : void
              7 : u64
              8 : u64
              9 : u64
              10 : <unknown>
              11 : void
              12 : main::do_work(u64) -> void
              l0 : <unknown>
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::String.into()),
                    found: Ty::UInt(64).into(),
                },
                228..243,
                Some((
                    TyDiagnosticHelpKind::BreakHere {
                        ty: Ty::String.into(),
                        is_default: false,
                    },
                    145..178,
                )),
            )]
        },
    )
}

#[test]
fn simple_val_expected_error_union() {
    check(
        r#"
            do_work :: (task_number: u64) {
                result : str!u64 = "this is an error!";
            }
        "#,
        expect![[r#"
            main::do_work : main::do_work(u64) -> void
              6 : main::do_work(u64) -> void
            main::lambda#do_work : main::do_work(u64) -> void
              4 : str
              5 : void
              6 : main::do_work(u64) -> void
              l0 : str!u64
        "#]],
        |_| [],
    )
}

#[test]
fn error_union_try() {
    check(
        r#"
            Error_Kind :: enum {
                Not_Supported,
                Foo_Failed,
            };

            Error :: struct {
                why: Error_Kind,
                timestamp: str,
            };

            do_lots_of_work :: (task_num: u64) -> Error!u64 {
                work := do_work(task_num).try;

                work * 2
            }

            do_work :: (task_number: u64) -> Error!u64 {
                if task_number == 3 {
                    return .{
                        why = Error_Kind.Not_Supported,
                        timestamp = "1955-11-05 6:15am"
                    };
                }

                foo(task_number == 0 || task_number % 8 != 0).try;

                return task_number * 2;
            }

            foo :: (cond: bool) -> Error!void {
                if !cond {
                    return .{
                        why = Error_Kind.Foo_Failed,
                        timestamp = "1955-11-12 10:04pm",
                    };
                }
            }
        "#,
        expect![[r#"
            main::Error_Kind : type
              0 : type
            main::Error : type
              3 : type
            main::do_lots_of_work : main::do_lots_of_work(u64) -> main::Error!u64
              16 : main::do_lots_of_work(u64) -> main::Error!u64
            main::lambda#do_lots_of_work : main::do_lots_of_work(u64) -> main::Error!u64
              8 : main::do_work(u64) -> main::Error!u64
              9 : u64
              10 : main::Error!u64
              11 : u64
              12 : u64
              13 : u64
              14 : u64
              15 : main::Error!u64
              16 : main::do_lots_of_work(u64) -> main::Error!u64
              l0 : u64
            main::do_work : main::do_work(u64) -> main::Error!u64
              46 : main::do_work(u64) -> main::Error!u64
            main::lambda#do_work : main::do_work(u64) -> main::Error!u64
              21 : u64
              22 : u64
              23 : bool
              24 : type
              25 : main::Error_Kind.Not_Supported
              26 : str
              27 : ~struct {why: main::Error_Kind.Not_Supported, timestamp: str}
              28 : noeval
              29 : void
              30 : main::foo(bool) -> main::Error!void
              31 : u64
              32 : u64
              33 : bool
              34 : u64
              35 : u64
              36 : u64
              37 : u64
              38 : bool
              39 : bool
              40 : main::Error!void
              41 : void
              42 : u64
              43 : u64
              44 : u64
              45 : main::Error!u64
              46 : main::do_work(u64) -> main::Error!u64
            main::foo : main::foo(bool) -> main::Error!void
              60 : main::foo(bool) -> main::Error!void
            main::lambda#foo : main::foo(bool) -> main::Error!void
              51 : bool
              52 : bool
              53 : type
              54 : main::Error_Kind.Foo_Failed
              55 : str
              56 : ~struct {why: main::Error_Kind.Foo_Failed, timestamp: str}
              57 : noeval
              58 : void
              59 : main::Error!void
              60 : main::foo(bool) -> main::Error!void
        "#]],
        |_| [],
    )
}

#[test]
fn error_union_try_mismatch() {
    check(
        r#"
            Error_Kind :: enum {
                Not_Supported,
                Foo_Failed,
            };

            Error :: struct {
                why: Error_Kind,
                timestamp: str,
            };

            do_lots_of_work :: (task_num: u64) -> str!u64 {
                work := do_work(task_num).try;

                work * 2
            }

            do_work :: (task_number: u64) -> str!u64 {
                if task_number == 3 {
                    return .{
                        why = Error_Kind.Not_Supported,
                        timestamp = "1955-11-05 6:15am"
                    };
                }

                foo(task_number == 0 || task_number % 8 != 0).try;

                return task_number * 2;
            }

            foo :: (cond: bool) -> Error!void {
                if !cond {
                    return .{
                        why = Error_Kind.Foo_Failed,
                        timestamp = "1955-11-12 10:04pm",
                    };
                }
            }
        "#,
        expect![[r#"
            main::Error_Kind : type
              0 : type
            main::Error : type
              3 : type
            main::do_lots_of_work : main::do_lots_of_work(u64) -> str!u64
              16 : main::do_lots_of_work(u64) -> str!u64
            main::lambda#do_lots_of_work : main::do_lots_of_work(u64) -> str!u64
              8 : main::do_work(u64) -> str!u64
              9 : u64
              10 : str!u64
              11 : u64
              12 : u64
              13 : u64
              14 : u64
              15 : str!u64
              16 : main::do_lots_of_work(u64) -> str!u64
              l0 : u64
            main::do_work : main::do_work(u64) -> str!u64
              46 : main::do_work(u64) -> str!u64
            main::lambda#do_work : main::do_work(u64) -> str!u64
              21 : u64
              22 : u64
              23 : bool
              24 : type
              25 : main::Error_Kind.Not_Supported
              26 : str
              27 : ~struct {why: main::Error_Kind.Not_Supported, timestamp: str}
              28 : noeval
              29 : void
              30 : main::foo(bool) -> main::Error!void
              31 : u64
              32 : u64
              33 : bool
              34 : u64
              35 : u64
              36 : u64
              37 : u64
              38 : bool
              39 : bool
              40 : main::Error!void
              41 : void
              42 : u64
              43 : u64
              44 : u64
              45 : <unknown>
              46 : main::do_work(u64) -> str!u64
            main::foo : main::foo(bool) -> main::Error!void
              60 : main::foo(bool) -> main::Error!void
            main::lambda#foo : main::foo(bool) -> main::Error!void
              51 : bool
              52 : bool
              53 : type
              54 : main::Error_Kind.Foo_Failed
              55 : str
              56 : ~struct {why: main::Error_Kind.Foo_Failed, timestamp: str}
              57 : noeval
              58 : void
              59 : main::Error!void
              60 : main::foo(bool) -> main::Error!void
        "#]],
        |i| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(
                        Ty::ErrorUnion {
                            error_ty: Ty::String.into(),
                            payload_ty: Ty::UInt(64).into(),
                        }
                        .into(),
                    ),
                    found: Ty::AnonStruct {
                        members: vec![
                            MemberTy {
                                name: Name(i.intern("why")),
                                ty: Ty::EnumVariant {
                                    enum_uid: 2,
                                    variant_name: Name(i.intern("Not_Supported")),
                                    uid: 0,
                                    sub_ty: Ty::Void.into(),
                                    discriminant: 0,
                                }
                                .into(),
                            },
                            MemberTy {
                                name: Name(i.intern("timestamp")),
                                ty: Ty::String.into(),
                            },
                        ],
                    }
                    .into(),
                },
                488..624,
                Some((
                    TyDiagnosticHelpKind::ReturnTyHere {
                        ty: Ty::ErrorUnion {
                            error_ty: Ty::String.into(),
                            payload_ty: Ty::UInt(64).into(),
                        }
                        .into(),
                        is_default: false,
                    },
                    413..420,
                )),
            )]
        },
    )
}

#[test]
fn error_union_impossible_to_differentiate() {
    check(
        r#"
            foo :: () -> u8!i64 {
                42
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> <unknown>
              5 : main::foo() -> <unknown>
            main::lambda#foo : main::foo() -> <unknown>
              3 : {uint}
              4 : <unknown>
              5 : main::foo() -> <unknown>
        "#]],
        |_| {
            [(
                TyDiagnosticKind::ImpossibleToDifferentiateErrorUnion {
                    error_ty: Ty::UInt(8).into(),
                    payload_ty: Ty::IInt(64).into(),
                },
                26..32,
                None,
            )]
        },
    )
}

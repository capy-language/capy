use la_arena::Arena;

use crate::ResolvedTy;

/// automagically converts two types into the type that can represent both.
///
/// this function accepts unknown types.
///
/// ```text
///  {int} → i8 → i16 → i32 → i64 → isize
///                ↘     ↘
///    ↕             f32 → f64
///                ↗     ↗
/// {uint} → u8 → u16 → u32 → u64 → usize
///             ↘     ↘     ↘     ↘
///          i8 → i16 → i32 → i64 → isize
/// ```
///
/// diagram stolen from vlang docs bc i liked it
pub(crate) fn max_cast(
    resolved_arena: &Arena<ResolvedTy>,
    first: ResolvedTy,
    second: ResolvedTy,
) -> Option<ResolvedTy> {
    if first == second {
        return Some(first);
    }

    match (first, second) {
        (ResolvedTy::UInt(0), ResolvedTy::UInt(0)) => Some(ResolvedTy::UInt(0)),
        (ResolvedTy::IInt(0) | ResolvedTy::UInt(0), ResolvedTy::IInt(0) | ResolvedTy::UInt(0)) => {
            Some(ResolvedTy::IInt(0))
        }
        (ResolvedTy::IInt(first_bit_width), ResolvedTy::IInt(second_bit_width)) => {
            Some(ResolvedTy::IInt(first_bit_width.max(second_bit_width)))
        }
        (ResolvedTy::UInt(first_bit_width), ResolvedTy::UInt(second_bit_width)) => {
            Some(ResolvedTy::UInt(first_bit_width.max(second_bit_width)))
        }
        (ResolvedTy::IInt(signed_bit_width), ResolvedTy::UInt(unsigned_bit_width))
        | (ResolvedTy::UInt(unsigned_bit_width), ResolvedTy::IInt(signed_bit_width)) => {
            if signed_bit_width > unsigned_bit_width {
                Some(ResolvedTy::IInt(signed_bit_width))
            } else {
                println!(
                    "{:?} does not fit into {:?}",
                    unsigned_bit_width, signed_bit_width
                );
                None
            }
        }
        (
            ResolvedTy::Distinct {
                fqn,
                uid,
                ty: distinct_ty,
            },
            other,
        )
        | (
            other,
            ResolvedTy::Distinct {
                fqn,
                uid,
                ty: distinct_ty,
            },
        ) => {
            let distinct = ResolvedTy::Distinct {
                fqn,
                uid,
                ty: distinct_ty,
            };
            if has_semantics_of(resolved_arena, distinct, other) {
                Some(distinct)
            } else {
                None
            }
        }
        (ResolvedTy::Unknown, other) | (other, ResolvedTy::Unknown) => Some(other),
        _ => None,
    }
}

/// returns whether one type can "fit" into another type as shown in the below diagram.
///
/// ```text
///  {int} → i8 → i16 → i32 → i64
///                ↘     ↘
///                  f32 → f64
///                ↗     ↗
/// {uint} → u8 → u16 → u32 → u64 → usize
///        ↘    ↘     ↘     ↘     ↘
///          i8 → i16 → i32 → i64 → isize
///
///  {int} → distinct {int}
///        ↗
/// {uint} → distinct {uint}
/// ```
///
/// this function panics when given an unknown type
///
/// diagram stolen from vlang docs bc i liked it
pub(crate) fn can_fit(
    resolved_arena: &Arena<ResolvedTy>,
    found: ResolvedTy,
    expected: ResolvedTy,
) -> bool {
    assert_ne!(found, ResolvedTy::Unknown);
    assert_ne!(expected, ResolvedTy::Unknown);

    if found == expected {
        return true;
    }

    match (found, expected) {
        (ResolvedTy::IInt(found_bit_width), ResolvedTy::IInt(expected_bit_width))
        | (ResolvedTy::UInt(found_bit_width), ResolvedTy::UInt(expected_bit_width)) => {
            expected_bit_width == 0 || found_bit_width <= expected_bit_width
        }
        // we allow this because the uint is weak
        (ResolvedTy::IInt(_), ResolvedTy::UInt(0)) => true,
        // we don't allow this case because of the loss of the sign
        (ResolvedTy::IInt(_), ResolvedTy::UInt(_)) => false,
        (ResolvedTy::UInt(found_bit_width), ResolvedTy::IInt(expected_bit_width)) => {
            expected_bit_width == 0 || found_bit_width < expected_bit_width
        }
        (
            ResolvedTy::Pointer { sub_ty: found_ty },
            ResolvedTy::Pointer {
                sub_ty: expected_ty,
            },
        ) => can_fit(
            resolved_arena,
            resolved_arena[found_ty],
            resolved_arena[expected_ty],
        ),
        (
            ResolvedTy::Array {
                sub_ty: found_ty,
                size: found_size,
            },
            ResolvedTy::Array {
                sub_ty: expected_ty,
                size: expected_size,
            },
        ) => {
            found_size == expected_size
                && can_fit(
                    resolved_arena,
                    resolved_arena[found_ty],
                    resolved_arena[expected_ty],
                )
        }
        (
            ResolvedTy::Distinct { uid: found_uid, .. },
            ResolvedTy::Distinct {
                uid: expected_uid, ..
            },
        ) => found_uid == expected_uid,
        (found, ResolvedTy::Distinct { ty, .. }) => {
            can_fit(resolved_arena, found, resolved_arena[ty])
        }
        _ => false,
    }
}

pub(crate) fn primitive_castable(
    resolved_arena: &Arena<ResolvedTy>,
    from: ResolvedTy,
    to: ResolvedTy,
) -> bool {
    if can_fit(resolved_arena, from, to) {
        return true;
    }

    match (from, to) {
        (
            ResolvedTy::Bool | ResolvedTy::IInt(_) | ResolvedTy::UInt(_),
            ResolvedTy::Bool | ResolvedTy::IInt(_) | ResolvedTy::UInt(_),
        ) => true,
        (ResolvedTy::Distinct { ty: from, .. }, ResolvedTy::Distinct { ty: to, .. }) => {
            primitive_castable(resolved_arena, resolved_arena[from], resolved_arena[to])
        }
        (ResolvedTy::Distinct { ty: from, .. }, to) => {
            primitive_castable(resolved_arena, resolved_arena[from], to)
        }
        _ => false,
    }
}

/// allows `distinct` types to have the same semantics as other types as long as the inner type is correct
pub(crate) fn has_semantics_of(
    resolved_arena: &Arena<ResolvedTy>,
    found: ResolvedTy,
    expected: ResolvedTy,
) -> bool {
    match (found, expected) {
        (ResolvedTy::Distinct { ty, .. }, ResolvedTy::IInt(0) | ResolvedTy::UInt(0)) => {
            if has_semantics_of(resolved_arena, resolved_arena[ty], expected) {
                return true;
            }
        }
        (ResolvedTy::Distinct { .. }, ResolvedTy::IInt(_) | ResolvedTy::UInt(_)) => return false,
        (
            ResolvedTy::Distinct { uid: found_uid, .. },
            ResolvedTy::Distinct {
                uid: expected_uid, ..
            },
        ) => {
            if found_uid == expected_uid {
                return true;
            }
        }
        (ResolvedTy::Distinct { ty, .. }, expected) => {
            if has_semantics_of(resolved_arena, resolved_arena[ty], expected) {
                return true;
            }
        }
        _ => {}
    }

    if can_fit(resolved_arena, found, expected) {
        return true;
    }

    false
}

use la_arena::Arena;

use crate::ResolvedTy;

pub(crate) struct BinaryOutputTy {
    pub(crate) max_ty: ResolvedTy,
    pub(crate) final_output_ty: ResolvedTy,
}

pub(crate) trait TypedBinaryOp {
    fn can_perform(&self, resolved_arena: &Arena<ResolvedTy>, ty: ResolvedTy) -> bool;

    fn get_possible_output_ty(
        &self,
        resolved_arena: &Arena<ResolvedTy>,
        first: ResolvedTy,
        second: ResolvedTy,
    ) -> Option<BinaryOutputTy>;

    fn default_ty(&self) -> ResolvedTy;
}

impl TypedBinaryOp for hir::BinaryOp {
    /// should check with `can_perform` before actually using the type emitted from this function
    fn get_possible_output_ty(
        &self,
        resolved_arena: &Arena<ResolvedTy>,
        first: ResolvedTy,
        second: ResolvedTy,
    ) -> Option<BinaryOutputTy> {
        max_cast(resolved_arena, first, second).map(|max_ty| BinaryOutputTy {
            max_ty: max_ty.clone(),
            final_output_ty: match self {
                hir::BinaryOp::Add
                | hir::BinaryOp::Sub
                | hir::BinaryOp::Mul
                | hir::BinaryOp::Div
                | hir::BinaryOp::Mod => max_ty,
                hir::BinaryOp::Lt
                | hir::BinaryOp::Gt
                | hir::BinaryOp::Le
                | hir::BinaryOp::Ge
                | hir::BinaryOp::Eq
                | hir::BinaryOp::Ne
                | hir::BinaryOp::And
                | hir::BinaryOp::Or => ResolvedTy::Bool,
            },
        })
    }

    fn can_perform(&self, resolved_arena: &Arena<ResolvedTy>, found: ResolvedTy) -> bool {
        let expected: &[ResolvedTy] = match self {
            hir::BinaryOp::Add | hir::BinaryOp::Sub | hir::BinaryOp::Mul | hir::BinaryOp::Div => {
                &[ResolvedTy::IInt(0), ResolvedTy::Float(0)]
            }
            hir::BinaryOp::Mod => &[ResolvedTy::IInt(0)],
            hir::BinaryOp::Lt
            | hir::BinaryOp::Gt
            | hir::BinaryOp::Le
            | hir::BinaryOp::Ge
            | hir::BinaryOp::Eq
            | hir::BinaryOp::Ne => &[ResolvedTy::IInt(0)],
            hir::BinaryOp::And | hir::BinaryOp::Or => &[ResolvedTy::Bool],
        };

        expected
            .iter()
            .any(|expected| has_semantics_of(resolved_arena, found.clone(), expected.clone()))
    }

    fn default_ty(&self) -> ResolvedTy {
        match self {
            hir::BinaryOp::Add | hir::BinaryOp::Sub | hir::BinaryOp::Mul | hir::BinaryOp::Div => {
                ResolvedTy::IInt(0)
            }
            hir::BinaryOp::Mod => ResolvedTy::IInt(0),
            hir::BinaryOp::Lt
            | hir::BinaryOp::Gt
            | hir::BinaryOp::Le
            | hir::BinaryOp::Ge
            | hir::BinaryOp::Eq
            | hir::BinaryOp::Ne => ResolvedTy::Bool,
            hir::BinaryOp::And | hir::BinaryOp::Or => ResolvedTy::Bool,
        }
    }
}

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
                // println!(
                //     "{:?} does not fit into {:?}",
                //     unsigned_bit_width, signed_bit_width
                // );
                None
            }
        }
        (ResolvedTy::IInt(0) | ResolvedTy::UInt(0), ResolvedTy::Float(float_bit_width))
        | (ResolvedTy::Float(float_bit_width), ResolvedTy::IInt(0) | ResolvedTy::UInt(0)) => {
            Some(ResolvedTy::Float(float_bit_width))
        }
        (
            ResolvedTy::IInt(int_bit_width) | ResolvedTy::UInt(int_bit_width),
            ResolvedTy::Float(float_bit_width),
        )
        | (
            ResolvedTy::Float(float_bit_width),
            ResolvedTy::IInt(int_bit_width) | ResolvedTy::UInt(int_bit_width),
        ) => {
            if int_bit_width < 64 && float_bit_width == 0 {
                // the int bit width must be smaller than the final float which can only go up to 64 bits,
                // the int bit width is doubled, to go up to the next largest bit width, and then maxed
                // with 32 to ensure that we don't accidentally create an f16 type.
                Some(ResolvedTy::Float((int_bit_width * 2).max(32)))
            } else if int_bit_width < float_bit_width {
                Some(ResolvedTy::Float(float_bit_width))
            } else {
                None
            }
        }
        (ResolvedTy::Float(first_bit_width), ResolvedTy::Float(second_bit_width)) => {
            Some(ResolvedTy::Float(first_bit_width.max(second_bit_width)))
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
            if has_semantics_of(resolved_arena, distinct.clone(), other) {
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
/// an expected int typw with a bit width of `0` represents a "wildcard"
/// and will match to any found int type
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
            ResolvedTy::IInt(found_bit_width) | ResolvedTy::UInt(found_bit_width),
            ResolvedTy::Float(expected_bit_width),
        ) => found_bit_width == 0 || found_bit_width < expected_bit_width,
        (ResolvedTy::Float(found_bit_width), ResolvedTy::Float(expected_bit_width)) => {
            expected_bit_width == 0 || found_bit_width <= expected_bit_width
        }
        (
            ResolvedTy::Pointer {
                mutable: found_mutable,
                sub_ty: found_ty,
            },
            ResolvedTy::Pointer {
                mutable: expected_mutable,
                sub_ty: expected_ty,
            },
        ) => {
            matches!(
                (found_mutable, expected_mutable),
                (true, _) | (false, false)
            ) && can_fit(
                resolved_arena,
                resolved_arena[found_ty].clone(),
                resolved_arena[expected_ty].clone(),
            )
        }
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
                    resolved_arena[found_ty].clone(),
                    resolved_arena[expected_ty].clone(),
                )
        }
        (
            ResolvedTy::Distinct { uid: found_uid, .. },
            ResolvedTy::Distinct {
                uid: expected_uid, ..
            },
        ) => found_uid == expected_uid,
        (found, ResolvedTy::Distinct { ty, .. }) => {
            can_fit(resolved_arena, found, resolved_arena[ty].clone())
        }
        _ => false,
    }
}

pub(crate) fn primitive_castable(
    resolved_arena: &Arena<ResolvedTy>,
    from: ResolvedTy,
    to: ResolvedTy,
) -> bool {
    if can_fit(resolved_arena, from.clone(), to.clone()) {
        return true;
    }

    match (from, to) {
        (
            ResolvedTy::Bool | ResolvedTy::IInt(_) | ResolvedTy::UInt(_) | ResolvedTy::Float(_),
            ResolvedTy::Bool | ResolvedTy::IInt(_) | ResolvedTy::UInt(_) | ResolvedTy::Float(_),
        ) => true,
        (ResolvedTy::Distinct { ty: from, .. }, ResolvedTy::Distinct { ty: to, .. }) => {
            primitive_castable(
                resolved_arena,
                resolved_arena[from].clone(),
                resolved_arena[to].clone(),
            )
        }
        (ResolvedTy::Distinct { ty: from, .. }, to) => {
            primitive_castable(resolved_arena, resolved_arena[from].clone(), to)
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
    match (found.clone(), expected.clone()) {
        (ResolvedTy::Distinct { ty, .. }, ResolvedTy::IInt(0) | ResolvedTy::UInt(0)) => {
            if has_semantics_of(resolved_arena, resolved_arena[ty].clone(), expected.clone()) {
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
            if has_semantics_of(resolved_arena, resolved_arena[ty].clone(), expected) {
                return true;
            }
        }
        _ => {}
    }

    can_fit(resolved_arena, found, expected)
}

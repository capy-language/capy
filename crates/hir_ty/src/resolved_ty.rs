use hir::UnaryOp;
use internment::Intern;

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum ResolvedTy {
    NotYetResolved,
    Unknown,
    /// a bit-width of u32::MAX represents an isize
    /// a bit-width of 0 represents ANY signed integer type
    IInt(u32),
    /// a bit-width of u32::MAX represents a usize
    /// a bit-width of 0 represents ANY unsigned integer type
    UInt(u32),
    /// the bit-width can either be 32 or 64
    /// a bit-width of 0 represents ANY float type
    Float(u32),
    Bool,
    String,
    Char,
    Array {
        size: u64,
        sub_ty: Intern<ResolvedTy>,
    },
    Pointer {
        mutable: bool,
        sub_ty: Intern<ResolvedTy>,
    },
    Distinct {
        fqn: Option<hir::Fqn>,
        uid: u32,
        ty: Intern<ResolvedTy>,
    },
    Type,
    Any,
    Module(hir::FileName),
    // this is only ever used for functions defined locally
    Function {
        params: Vec<Intern<ResolvedTy>>,
        return_ty: Intern<ResolvedTy>,
    },
    Struct {
        fqn: Option<hir::Fqn>,
        uid: u32,
        fields: Vec<(hir::Name, Intern<ResolvedTy>)>,
    },
    Void,
}

pub(crate) struct BinaryOutputTy {
    pub(crate) max_ty: ResolvedTy,
    pub(crate) final_output_ty: ResolvedTy,
}

impl ResolvedTy {
    /// If self is a struct, this returns the fields
    pub fn as_struct(&self) -> Option<Vec<(hir::Name, Intern<ResolvedTy>)>> {
        match self {
            ResolvedTy::Struct { fields, .. } => Some(fields.clone()),
            ResolvedTy::Distinct { ty, .. } => ty.as_struct(),
            _ => None,
        }
    }

    /// If self is a function, this returns the parameters and return type
    pub fn as_function(&self) -> Option<(Vec<Intern<ResolvedTy>>, Intern<ResolvedTy>)> {
        match self {
            ResolvedTy::Function { params, return_ty } => Some((params.clone(), *return_ty)),
            ResolvedTy::Distinct { ty, .. } => ty.as_function(),
            _ => None,
        }
    }

    /// If self is a pointer, this returns the mutability and sub type
    pub fn as_pointer(&self) -> Option<(bool, Intern<ResolvedTy>)> {
        match self {
            ResolvedTy::Pointer { mutable, sub_ty } => Some((*mutable, *sub_ty)),
            ResolvedTy::Distinct { ty, .. } => ty.as_pointer(),
            _ => None,
        }
    }

    /// If self is an array, this returns the length and sub type
    pub fn as_array(&self) -> Option<(u64, Intern<ResolvedTy>)> {
        match self {
            ResolvedTy::Array { size, sub_ty } => Some((*size, *sub_ty)),
            ResolvedTy::Distinct { ty, .. } => ty.as_array(),
            _ => None,
        }
    }

    pub fn is_aggregate(&self) -> bool {
        match self {
            ResolvedTy::Struct { .. } => true,
            ResolvedTy::Array { .. } => true,
            ResolvedTy::Distinct { ty, .. } => ty.is_aggregate(),
            _ => false,
        }
    }

    pub fn is_array(&self) -> bool {
        match self {
            ResolvedTy::Array { .. } => true,
            ResolvedTy::Distinct { ty, .. } => ty.is_array(),
            _ => false,
        }
    }

    pub fn is_pointer(&self) -> bool {
        match self {
            ResolvedTy::Pointer { .. } => true,
            ResolvedTy::Distinct { ty, .. } => ty.is_pointer(),
            _ => false,
        }
    }

    pub fn is_function(&self) -> bool {
        match self {
            ResolvedTy::Function { .. } => true,
            ResolvedTy::Distinct { ty, .. } => ty.is_function(),
            _ => false,
        }
    }

    pub fn is_struct(&self) -> bool {
        match self {
            ResolvedTy::Struct { .. } => true,
            ResolvedTy::Distinct { ty, .. } => ty.is_struct(),
            _ => false,
        }
    }

    /// returns true if the type is void, or contains void, or is an empty array, etc.
    pub fn is_empty(&self) -> bool {
        match self {
            ResolvedTy::Void => true,
            ResolvedTy::Type => true,
            ResolvedTy::Pointer { sub_ty, .. } => sub_ty.is_empty(),
            ResolvedTy::Distinct { ty, .. } => ty.is_empty(),
            _ => false,
        }
    }

    /// returns true if the type is unknown, or contains unknown, or is an unknown array, etc.
    pub fn is_unknown(&self) -> bool {
        match self {
            ResolvedTy::NotYetResolved => true,
            ResolvedTy::Unknown => true,
            ResolvedTy::Pointer { sub_ty, .. } => sub_ty.is_unknown(),
            ResolvedTy::Array { size, sub_ty } => *size == 0 || sub_ty.is_unknown(),
            ResolvedTy::Struct { fields, .. } => fields.iter().any(|(_, ty)| ty.is_unknown()),
            ResolvedTy::Distinct { ty, .. } => ty.is_unknown(),
            _ => false,
        }
    }

    /// A true equality check
    pub fn is_equal_to(&self, other: &Self) -> bool {
        if self == other {
            return true;
        }

        match (self, other) {
            (
                ResolvedTy::Array {
                    size: first_size,
                    sub_ty: first_sub_ty,
                },
                ResolvedTy::Array {
                    size: second_size,
                    sub_ty: second_sub_ty,
                    ..
                },
            ) => first_size == second_size && first_sub_ty.is_equal_to(second_sub_ty),
            (
                ResolvedTy::Pointer {
                    mutable: first_mutable,
                    sub_ty: first_sub_ty,
                },
                ResolvedTy::Pointer {
                    mutable: second_mutable,
                    sub_ty: second_sub_ty,
                },
            ) => first_mutable == second_mutable && first_sub_ty.is_equal_to(second_sub_ty),
            (ResolvedTy::Distinct { uid: first, .. }, ResolvedTy::Distinct { uid: second, .. }) => {
                first == second
            }
            (
                ResolvedTy::Function {
                    params: first_params,
                    return_ty: first_return_ty,
                },
                ResolvedTy::Function {
                    params: second_params,
                    return_ty: second_return_ty,
                },
            ) => {
                first_return_ty.is_equal_to(second_return_ty)
                    && first_params.len() == second_params.len()
                    && first_params
                        .iter()
                        .zip(second_params.iter())
                        .all(|(first_param, second_param)| first_param.is_equal_to(second_param))
            }
            _ => false,
        }
    }

    /// an equality check that ignores distinct types.
    /// All other types must be exactly equal (i32 == i32, i32 != i64)
    pub fn is_functionally_equivalent_to(&self, other: &Self) -> bool {
        match (self, other) {
            (
                ResolvedTy::Array {
                    size: first_size,
                    sub_ty: first_sub_ty,
                },
                ResolvedTy::Array {
                    size: second_size,
                    sub_ty: second_sub_ty,
                    ..
                },
            ) => {
                first_size == second_size
                    && first_sub_ty.is_functionally_equivalent_to(second_sub_ty)
            }
            (
                ResolvedTy::Pointer {
                    mutable: first_mutable,
                    sub_ty: first_sub_ty,
                },
                ResolvedTy::Pointer {
                    mutable: second_mutable,
                    sub_ty: second_sub_ty,
                },
            ) => {
                first_mutable == second_mutable
                    && first_sub_ty.is_functionally_equivalent_to(second_sub_ty)
            }
            (ResolvedTy::Distinct { ty: first, .. }, ResolvedTy::Distinct { ty: second, .. }) => {
                first.is_functionally_equivalent_to(second)
            }
            (
                ResolvedTy::Distinct {
                    ty: distinct_inner, ..
                },
                other,
            )
            | (
                other,
                ResolvedTy::Distinct {
                    ty: distinct_inner, ..
                },
            ) => {
                // println!("  {:?} as {:?}", other, resolved_arena[distinct]);
                distinct_inner.is_functionally_equivalent_to(other)
            }
            (first, second) => first.is_equal_to(second),
        }
    }

    pub(crate) fn get_max_int_size(&self) -> Option<u64> {
        match self {
            ResolvedTy::IInt(bit_width) => match bit_width {
                8 => Some(i8::MAX as u64),
                16 => Some(i16::MAX as u64),
                32 => Some(i32::MAX as u64),
                64 | 128 => Some(i64::MAX as u64),
                _ => None,
            },
            ResolvedTy::UInt(bit_width) => match bit_width {
                8 => Some(u8::MAX as u64),
                16 => Some(u16::MAX as u64),
                32 => Some(u32::MAX as u64),
                64 | 128 => Some(u64::MAX),
                _ => None,
            },
            ResolvedTy::Distinct { ty, .. } => ty.get_max_int_size(),
            _ => None,
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
    pub(crate) fn max(&self, other: &ResolvedTy) -> Option<ResolvedTy> {
        if self == other {
            return Some(self.clone());
        }

        match (self, other) {
            (ResolvedTy::UInt(0), ResolvedTy::UInt(0)) => Some(ResolvedTy::UInt(0)),
            (
                ResolvedTy::IInt(0) | ResolvedTy::UInt(0),
                ResolvedTy::IInt(0) | ResolvedTy::UInt(0),
            ) => Some(ResolvedTy::IInt(0)),
            (ResolvedTy::IInt(first_bit_width), ResolvedTy::IInt(second_bit_width)) => {
                Some(ResolvedTy::IInt(*first_bit_width.max(second_bit_width)))
            }
            (ResolvedTy::UInt(first_bit_width), ResolvedTy::UInt(second_bit_width)) => {
                Some(ResolvedTy::UInt(*first_bit_width.max(second_bit_width)))
            }
            (ResolvedTy::IInt(signed_bit_width), ResolvedTy::UInt(unsigned_bit_width))
            | (ResolvedTy::UInt(unsigned_bit_width), ResolvedTy::IInt(signed_bit_width)) => {
                if signed_bit_width > unsigned_bit_width {
                    Some(ResolvedTy::IInt(*signed_bit_width))
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
                Some(ResolvedTy::Float(*float_bit_width))
            }
            (
                ResolvedTy::IInt(int_bit_width) | ResolvedTy::UInt(int_bit_width),
                ResolvedTy::Float(float_bit_width),
            )
            | (
                ResolvedTy::Float(float_bit_width),
                ResolvedTy::IInt(int_bit_width) | ResolvedTy::UInt(int_bit_width),
            ) => {
                if *int_bit_width < 64 && *float_bit_width == 0 {
                    // the int bit width must be smaller than the final float which can only go up to 64 bits,
                    // the int bit width is doubled, to go up to the next largest bit width, and then maxed
                    // with 32 to ensure that we don't accidentally create an f16 type.
                    Some(ResolvedTy::Float((int_bit_width * 2).max(32)))
                } else if int_bit_width < float_bit_width {
                    Some(ResolvedTy::Float(*float_bit_width))
                } else {
                    None
                }
            }
            (ResolvedTy::Float(first_bit_width), ResolvedTy::Float(second_bit_width)) => {
                Some(ResolvedTy::Float(*first_bit_width.max(second_bit_width)))
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
                    fqn: *fqn,
                    uid: *uid,
                    ty: *distinct_ty,
                };
                if distinct.has_semantics_of(other) {
                    Some(distinct)
                } else {
                    None
                }
            }
            (ResolvedTy::Unknown, other) | (other, ResolvedTy::Unknown) => Some(other.clone()),
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
    /// Any int can fit into a wildcard int type (bit-width of 0)
    ///
    /// diagram stolen from vlang docs bc i liked it
    pub(crate) fn can_fit_into(&self, expected: &ResolvedTy) -> bool {
        if self == expected {
            return true;
        }

        match (self, expected) {
            // the callers of can_fit_into should probably
            // execute their own logic if one of the types is unknown
            (ResolvedTy::Unknown, _) | (_, ResolvedTy::Unknown) => true,
            (ResolvedTy::IInt(found_bit_width), ResolvedTy::IInt(expected_bit_width))
            | (ResolvedTy::UInt(found_bit_width), ResolvedTy::UInt(expected_bit_width)) => {
                *expected_bit_width == 0 || found_bit_width <= expected_bit_width
            }
            // we allow this because the uint is weak
            (ResolvedTy::IInt(_), ResolvedTy::UInt(0)) => true,
            // we don't allow this case because of the loss of the sign
            (ResolvedTy::IInt(_), ResolvedTy::UInt(_)) => false,
            (ResolvedTy::UInt(found_bit_width), ResolvedTy::IInt(expected_bit_width)) => {
                *expected_bit_width == 0 || found_bit_width < expected_bit_width
            }
            (
                ResolvedTy::IInt(found_bit_width) | ResolvedTy::UInt(found_bit_width),
                ResolvedTy::Float(expected_bit_width),
            ) => *found_bit_width == 0 || found_bit_width < expected_bit_width,
            (ResolvedTy::Float(found_bit_width), ResolvedTy::Float(expected_bit_width)) => {
                *expected_bit_width == 0 || found_bit_width <= expected_bit_width
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
                ) && (**expected_ty == ResolvedTy::Any || found_ty.can_fit_into(expected_ty))
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
            ) => found_size == expected_size && found_ty.can_fit_into(expected_ty),
            (
                ResolvedTy::Struct { uid: found_uid, .. },
                ResolvedTy::Struct {
                    uid: expected_uid, ..
                },
            ) => found_uid == expected_uid,
            (
                ResolvedTy::Distinct { uid: found_uid, .. },
                ResolvedTy::Distinct {
                    uid: expected_uid, ..
                },
            ) => found_uid == expected_uid,
            (found, ResolvedTy::Distinct { ty, .. }) => found.can_fit_into(ty),
            (found, expected) => found.is_equal_to(expected),
        }
    }

    /// This is used for the `as` operator to see whether something can be casted into something else
    ///
    /// This only allows primitives to be casted to each other, or types that are already equal
    pub(crate) fn primitive_castable(&self, primitive_ty: &ResolvedTy) -> bool {
        match (self, primitive_ty) {
            (
                ResolvedTy::Bool
                | ResolvedTy::IInt(_)
                | ResolvedTy::UInt(_)
                | ResolvedTy::Float(_)
                | ResolvedTy::Char,
                ResolvedTy::Bool
                | ResolvedTy::IInt(_)
                | ResolvedTy::UInt(_)
                | ResolvedTy::Float(_)
                | ResolvedTy::Char,
            ) => true,
            // todo: right now all the fields must be exactly equal,
            // technically it would be possible to make it so that fields autocast
            // but I'm lazy and that would require some changes in the codegen crate
            (
                ResolvedTy::Struct {
                    fields: found_fields,
                    ..
                },
                ResolvedTy::Struct {
                    fields: expected_fields,
                    ..
                },
            ) => {
                found_fields.len() == expected_fields.len()
                    && found_fields.iter().zip(expected_fields.iter()).all(
                        |((found_name, found_ty), (expected_name, expected_ty))| {
                            found_name == expected_name
                                && found_ty.is_functionally_equivalent_to(expected_ty)
                        },
                    )
            }
            (ResolvedTy::Distinct { ty: from, .. }, ResolvedTy::Distinct { ty: to, .. }) => {
                from.primitive_castable(to)
            }
            (ResolvedTy::Distinct { ty: distinct, .. }, other)
            | (other, ResolvedTy::Distinct { ty: distinct, .. }) => {
                distinct.primitive_castable(other)
            }
            (
                ResolvedTy::Pointer {
                    mutable: found_mutable,
                    sub_ty: found_sub_ty,
                },
                ResolvedTy::Pointer {
                    mutable: expected_mutable,
                    sub_ty: expected_sub_ty,
                },
            ) => {
                matches!(
                    (found_mutable, expected_mutable),
                    (true, _) | (false, false)
                ) && (found_sub_ty == expected_sub_ty
                    || **found_sub_ty == ResolvedTy::Any
                    || **expected_sub_ty == ResolvedTy::Any)
            }
            // string to and from ^any and ^u8
            (ResolvedTy::String, ResolvedTy::Pointer { sub_ty, .. })
            | (ResolvedTy::Pointer { sub_ty, .. }, ResolvedTy::String) => {
                matches!(
                    sub_ty.as_ref(),
                    ResolvedTy::Any | ResolvedTy::UInt(8) | ResolvedTy::Char
                )
            }
            _ => self.is_functionally_equivalent_to(primitive_ty),
        }
    }

    /// allows `distinct` types to have the same semantics as other types as long as the inner type matches
    pub(crate) fn has_semantics_of(&self, expected: &ResolvedTy) -> bool {
        match (self, expected) {
            (ResolvedTy::Distinct { ty, .. }, ResolvedTy::IInt(0) | ResolvedTy::UInt(0)) => {
                if ty.has_semantics_of(expected) {
                    return true;
                }
            }
            (ResolvedTy::Distinct { .. }, ResolvedTy::IInt(_) | ResolvedTy::UInt(_)) => {
                return false
            }
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
            (ResolvedTy::Distinct { ty: inner_ty, .. }, expected) => {
                if inner_ty.has_semantics_of(expected) {
                    return true;
                }
            }
            _ => {}
        }

        self.can_fit_into(expected)
    }

    pub(crate) fn is_weak_type_replaceable_by(&self, expected: &ResolvedTy) -> bool {
        // println!("  is_weak_type_replaceable({:?}, {:?})", found, expected);
        match (self, expected) {
            // weak signed to strong signed, or weak unsigned to strong unsigned
            (ResolvedTy::IInt(0), ResolvedTy::IInt(bit_width))
            | (ResolvedTy::UInt(0), ResolvedTy::UInt(bit_width)) => *bit_width != 0,
            // always accept a switch of sign
            (ResolvedTy::IInt(0), ResolvedTy::UInt(_))
            | (ResolvedTy::UInt(0), ResolvedTy::IInt(_)) => true,
            // always accept a switch to float
            (ResolvedTy::IInt(0) | ResolvedTy::UInt(0), ResolvedTy::Float(_)) => true,
            // weak float to strong float
            (ResolvedTy::Float(0), ResolvedTy::Float(bit_width)) => *bit_width != 0,
            (
                ResolvedTy::Array {
                    size: found_size,
                    sub_ty: found_sub_ty,
                },
                ResolvedTy::Array {
                    size: expected_size,
                    sub_ty: expected_sub_ty,
                },
            ) => {
                found_size == expected_size
                    && found_sub_ty.is_weak_type_replaceable_by(expected_sub_ty)
            }
            (
                ResolvedTy::Pointer {
                    mutable: found_mutable,
                    sub_ty: found_sub_ty,
                },
                ResolvedTy::Pointer {
                    mutable: expected_mutable,
                    sub_ty: expected_sub_ty,
                },
            ) => {
                matches!(
                    (found_mutable, expected_mutable),
                    (true, _) | (false, false)
                ) && found_sub_ty.is_weak_type_replaceable_by(expected_sub_ty)
            }
            // Right now there are no weak structs, so having this doesn't make sense
            // Maybe in the future if we have `.{}` syntax we can figure something out
            // (
            //     ResolvedTy::Struct {
            //         fields: found_fields,
            //         ..
            //     },
            //     ResolvedTy::Struct {
            //         fields: expected_fields,
            //         ..
            //     },
            // ) => {
            //     self.can_fit_into(expected)
            //         && found_fields.iter().zip(expected_fields.iter()).any(
            //             |((_, found_ty), (_, expected_ty))| {
            //                 found_ty.is_weak_type_replaceable_by(expected_ty)
            //             },
            //         )
            // }
            (
                ResolvedTy::Distinct { uid: found_uid, .. },
                ResolvedTy::Distinct {
                    uid: expected_uid, ..
                },
            ) => found_uid == expected_uid,
            (found, ResolvedTy::Distinct { ty, .. }) => found.is_weak_type_replaceable_by(ty),
            _ => false,
        }
    }
}

pub(crate) trait BinaryOutput {
    fn get_possible_output_ty(
        &self,
        first: &ResolvedTy,
        second: &ResolvedTy,
    ) -> Option<BinaryOutputTy>;
}

impl BinaryOutput for hir::BinaryOp {
    /// should check with `can_perform` before actually using the type emitted from this function
    fn get_possible_output_ty(
        &self,
        first: &ResolvedTy,
        second: &ResolvedTy,
    ) -> Option<BinaryOutputTy> {
        first.max(second).map(|max_ty| BinaryOutputTy {
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
}

pub(crate) trait UnaryOutput {
    fn get_possible_output_ty(&self, input: Intern<ResolvedTy>) -> Intern<ResolvedTy>;
}

impl UnaryOutput for UnaryOp {
    fn get_possible_output_ty(&self, input: Intern<ResolvedTy>) -> Intern<ResolvedTy> {
        match self {
            hir::UnaryOp::Neg => match *input {
                ResolvedTy::UInt(bit_width) => ResolvedTy::IInt(bit_width).into(),
                _ => input,
            },
            hir::UnaryOp::Pos | hir::UnaryOp::Not => input,
        }
    }
}

pub(crate) trait TypedOp {
    fn can_perform(&self, ty: &ResolvedTy) -> bool;

    fn default_ty(&self) -> ResolvedTy;
}

impl TypedOp for hir::BinaryOp {
    fn can_perform(&self, found: &ResolvedTy) -> bool {
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
            | hir::BinaryOp::Ne => &[ResolvedTy::IInt(0), ResolvedTy::Float(0)],
            hir::BinaryOp::And | hir::BinaryOp::Or => &[ResolvedTy::Bool],
        };

        expected
            .iter()
            .any(|expected| found.has_semantics_of(expected))
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

impl TypedOp for hir::UnaryOp {
    fn can_perform(&self, found: &ResolvedTy) -> bool {
        let expected: &[ResolvedTy] = match self {
            hir::UnaryOp::Neg | hir::UnaryOp::Pos => &[ResolvedTy::IInt(0), ResolvedTy::Float(0)],
            hir::UnaryOp::Not => &[ResolvedTy::Bool],
        };

        expected
            .iter()
            .any(|expected| found.has_semantics_of(expected))
    }

    fn default_ty(&self) -> ResolvedTy {
        match self {
            hir::UnaryOp::Neg | hir::UnaryOp::Pos => ResolvedTy::IInt(0),
            hir::UnaryOp::Not => ResolvedTy::Bool,
        }
    }
}

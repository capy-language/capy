use hir::{PrimitiveTy, UnaryOp};
use internment::Intern;
use rustc_hash::FxHashMap;

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum Ty {
    NotYetResolved,
    Unknown,
    /// a bit-width of u32::MAX represents an isize
    /// a bit-width of 0 represents ANY signed integer type
    IInt(u8),
    /// a bit-width of u32::MAX represents a usize
    /// a bit-width of 0 represents ANY unsigned integer type
    UInt(u8),
    /// the bit-width can either be 32 or 64
    /// a bit-width of 0 represents ANY float type
    Float(u8),
    Bool,
    String,
    Char,
    Array {
        anonymous: bool,
        size: u64,
        sub_ty: Intern<Ty>,
    },
    Slice {
        sub_ty: Intern<Ty>,
    },
    Pointer {
        mutable: bool,
        sub_ty: Intern<Ty>,
    },
    Distinct {
        fqn: Option<hir::Fqn>,
        uid: u32,
        sub_ty: Intern<Ty>,
    },
    Type,
    Any,
    File(hir::FileName),
    // this is only ever used for functions defined locally
    Function {
        param_tys: Vec<Intern<Ty>>,
        return_ty: Intern<Ty>,
    },
    Struct {
        // if anonymous is set to `true`, `uid` is useless
        anonymous: bool,
        fqn: Option<hir::Fqn>,
        uid: u32,
        members: Vec<(hir::Name, Intern<Ty>)>,
    },
    Void,
    // only used for blocks that always break.
    // kind of like a "noreturn" type.
    // the block will never reach it's own end,
    // but the blocks above it might reach theirs.
    NoEval,
}

pub(crate) struct BinaryOutputTy {
    pub(crate) max_ty: Ty,
    pub(crate) final_output_ty: Ty,
}

impl Ty {
    pub(crate) fn from_primitive(primitive: PrimitiveTy) -> Self {
        match primitive {
            PrimitiveTy::IInt { bit_width, .. } => Self::IInt(bit_width),
            PrimitiveTy::UInt { bit_width, .. } => Self::UInt(bit_width),
            PrimitiveTy::Float { bit_width, .. } => Self::Float(bit_width),
            PrimitiveTy::Bool { .. } => Self::Bool,
            PrimitiveTy::String { .. } => Self::String,
            PrimitiveTy::Char { .. } => Self::Char,
            PrimitiveTy::Type { .. } => Self::Type,
            PrimitiveTy::Any { .. } => Self::Any,
            PrimitiveTy::Void { .. } => Self::Void,
        }
    }

    pub fn has_default_value(&self) -> bool {
        match self {
            Ty::NotYetResolved => true,
            Ty::Unknown => true,
            Ty::IInt(_) => true,
            Ty::UInt(_) => true,
            Ty::Float(_) => true,
            Ty::Bool => true,
            Ty::String => false,
            Ty::Char => true,
            Ty::Array { sub_ty, .. } => sub_ty.has_default_value(),
            Ty::Slice { .. } => false,
            Ty::Pointer { .. } => false,
            Ty::Distinct { sub_ty, .. } => sub_ty.has_default_value(),
            Ty::Type => false,
            Ty::Any => false,
            Ty::File(_) => false,
            Ty::Function { .. } => false,
            Ty::Struct { members, .. } => members.iter().all(|(_, ty)| ty.has_default_value()),
            Ty::Void => true,
            Ty::NoEval => true,
        }
    }

    /// If self is a struct, this returns the fields
    pub fn as_struct(&self) -> Option<Vec<(hir::Name, Intern<Ty>)>> {
        match self {
            Ty::Struct { members, .. } => Some(members.clone()),
            Ty::Distinct { sub_ty, .. } => sub_ty.as_struct(),
            _ => None,
        }
    }

    /// If self is a function, this returns the parameters and return type
    pub fn as_function(&self) -> Option<(Vec<Intern<Ty>>, Intern<Ty>)> {
        match self {
            Ty::Function {
                param_tys: params,
                return_ty,
            } => Some((params.clone(), *return_ty)),
            Ty::Distinct { sub_ty, .. } => sub_ty.as_function(),
            _ => None,
        }
    }

    /// If self is a pointer, this returns the mutability and sub type
    pub fn as_pointer(&self) -> Option<(bool, Intern<Ty>)> {
        match self {
            Ty::Pointer { mutable, sub_ty } => Some((*mutable, *sub_ty)),
            Ty::Distinct { sub_ty, .. } => sub_ty.as_pointer(),
            _ => None,
        }
    }

    /// If self is an array, this returns the length and sub type
    pub fn as_array(&self) -> Option<(u64, Intern<Ty>)> {
        match self {
            Ty::Array { size, sub_ty, .. } => Some((*size, *sub_ty)),
            Ty::Distinct { sub_ty, .. } => sub_ty.as_array(),
            _ => None,
        }
    }

    /// If self is a slice, this returns the sub type
    pub fn as_slice(&self) -> Option<Intern<Ty>> {
        match self {
            Ty::Slice { sub_ty } => Some(*sub_ty),
            Ty::Distinct { sub_ty, .. } => sub_ty.as_slice(),
            _ => None,
        }
    }

    pub fn is_any_type(&self) -> bool {
        match self {
            Ty::Any => true,
            Ty::Distinct { sub_ty, .. } => sub_ty.is_any_type(),
            _ => false,
        }
    }

    pub fn is_aggregate(&self) -> bool {
        match self {
            Ty::Struct { .. } => true,
            Ty::Array { .. } => true,
            Ty::Slice { .. } => true,
            Ty::Distinct { sub_ty, .. } => sub_ty.is_aggregate(),
            _ => false,
        }
    }

    pub fn is_array(&self) -> bool {
        match self {
            Ty::Array { .. } => true,
            Ty::Distinct { sub_ty, .. } => sub_ty.is_array(),
            _ => false,
        }
    }

    pub fn is_slice(&self) -> bool {
        match self {
            Ty::Slice { .. } => true,
            Ty::Distinct { sub_ty, .. } => sub_ty.is_slice(),
            _ => false,
        }
    }

    pub fn is_pointer(&self) -> bool {
        match self {
            Ty::Pointer { .. } => true,
            Ty::Distinct { sub_ty, .. } => sub_ty.is_pointer(),
            _ => false,
        }
    }

    pub fn is_function(&self) -> bool {
        match self {
            Ty::Function { .. } => true,
            Ty::Distinct { sub_ty, .. } => sub_ty.is_function(),
            _ => false,
        }
    }

    pub fn is_struct(&self) -> bool {
        match self {
            Ty::Struct { .. } => true,
            Ty::Distinct { sub_ty, .. } => sub_ty.is_struct(),
            _ => false,
        }
    }

    /// Returns `true` if the struct contains only a `^any` and a `type`
    pub fn is_any_struct(&self) -> bool {
        match self {
            Ty::Struct { members, .. } => {
                if members.len() != 2 {
                    return false;
                }

                matches!(
                    (members[0].1.as_ref(), members[1].1.as_ref()),
                    (Ty::Pointer { sub_ty, .. }, Ty::Type) | (Ty::Type, Ty::Pointer { sub_ty, mutable: false })
                        if matches!(sub_ty.as_ref(), Ty::Any))
            }
            Ty::Distinct { sub_ty, .. } => sub_ty.is_any_struct(),
            _ => false,
        }
    }

    /// returns true if the type is zero-sized
    pub fn is_zero_sized(&self) -> bool {
        match self {
            Ty::NotYetResolved | Ty::Unknown => true,
            Ty::Void => true,
            Ty::File(_) => true,
            Ty::NoEval => true,
            Ty::Array { size, sub_ty, .. } => *size == 0 || sub_ty.is_zero_sized(),
            Ty::Struct { members, .. } => {
                members.is_empty() || members.iter().all(|(_, ty)| ty.is_zero_sized())
            }
            Ty::Distinct { sub_ty: ty, .. } => ty.is_zero_sized(),
            _ => false,
        }
    }

    pub fn is_void(&self) -> bool {
        match self {
            Ty::Void => true,
            Ty::Distinct { sub_ty, .. } => sub_ty.is_void(),
            _ => false,
        }
    }

    pub fn is_int(&self) -> bool {
        match self {
            Ty::IInt(_) | Ty::UInt(_) => true,
            Ty::Distinct { sub_ty, .. } => sub_ty.is_int(),
            _ => false,
        }
    }
    
    pub fn is_float(&self) -> bool {
        match self {
            Ty::Float(_) => true,
            Ty::Distinct { sub_ty, .. } => sub_ty.is_float(),
            _ => false,
        }
    }

    /// returns true if the type is unknown, or contains unknown, or is an unknown array, etc.
    pub fn is_unknown(&self) -> bool {
        match self {
            Ty::NotYetResolved => true,
            Ty::Unknown => true,
            Ty::Pointer { sub_ty, .. } => sub_ty.is_unknown(),
            Ty::Array { sub_ty, .. } => sub_ty.is_unknown(),
            Ty::Struct { members, .. } => members.iter().any(|(_, ty)| ty.is_unknown()),
            Ty::Distinct { sub_ty, .. } => sub_ty.is_unknown(),
            Ty::Function {
                param_tys,
                return_ty,
            } => param_tys.iter().any(|p| p.is_unknown()) || return_ty.is_unknown(),
            _ => false,
        }
    }

    pub fn is_equal_to(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Ty::Array {
                    anonymous: first_anon,
                    size: first_size,
                    sub_ty: first_sub_ty,
                },
                Ty::Array {
                    anonymous: second_anon,
                    size: second_size,
                    sub_ty: second_sub_ty,
                    ..
                },
            ) => {
                first_anon == second_anon
                    && first_size == second_size
                    && first_sub_ty.is_equal_to(second_sub_ty)
            }
            (
                Ty::Pointer {
                    mutable: first_mutable,
                    sub_ty: first_sub_ty,
                },
                Ty::Pointer {
                    mutable: second_mutable,
                    sub_ty: second_sub_ty,
                },
            ) => first_mutable == second_mutable && first_sub_ty.is_equal_to(second_sub_ty),
            (Ty::Distinct { uid: first, .. }, Ty::Distinct { uid: second, .. }) => first == second,
            (
                Ty::Function {
                    param_tys: first_params,
                    return_ty: first_return_ty,
                },
                Ty::Function {
                    param_tys: second_params,
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
            (
                Ty::Struct {
                    anonymous: true,
                    members: first_members,
                    ..
                },
                Ty::Struct {
                    anonymous: true,
                    members: second_members,
                    ..
                },
            ) => {
                first_members.len() == second_members.len()
                    && first_members.iter().zip(second_members.iter()).all(
                        |((first_name, first_ty), (second_name, second_ty))| {
                            first_name == second_name && first_ty.is_equal_to(second_ty)
                        },
                    )
            }
            (
                Ty::Struct {
                    anonymous: false,
                    uid: first_uid,
                    ..
                },
                Ty::Struct {
                    anonymous: false,
                    uid: second_uid,
                    ..
                },
            ) => first_uid == second_uid,
            _ => self == other,
        }
    }

    /// an equality check that ignores distinct types.
    /// All other types must be exactly equal (i32 == i32, i32 != i64)
    ///
    /// if `two_way` is false, distincts cannot be made non-distinct.
    ///
    /// This function must guarentee that if A is functionally equivalent to B,
    /// then the bytes that make up A are also valid bytes for B
    pub fn is_functionally_equivalent_to(&self, other: &Self, two_way: bool) -> bool {
        match (self, other) {
            (
                Ty::Array {
                    anonymous: first_anon,
                    size: first_size,
                    sub_ty: first_sub_ty,
                },
                Ty::Array {
                    anonymous: second_anon,
                    size: second_size,
                    sub_ty: second_sub_ty,
                    ..
                },
            ) => {
                first_anon == second_anon
                    && first_size == second_size
                    && first_sub_ty.is_functionally_equivalent_to(second_sub_ty, two_way)
            }
            (
                Ty::Pointer {
                    mutable: first_mutable,
                    sub_ty: first_sub_ty,
                },
                Ty::Pointer {
                    mutable: second_mutable,
                    sub_ty: second_sub_ty,
                },
            ) => {
                first_mutable == second_mutable
                    && first_sub_ty.is_functionally_equivalent_to(second_sub_ty, two_way)
            }
            (Ty::Distinct { sub_ty: first, .. }, Ty::Distinct { sub_ty: second, .. }) => {
                first.is_functionally_equivalent_to(second, two_way)
            }
            (
                Ty::Distinct {
                    sub_ty: distinct_inner,
                    ..
                },
                other,
            ) => two_way && distinct_inner.is_functionally_equivalent_to(other, two_way),
            (
                other,
                Ty::Distinct {
                    sub_ty: distinct_inner,
                    ..
                },
            ) => {
                // println!("  {:?} as {:?}", other, resolved_arena[distinct]);
                other.is_functionally_equivalent_to(distinct_inner, two_way)
            }
            (
                Ty::Struct {
                    members: first_members,
                    ..
                },
                Ty::Struct {
                    members: second_members,
                    ..
                },
            ) => {
                first_members.len() == second_members.len()
                    && first_members.iter().zip(second_members.iter()).all(
                        |((first_name, first_ty), (second_name, second_ty))| {
                            first_name == second_name
                                && first_ty.is_functionally_equivalent_to(second_ty, two_way)
                        },
                    )
            }
            (first, second) => first.is_equal_to(second),
        }
    }

    pub(crate) fn get_max_int_size(&self) -> Option<u64> {
        match self {
            Ty::IInt(bit_width) => match bit_width {
                8 => Some(i8::MAX as u64),
                16 => Some(i16::MAX as u64),
                32 => Some(i32::MAX as u64),
                64 | 128 => Some(i64::MAX as u64),
                _ => None,
            },
            Ty::UInt(bit_width) => match bit_width {
                8 => Some(u8::MAX as u64),
                16 => Some(u16::MAX as u64),
                32 => Some(u32::MAX as u64),
                64 | 128 => Some(u64::MAX),
                _ => None,
            },
            Ty::Distinct { sub_ty: ty, .. } => ty.get_max_int_size(),
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
    pub(crate) fn max(&self, other: &Ty) -> Option<Ty> {
        if self.is_equal_to(other) {
            return Some(self.clone());
        }

        match (self, other) {
            (Ty::UInt(0), Ty::UInt(0)) => Some(Ty::UInt(0)),
            (Ty::IInt(0) | Ty::UInt(0), Ty::IInt(0) | Ty::UInt(0)) => Some(Ty::IInt(0)),
            (Ty::IInt(first_bit_width), Ty::IInt(second_bit_width)) => {
                Some(Ty::IInt(*first_bit_width.max(second_bit_width)))
            }
            (Ty::UInt(first_bit_width), Ty::UInt(second_bit_width)) => {
                Some(Ty::UInt(*first_bit_width.max(second_bit_width)))
            }
            (Ty::IInt(signed_bit_width), Ty::UInt(unsigned_bit_width))
            | (Ty::UInt(unsigned_bit_width), Ty::IInt(signed_bit_width)) => {
                if signed_bit_width > unsigned_bit_width {
                    Some(Ty::IInt(*signed_bit_width))
                } else {
                    // println!(
                    //     "{:?} does not fit into {:?}",
                    //     unsigned_bit_width, signed_bit_width
                    // );
                    None
                }
            }
            (Ty::IInt(0) | Ty::UInt(0), Ty::Float(float_bit_width))
            | (Ty::Float(float_bit_width), Ty::IInt(0) | Ty::UInt(0)) => {
                Some(Ty::Float(*float_bit_width))
            }
            (Ty::IInt(int_bit_width) | Ty::UInt(int_bit_width), Ty::Float(float_bit_width))
            | (Ty::Float(float_bit_width), Ty::IInt(int_bit_width) | Ty::UInt(int_bit_width)) => {
                if *int_bit_width < 64 && *float_bit_width == 0 {
                    // the int bit width must be smaller than the final float which can only go up to 64 bits,
                    // the int bit width is doubled, to go up to the next largest bit width, and then maxed
                    // with 32 to ensure that we don't accidentally create an f16 type.
                    Some(Ty::Float((int_bit_width * 2).max(32)))
                } else if int_bit_width < float_bit_width {
                    Some(Ty::Float(*float_bit_width))
                } else {
                    None
                }
            }
            (Ty::Float(first_bit_width), Ty::Float(second_bit_width)) => {
                Some(Ty::Float(*first_bit_width.max(second_bit_width)))
            }
            (
                Ty::Distinct {
                    fqn,
                    uid,
                    sub_ty: distinct_ty,
                },
                other,
            )
            | (
                other,
                Ty::Distinct {
                    fqn,
                    uid,
                    sub_ty: distinct_ty,
                },
            ) => {
                let distinct = Ty::Distinct {
                    fqn: *fqn,
                    uid: *uid,
                    sub_ty: *distinct_ty,
                };
                if distinct.has_semantics_of(other) {
                    Some(distinct)
                } else {
                    None
                }
            }
            (Ty::Unknown | Ty::NoEval, other) | (other, Ty::Unknown | Ty::NoEval) => {
                Some(other.clone())
            }
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
    pub(crate) fn can_fit_into(&self, expected: &Ty) -> bool {
        if self.is_equal_to(expected) {
            return true;
        }

        match (self, expected) {
            // the callers of can_fit_into should probably
            // execute their own logic if one of the types is unknown
            (Ty::Unknown, _) | (_, Ty::Unknown) => true,
            (Ty::NoEval, _) => true,
            (Ty::IInt(found_bit_width), Ty::IInt(expected_bit_width))
            | (Ty::UInt(found_bit_width), Ty::UInt(expected_bit_width)) => {
                *expected_bit_width == 0 || found_bit_width <= expected_bit_width
            }
            // we allow this because the uint is weak
            (Ty::IInt(_), Ty::UInt(0)) => true,
            // we don't allow this case because of the loss of the sign
            (Ty::IInt(_), Ty::UInt(_)) => false,
            (Ty::UInt(found_bit_width), Ty::IInt(expected_bit_width)) => {
                *expected_bit_width == 0 || found_bit_width < expected_bit_width
            }
            (
                Ty::IInt(found_bit_width) | Ty::UInt(found_bit_width),
                Ty::Float(expected_bit_width),
            ) => *found_bit_width == 0 || found_bit_width < expected_bit_width,
            (Ty::Float(found_bit_width), Ty::Float(expected_bit_width)) => {
                *expected_bit_width == 0 || found_bit_width <= expected_bit_width
            }
            (
                Ty::Pointer {
                    mutable: found_mutable,
                    sub_ty: found_ty,
                },
                Ty::Pointer {
                    mutable: expected_mutable,
                    sub_ty: expected_ty,
                },
            ) => {
                matches!(
                    (found_mutable, expected_mutable),
                    (true, _) | (false, false)
                ) && ((**expected_ty == Ty::Any && !found_ty.might_be_weak())
                    || found_ty.can_fit_into(expected_ty))
            }
            (
                Ty::Slice { sub_ty: found_ty },
                Ty::Slice {
                    sub_ty: expected_ty,
                },
            ) => {
                // todo: do we need this `might_be_weak`?
                (**expected_ty == Ty::Any && !found_ty.might_be_weak())
                    || found_ty.can_fit_into(expected_ty)
            }
            (
                Ty::Array {
                    anonymous,
                    sub_ty: found_ty,
                    ..
                },
                Ty::Slice {
                    sub_ty: expected_ty,
                },
            ) => {
                (*anonymous && found_ty.is_weak_replaceable_by(expected_ty))
                    || found_ty.is_functionally_equivalent_to(expected_ty, false)
            }
            (
                Ty::Array {
                    anonymous: true,
                    size: found_size,
                    sub_ty: found_ty,
                },
                Ty::Array {
                    size: expected_size,
                    sub_ty: expected_ty,
                    ..
                },
            ) => {
                found_size == expected_size
                    && (found_ty.is_weak_replaceable_by(expected_ty)
                        || found_ty.is_functionally_equivalent_to(expected_ty, false))
            }
            (
                Ty::Array {
                    size: found_size,
                    sub_ty: found_ty,
                    ..
                },
                Ty::Array {
                    anonymous: expected_anon,
                    size: expected_size,
                    sub_ty: expected_ty,
                },
            ) => {
                !expected_anon
                    && found_size == expected_size
                    && found_ty.is_functionally_equivalent_to(expected_ty, false)
            }
            (_, expected) if expected.is_any_struct() => true,
            (
                Ty::Struct {
                    anonymous: false,
                    uid: found_uid,
                    ..
                },
                Ty::Struct {
                    anonymous: false,
                    uid: expected_uid,
                    ..
                },
            ) => found_uid == expected_uid,
            (
                Ty::Struct {
                    anonymous: true,
                    members: found_members,
                    ..
                },
                Ty::Struct {
                    members: expected_members,
                    ..
                },
            ) => {
                if found_members.len() != expected_members.len() {
                    return false;
                }

                let expected_members: FxHashMap<_, _> = expected_members.iter().copied().collect();

                for (name, found_ty) in found_members {
                    let Some(expected_ty) = expected_members.get(name) else {
                        return false;
                    };

                    if !found_ty.can_fit_into(expected_ty) {
                        return false;
                    }
                }

                let found_members: FxHashMap<_, _> = found_members.iter().copied().collect();

                for (name, _) in expected_members {
                    if !found_members.contains_key(&name) {
                        return false;
                    }
                }

                true
            }
            (
                Ty::Distinct { uid: found_uid, .. },
                Ty::Distinct {
                    uid: expected_uid, ..
                },
            ) => found_uid == expected_uid,
            (found, Ty::Distinct { sub_ty: ty, .. }) => found.can_fit_into(ty),
            (found, expected) => found.is_functionally_equivalent_to(expected, false),
        }
    }

    /// This is used for the `as` operator to see whether something can be casted into something else
    ///
    /// This only allows primitives to be casted to each other, or types that are already equal.
    pub(crate) fn can_cast_to(&self, cast_into: &Ty) -> bool {
        if self.can_fit_into(cast_into) {
            return true;
        }

        match (self, cast_into) {
            (
                Ty::Bool | Ty::IInt(_) | Ty::UInt(_) | Ty::Float(_) | Ty::Char,
                Ty::Bool | Ty::IInt(_) | Ty::UInt(_) | Ty::Float(_) | Ty::Char,
            ) => true,
            (Ty::Distinct { sub_ty: from, .. }, Ty::Distinct { sub_ty: to, .. }) => {
                from.can_cast_to(to)
            }
            (Ty::Distinct { sub_ty: from, .. }, to) => from.can_cast_to(to),
            (from, Ty::Distinct { sub_ty: to, .. }) => from.can_cast_to(to),
            (
                Ty::Pointer {
                    mutable: found_mutable,
                    sub_ty: found_sub_ty,
                },
                Ty::Pointer {
                    mutable: expected_mutable,
                    sub_ty: expected_sub_ty,
                },
            ) => {
                matches!(
                    (found_mutable, expected_mutable),
                    (true, _) | (false, false)
                ) && (found_sub_ty == expected_sub_ty
                    || **found_sub_ty == Ty::Any
                    || **expected_sub_ty == Ty::Any
                    || found_sub_ty.is_weak_replaceable_by(expected_sub_ty))
            }
            // string to and from ^any and ^char and ^u8
            (Ty::String, Ty::Pointer { sub_ty, .. }) | (Ty::Pointer { sub_ty, .. }, Ty::String) => {
                matches!(sub_ty.as_ref(), Ty::Any | Ty::Char | Ty::UInt(8))
            }
            // string to and from [_]char and [_]u8
            (Ty::String, Ty::Array { sub_ty, .. }) | (Ty::Array { sub_ty, .. }, Ty::String) => {
                matches!(sub_ty.as_ref(), Ty::Char | Ty::UInt(8))
            }
            // `[]any` acts like `^any`
            (Ty::Slice { sub_ty: from, .. }, Ty::Slice { sub_ty: to }) => {
                from == to
                    || **from == Ty::Any
                    || **to == Ty::Any
                    || from.is_weak_replaceable_by(to)
            }
            (Ty::Array { sub_ty: from, .. }, Ty::Slice { sub_ty: to })
            | (Ty::Slice { sub_ty: from }, Ty::Array { sub_ty: to, .. }) => from.can_cast_to(to),
            (
                Ty::Array {
                    size: found_size,
                    sub_ty: found_ty,
                    ..
                },
                Ty::Array {
                    size: expected_size,
                    sub_ty: expected_ty,
                    ..
                },
            ) => found_size == expected_size && found_ty.can_cast_to(expected_ty),
            (_, expected) if expected.is_any_struct() => true,
            (
                Ty::Struct {
                    members: found_members,
                    ..
                },
                Ty::Struct {
                    members: expected_members,
                    ..
                },
            ) => {
                if found_members.len() != expected_members.len() {
                    return false;
                }

                let expected_members: FxHashMap<_, _> = expected_members.iter().copied().collect();

                for (name, found_ty) in found_members {
                    let Some(expected_ty) = expected_members.get(name) else {
                        return false;
                    };

                    if !found_ty.can_cast_to(expected_ty) {
                        return false;
                    }
                }

                let found_members: FxHashMap<_, _> = found_members.iter().copied().collect();

                for (name, _) in expected_members {
                    if !found_members.contains_key(&name) {
                        return false;
                    }
                }

                true
            }
            _ => self.is_functionally_equivalent_to(cast_into, true) || cast_into.is_any_struct(),
        }
    }

    /// allows `distinct` types to have the same semantics as other types as long as the inner type matches
    pub(crate) fn has_semantics_of(&self, expected: &Ty) -> bool {
        match (self, expected) {
            (Ty::Distinct { sub_ty: ty, .. }, Ty::IInt(0) | Ty::UInt(0)) => {
                if ty.has_semantics_of(expected) {
                    return true;
                }
            }
            (Ty::Distinct { .. }, Ty::IInt(_) | Ty::UInt(_)) => return false,
            (
                Ty::Distinct { uid: found_uid, .. },
                Ty::Distinct {
                    uid: expected_uid, ..
                },
            ) => {
                if found_uid == expected_uid {
                    return true;
                }
            }
            (
                Ty::Distinct {
                    sub_ty: inner_ty, ..
                },
                expected,
            ) => {
                if inner_ty.has_semantics_of(expected) {
                    return true;
                }
            }
            _ => {}
        }

        self.can_fit_into(expected)
    }

    /// THIS IS NOT AN INDICATOR AS TO WHETHER OR NOT A TYPE CAN BE REPLACED BY ANOTHER
    /// USE `is_weak_replaceable_by` INSTEAD
    pub(crate) fn might_be_weak(&self) -> bool {
        match self {
            Ty::IInt(0) | Ty::UInt(0) | Ty::Float(0) => true,
            Ty::Array { sub_ty, .. } => sub_ty.might_be_weak(),
            Ty::Pointer { sub_ty, .. } => sub_ty.might_be_weak(),
            _ => false,
        }
    }

    pub(crate) fn is_weak_replaceable_by(&self, expected: &Ty) -> bool {
        // println!("  is_weak_type_replaceable({:?}, {:?})", found, expected);
        match (self, expected) {
            // weak signed to strong signed, or weak unsigned to strong unsigned
            (Ty::IInt(0), Ty::IInt(bit_width)) | (Ty::UInt(0), Ty::UInt(bit_width)) => {
                *bit_width != 0
            }
            // always accept a switch of unsigned to signed
            (Ty::UInt(0), Ty::IInt(_)) => true,
            // always accept a switch to float
            (Ty::IInt(0) | Ty::UInt(0), Ty::Float(_)) => true,
            // weak float to strong float
            (Ty::Float(0), Ty::Float(bit_width)) => *bit_width != 0,
            (
                Ty::Array {
                    anonymous: first_anon,
                    size: found_size,
                    sub_ty: found_sub_ty,
                },
                Ty::Array {
                    anonymous: second_anon,
                    size: expected_size,
                    sub_ty: expected_sub_ty,
                },
            ) => {
                (*first_anon || !second_anon)
                    && found_size == expected_size
                    && found_sub_ty.is_weak_replaceable_by(expected_sub_ty)
            }
            (
                Ty::Pointer {
                    mutable: found_mutable,
                    sub_ty: found_sub_ty,
                },
                Ty::Pointer {
                    mutable: expected_mutable,
                    sub_ty: expected_sub_ty,
                },
            ) => {
                matches!(
                    (found_mutable, expected_mutable),
                    (true, _) | (false, false)
                ) && found_sub_ty.is_weak_replaceable_by(expected_sub_ty)
            }
            (
                Ty::Struct {
                    anonymous: true, ..
                },
                Ty::Struct { .. },
            ) => !expected.is_any_struct() && self.can_fit_into(expected),
            (
                Ty::Distinct { uid: found_uid, .. },
                Ty::Distinct {
                    uid: expected_uid, ..
                },
            ) => found_uid == expected_uid,
            (found, Ty::Distinct { sub_ty: ty, .. }) => found.is_weak_replaceable_by(ty),
            _ => false,
        }
    }
}

pub trait InternTyExt {
    fn remove_distinct(self) -> Intern<Ty>;
}

impl InternTyExt for Intern<Ty> {
    #[inline]
    fn remove_distinct(self) -> Intern<Ty> {
        match self.as_ref() {
            Ty::Distinct { sub_ty, .. } => sub_ty.remove_distinct(),
            _ => self,
        }
    }
}

pub(crate) trait BinaryOutput {
    fn get_possible_output_ty(&self, first: &Ty, second: &Ty) -> Option<BinaryOutputTy>;
}

impl BinaryOutput for hir::BinaryOp {
    /// should check with `can_perform` before actually using the type emitted from this function
    fn get_possible_output_ty(&self, first: &Ty, second: &Ty) -> Option<BinaryOutputTy> {
        first.max(second).map(|max_ty| BinaryOutputTy {
            max_ty: max_ty.clone(),
            final_output_ty: match self {
                hir::BinaryOp::Add
                | hir::BinaryOp::Sub
                | hir::BinaryOp::Mul
                | hir::BinaryOp::Div
                | hir::BinaryOp::Mod
                | hir::BinaryOp::BAnd
                | hir::BinaryOp::BOr
                | hir::BinaryOp::Xor
                | hir::BinaryOp::LShift
                | hir::BinaryOp::RShift => max_ty,
                hir::BinaryOp::Lt
                | hir::BinaryOp::Gt
                | hir::BinaryOp::Le
                | hir::BinaryOp::Ge
                | hir::BinaryOp::Eq
                | hir::BinaryOp::Ne
                | hir::BinaryOp::LAnd
                | hir::BinaryOp::LOr => Ty::Bool,
            },
        })
    }
}

pub(crate) trait UnaryOutput {
    fn get_possible_output_ty(&self, input: Intern<Ty>) -> Intern<Ty>;
}

impl UnaryOutput for UnaryOp {
    fn get_possible_output_ty(&self, input: Intern<Ty>) -> Intern<Ty> {
        match self {
            hir::UnaryOp::Neg => match *input {
                Ty::UInt(bit_width) => Ty::IInt(bit_width).into(),
                _ => input,
            },
            hir::UnaryOp::Pos | hir::UnaryOp::BNot | hir::UnaryOp::LNot => input,
        }
    }
}

pub(crate) trait TypedOp {
    fn can_perform(&self, ty: &Ty) -> bool;

    fn default_ty(&self) -> Ty;
}

impl TypedOp for hir::BinaryOp {
    fn can_perform(&self, found: &Ty) -> bool {
        let expected: &[Ty] = match self {
            hir::BinaryOp::Add
            | hir::BinaryOp::Sub
            | hir::BinaryOp::Mul
            | hir::BinaryOp::Div
            | hir::BinaryOp::Xor => &[Ty::IInt(0), Ty::Float(0)],
            hir::BinaryOp::BAnd | hir::BinaryOp::BOr => &[Ty::IInt(0), Ty::Float(0), Ty::Bool],
            hir::BinaryOp::Mod | hir::BinaryOp::LShift | hir::BinaryOp::RShift => &[Ty::IInt(0)],
            hir::BinaryOp::Lt | hir::BinaryOp::Gt | hir::BinaryOp::Le | hir::BinaryOp::Ge => {
                &[Ty::IInt(0), Ty::Float(0)]
            }
            hir::BinaryOp::Eq | hir::BinaryOp::Ne => {
                &[Ty::Char, Ty::IInt(0), Ty::Float(0), Ty::Type]
            }
            hir::BinaryOp::LAnd | hir::BinaryOp::LOr => &[Ty::Bool],
        };

        expected
            .iter()
            .any(|expected| found.has_semantics_of(expected))
    }

    fn default_ty(&self) -> Ty {
        match self {
            hir::BinaryOp::Add
            | hir::BinaryOp::Sub
            | hir::BinaryOp::Mul
            | hir::BinaryOp::Div
            | hir::BinaryOp::BAnd
            | hir::BinaryOp::BOr
            | hir::BinaryOp::Xor => Ty::IInt(0),
            hir::BinaryOp::Mod | hir::BinaryOp::LShift | hir::BinaryOp::RShift => Ty::IInt(0),
            hir::BinaryOp::Lt
            | hir::BinaryOp::Gt
            | hir::BinaryOp::Le
            | hir::BinaryOp::Ge
            | hir::BinaryOp::Eq
            | hir::BinaryOp::Ne => Ty::Bool,
            hir::BinaryOp::LAnd | hir::BinaryOp::LOr => Ty::Bool,
        }
    }
}

impl TypedOp for hir::UnaryOp {
    fn can_perform(&self, found: &Ty) -> bool {
        let expected: &[Ty] = match self {
            hir::UnaryOp::Neg | hir::UnaryOp::Pos | hir::UnaryOp::BNot => {
                &[Ty::IInt(0), Ty::Float(0)]
            }
            hir::UnaryOp::LNot => &[Ty::Bool],
        };

        expected
            .iter()
            .any(|expected| found.has_semantics_of(expected))
    }

    fn default_ty(&self) -> Ty {
        match self {
            hir::UnaryOp::Neg | hir::UnaryOp::Pos | hir::UnaryOp::BNot => Ty::IInt(0),
            hir::UnaryOp::LNot => Ty::Bool,
        }
    }
}

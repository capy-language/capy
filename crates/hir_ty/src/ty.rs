use std::{cell::RefCell, sync::LazyLock};

use hir::{PrimitiveTy, UnaryOp};
use internment::Intern;
use rustc_hash::FxHashMap;

// map of enum uid's to enum types
//
// this has to be thread local because all the capy unit tests run in multiple threads,
// and the enum data will overwrite each other and cause errors.
//
// todo: there is probably a much, much cleaner way to do all this
// the only reason I do this is because `Ty::max` needs to convert a `Ty::Variant` back into
// its `Ty::Enum`, but this is impossible because they'd both contain references to each other.
thread_local! {
    static ENUM_MAP: RefCell<FxHashMap<u32, Intern<Ty>>> = RefCell::new(FxHashMap::default());
}

#[track_caller]
pub(crate) fn get_enum_from_uid(enum_uid: u32) -> Intern<Ty> {
    ENUM_MAP.with(|map| map.borrow()[&enum_uid])
}

#[track_caller]
pub(crate) fn set_enum_uid(enum_uid: u32, ty: Intern<Ty>) {
    let Ty::Enum { uid, .. } = ty.as_ref() else {
        panic!("passed in non-enum");
    };

    assert_eq!(enum_uid, *uid);

    ENUM_MAP.with(|map| {
        map.borrow_mut().insert(enum_uid, ty);
    });
}

// Some commonly used types, defined in LazyLocks so that `.into()` is only called once

/// i0 represents ANY signed integer type `{int}`
pub static I0: LazyLock<Intern<Ty>> = LazyLock::new(|| Ty::IInt(0).into());
pub static I8: LazyLock<Intern<Ty>> = LazyLock::new(|| Ty::IInt(8).into());
pub static I32: LazyLock<Intern<Ty>> = LazyLock::new(|| Ty::IInt(32).into());

/// u0 represents ANY unsigned integer type `{uint}`
pub static U0: LazyLock<Intern<Ty>> = LazyLock::new(|| Ty::UInt(0).into());
pub static U8: LazyLock<Intern<Ty>> = LazyLock::new(|| Ty::UInt(8).into());
pub static U32: LazyLock<Intern<Ty>> = LazyLock::new(|| Ty::UInt(32).into());
pub static USIZE: LazyLock<Intern<Ty>> = LazyLock::new(|| Ty::UInt(u8::MAX).into());

/// f0 represents ANY float type `{float}`
pub static F0: LazyLock<Intern<Ty>> = LazyLock::new(|| Ty::Float(0).into());
pub static F32: LazyLock<Intern<Ty>> = LazyLock::new(|| Ty::Float(32).into());
pub static F64: LazyLock<Intern<Ty>> = LazyLock::new(|| Ty::Float(64).into());

pub static BOOL: LazyLock<Intern<Ty>> = LazyLock::new(|| Ty::Bool.into());
pub static STRING: LazyLock<Intern<Ty>> = LazyLock::new(|| Ty::String.into());
pub static CHAR: LazyLock<Intern<Ty>> = LazyLock::new(|| Ty::Char.into());
pub static META_TYPE: LazyLock<Intern<Ty>> = LazyLock::new(|| Ty::Type.into());
pub static ANY: LazyLock<Intern<Ty>> = LazyLock::new(|| Ty::Any.into());
pub static VOID: LazyLock<Intern<Ty>> = LazyLock::new(|| Ty::Void.into());
pub static NO_EVAL: LazyLock<Intern<Ty>> = LazyLock::new(|| Ty::NoEval.into());

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
    // capy slices are always len before ptr
    // offset       field
    // --------     -----
    // 0            len
    // ptr_size     ptr
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
    // the any type is always typeid before rawptr
    // offset       field
    // --------     -----
    // 0            typeid
    // 4            {padding}
    // ptr_size     rawptr
    Any,
    RawPtr {
        mutable: bool,
    },
    RawSlice,
    File(hir::FileName),
    Function {
        param_tys: Vec<ParamTy>,
        return_ty: Intern<Ty>,
    },
    Struct {
        /// if anonymous is set to `true`, `uid` is useless
        anonymous: bool,
        fqn: Option<hir::Fqn>,
        uid: u32,
        members: Vec<MemberTy>,
    },
    Enum {
        fqn: Option<hir::Fqn>,
        uid: u32,
        /// this is always an array of `Ty::Variant`s
        variants: Vec<Intern<Ty>>,
    },
    /// An enum variant is very similar to a distinct type.
    /// the main difference is more strict autocasting rules,
    /// and more information in the type related to the enum
    /// (like the enum's fqn and the discriminant)
    Variant {
        enum_fqn: Option<hir::Fqn>,
        enum_uid: u32,
        variant_name: hir::Name,
        uid: u32,
        sub_ty: Intern<Ty>,
        discriminant: u64,
    },
    Void,
    /// only used for blocks that always break.
    /// kind of like a "noreturn" type.
    /// the block will never reach it's own end,
    /// but the blocks above it might reach theirs.
    ///
    /// I think there was a specific reason I didn't name it `noreturn`
    /// but I can't remember atm.
    NoEval,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MemberTy {
    /// members without names are filtered out in hir_ty
    /// because they don't matter for type checking.
    /// we can't do anything with them
    pub name: hir::Name,
    pub ty: Intern<Ty>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ParamTy {
    pub ty: Intern<Ty>,
    pub varargs: bool,
    /// This is used so that "Missing Arg" errors aren't reported for arguments that are
    /// impossible to detect
    pub impossible_to_differentiate: bool,
}

#[derive(Debug)]
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
            PrimitiveTy::RawPtr { mutable, .. } => Self::RawPtr { mutable },
            PrimitiveTy::RawSlice { .. } => Self::RawSlice,
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
            Ty::RawPtr { .. } => false,
            Ty::RawSlice => false,
            Ty::File(_) => false,
            Ty::Function { .. } => false,
            Ty::Struct { members, .. } => members
                .iter()
                .all(|MemberTy { ty, .. }| ty.has_default_value()),
            // todo: create an @(default) annotation that allows you to set a default variant
            Ty::Enum { .. } => false,
            Ty::Variant { sub_ty, .. } => sub_ty.has_default_value(),
            Ty::Void => true,
            Ty::NoEval => true,
        }
    }

    /// Returns the "absolute" type.
    /// If the type is distinct, it will return the true underlying type.
    /// If `unwrap_variants` is true, then this function will also return the
    /// underlying type of `Ty::Variant`s
    pub fn absolute_ty(&self) -> &Self {
        let mut curr_ty = self;

        loop {
            match curr_ty {
                Ty::Variant { sub_ty, .. } => curr_ty = sub_ty.absolute_ty(),
                Ty::Distinct { sub_ty, .. } => curr_ty = sub_ty.absolute_ty(),
                _ => return curr_ty,
            }
        }
    }

    /// If self is a struct, this returns the fields
    pub fn as_struct(&self) -> Option<Vec<MemberTy>> {
        match self.absolute_ty() {
            Ty::Struct { members, .. } => Some(members.clone()),
            _ => None,
        }
    }

    /// If self is a function, this returns the parameters and return type
    pub fn as_function(&self) -> Option<(Vec<ParamTy>, Intern<Ty>)> {
        match self.absolute_ty() {
            Ty::Function {
                param_tys: params,
                return_ty,
            } => Some((params.clone(), *return_ty)),
            _ => None,
        }
    }

    /// If self is a pointer, this returns the mutability and sub type
    pub fn as_pointer(&self) -> Option<(bool, Intern<Ty>)> {
        match self.absolute_ty() {
            Ty::Pointer { mutable, sub_ty } => Some((*mutable, *sub_ty)),
            _ => None,
        }
    }

    /// If self is an array, this returns the length and sub type
    pub fn as_array(&self) -> Option<(u64, Intern<Ty>)> {
        match self.absolute_ty() {
            Ty::Array { size, sub_ty, .. } => Some((*size, *sub_ty)),
            _ => None,
        }
    }

    /// If self is a slice, this returns the sub type
    pub fn as_slice(&self) -> Option<Intern<Ty>> {
        match self.absolute_ty() {
            Ty::Slice { sub_ty } => Some(*sub_ty),
            _ => None,
        }
    }

    pub fn is_any(&self) -> bool {
        matches!(self.absolute_ty(), Ty::Any)
    }

    pub fn is_raw(&self) -> bool {
        matches!(self.absolute_ty(), Ty::RawPtr { .. } | Ty::RawSlice)
    }

    pub fn is_aggregate(&self) -> bool {
        matches!(
            self.absolute_ty(),
            Ty::Struct { .. }
                | Ty::Enum { .. }
                | Ty::Array { .. }
                | Ty::Slice { .. }
                | Ty::RawSlice
                | Ty::Any
        )
    }

    pub fn is_array(&self) -> bool {
        matches!(self.absolute_ty(), Ty::Array { .. })
    }

    pub fn is_slice(&self) -> bool {
        matches!(self.absolute_ty(), Ty::Slice { .. })
    }

    pub fn is_pointer(&self) -> bool {
        matches!(self.absolute_ty(), Ty::Pointer { .. })
    }

    pub fn is_function(&self) -> bool {
        matches!(self.absolute_ty(), Ty::Function { .. })
    }

    pub fn is_struct(&self) -> bool {
        matches!(self.absolute_ty(), Ty::Struct { .. })
    }

    /// returns true if the type is zero-sized
    pub fn is_zero_sized(&self) -> bool {
        match self.absolute_ty() {
            Ty::NotYetResolved | Ty::Unknown => true,
            Ty::Void => true,
            Ty::File(_) => true,
            Ty::NoEval => true,
            Ty::Array { size, sub_ty, .. } => *size == 0 || sub_ty.is_zero_sized(),
            Ty::Struct { members, .. } => {
                members.is_empty() || members.iter().all(|MemberTy { ty, .. }| ty.is_zero_sized())
            }
            Ty::Distinct { sub_ty: ty, .. } => ty.is_zero_sized(),
            _ => false,
        }
    }

    pub fn is_void(&self) -> bool {
        matches!(self.absolute_ty(), Ty::Void)
    }

    pub fn is_int(&self) -> bool {
        matches!(self.absolute_ty(), Ty::IInt(_) | Ty::UInt(_))
    }

    pub fn is_float(&self) -> bool {
        matches!(self.absolute_ty(), Ty::Float(_))
    }

    /// returns true if the type is unknown, or contains unknown, or is an unknown array, etc.
    pub fn is_unknown(&self) -> bool {
        // todo: make this iterative like `Ty::absolute_ty()`
        match self {
            Ty::NotYetResolved => true,
            Ty::Unknown => true,
            Ty::Pointer { sub_ty, .. } => sub_ty.is_unknown(),
            Ty::Array { sub_ty, .. } => sub_ty.is_unknown(),
            Ty::Struct { members, .. } => members.iter().any(|MemberTy { ty, .. }| ty.is_unknown()),
            Ty::Distinct { sub_ty, .. } => sub_ty.is_unknown(),
            Ty::Function {
                param_tys,
                return_ty,
            } => param_tys.iter().any(|p| p.ty.is_unknown()) || return_ty.is_unknown(),
            _ => false,
        }
    }

    /// I wrote this so that anonymous structs with different uid's but identical fields are considered equal
    ///
    /// Returns true if the bytes of one type would perfectly fit into the bytes of another type
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
                    && first_params.iter().zip(second_params.iter()).all(
                        |(first_param, second_param)| {
                            first_param.varargs == second_param.varargs
                                && first_param.ty.is_equal_to(&second_param.ty)
                        },
                    )
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
                    && first_members
                        .iter()
                        .zip(second_members.iter())
                        .all(|(first, second)| {
                            first.name == second.name && first.ty.is_equal_to(&second.ty)
                        })
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
            (Ty::Enum { uid: first, .. }, Ty::Enum { uid: second, .. }) => first == second,
            (Ty::Variant { uid: first, .. }, Ty::Variant { uid: second, .. }) => first == second,
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
                    && first_members
                        .iter()
                        .zip(second_members.iter())
                        .all(|(first, second)| {
                            first.name == second.name
                                && first.ty.is_functionally_equivalent_to(&second.ty, two_way)
                        })
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
            (
                Ty::Variant {
                    enum_uid: first_enum_uid,
                    ..
                },
                Ty::Variant {
                    enum_uid: second_enum_uid,
                    ..
                },
            ) => {
                if first_enum_uid == second_enum_uid {
                    Some((*get_enum_from_uid(*first_enum_uid)).clone())
                } else {
                    None
                }
            }
            (Ty::Variant { enum_uid, .. }, Ty::Enum { uid, .. }) if enum_uid == uid => {
                Some(other.clone())
            }
            (Ty::Enum { uid, .. }, Ty::Variant { enum_uid, .. }) if enum_uid == uid => {
                Some(self.clone())
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
    pub fn can_fit_into(&self, expected: &Ty) -> bool {
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
                ) && found_ty.can_fit_into(expected_ty)
            }
            (
                Ty::Pointer {
                    mutable: found_mutable,
                    sub_ty: found_ty,
                },
                Ty::RawPtr {
                    mutable: expected_mutable,
                },
            ) => {
                matches!(
                    (found_mutable, expected_mutable),
                    (true, _) | (false, false)
                ) && !found_ty.might_be_weak()
            }
            (
                Ty::RawPtr {
                    mutable: found_mutable,
                },
                Ty::RawPtr {
                    mutable: expected_mutable,
                },
            ) => matches!(
                (found_mutable, expected_mutable),
                (true, _) | (false, false)
            ),
            (
                Ty::Slice { sub_ty: found_ty },
                Ty::Slice {
                    sub_ty: expected_ty,
                },
            ) => found_ty.can_fit_into(expected_ty),
            (Ty::Slice { sub_ty: found_ty }, Ty::RawSlice) => !found_ty.might_be_weak(),
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
            (_, Ty::Any) => true,
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

                let expected_members: FxHashMap<_, _> = expected_members
                    .iter()
                    .map(|MemberTy { name, ty }| (*name, *ty))
                    .collect();

                for MemberTy { name, ty: found_ty } in found_members {
                    let Some(expected_ty) = expected_members.get(name) else {
                        return false;
                    };

                    if !found_ty.can_fit_into(expected_ty) {
                        return false;
                    }
                }

                let found_members: FxHashMap<_, _> = found_members
                    .iter()
                    .map(|MemberTy { name, ty }| (*name, *ty))
                    .collect();

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
            (
                Ty::Variant { uid: found_uid, .. },
                Ty::Variant {
                    uid: expected_uid, ..
                },
            ) => found_uid == expected_uid,
            (Ty::Variant { enum_uid, .. }, Ty::Enum { uid, .. }) => enum_uid == uid,
            (found, expected) => found.is_functionally_equivalent_to(expected, false),
        }
    }

    pub(crate) fn can_differentiate(&self, other: &Ty) -> bool {
        match (self, other) {
            (Ty::Unknown, _) | (_, Ty::Unknown) => true,
            (
                Ty::IInt(_) | Ty::UInt(_) | Ty::Float(_),
                Ty::IInt(_) | Ty::UInt(_) | Ty::Float(_),
            ) => false,
            (
                Ty::Pointer {
                    sub_ty: left_ty, ..
                },
                Ty::Pointer {
                    sub_ty: right_ty, ..
                },
            ) => left_ty.can_differentiate(right_ty),
            (Ty::Pointer { .. }, Ty::RawPtr { .. }) | (Ty::RawPtr { .. }, Ty::Pointer { .. }) => {
                false
            }
            (Ty::RawPtr { .. }, Ty::RawPtr { .. }) => false,
            (Ty::Slice { sub_ty: left_ty }, Ty::Slice { sub_ty: right_ty }) => {
                left_ty.can_differentiate(right_ty)
            }
            (Ty::Slice { .. }, Ty::RawSlice) | (Ty::RawPtr { .. }, Ty::Slice { .. }) => false,
            (
                Ty::Array {
                    sub_ty: left_ty, ..
                },
                Ty::Slice { sub_ty: right_ty },
            )
            | (
                Ty::Slice { sub_ty: left_ty },
                Ty::Array {
                    sub_ty: right_ty, ..
                },
            ) => {
                // this is perhaps much more strict than `can_fit_into`
                left_ty.can_differentiate(right_ty)
            }
            (
                Ty::Array {
                    size: left_size,
                    sub_ty: left_ty,
                    ..
                },
                Ty::Array {
                    size: right_size,
                    sub_ty: right_ty,
                    ..
                },
            ) => left_size != right_size || left_ty.can_differentiate(right_ty),
            (_, Ty::Any) | (Ty::Any, _) => false,
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
            ) => found_uid != expected_uid,
            (
                Ty::Struct {
                    anonymous: left_anon,
                    members: left_members,
                    ..
                },
                Ty::Struct {
                    anonymous: right_anon,
                    members: right_members,
                    ..
                },
            ) => {
                assert!(*left_anon || *right_anon);

                if left_members.len() != right_members.len() {
                    return true;
                }

                let right_members: FxHashMap<_, _> = right_members
                    .iter()
                    .map(|MemberTy { name, ty }| (*name, *ty))
                    .collect();

                for MemberTy { name, ty: left_ty } in left_members {
                    let Some(right_ty) = right_members.get(name) else {
                        return true;
                    };

                    if !left_ty.can_differentiate(right_ty) {
                        return true;
                    }
                }

                let left_members: FxHashMap<_, _> = left_members
                    .iter()
                    .map(|MemberTy { name, ty }| (*name, *ty))
                    .collect();

                for (name, _) in right_members {
                    if !left_members.contains_key(&name) {
                        return true;
                    }
                }

                false
            }
            (Ty::Distinct { uid: left_uid, .. }, Ty::Distinct { uid: right_uid, .. }) => {
                left_uid != right_uid
            }
            (other, Ty::Distinct { sub_ty, .. }) | (Ty::Distinct { sub_ty, .. }, other) => {
                other.can_differentiate(sub_ty)
            }
            (Ty::Variant { uid: left_uid, .. }, Ty::Variant { uid: right_uid, .. }) => {
                left_uid != right_uid
            }
            (Ty::Variant { enum_uid, .. }, Ty::Enum { uid, .. }) => enum_uid != uid,
            _ => !(self.can_fit_into(other) || other.can_fit_into(self)),
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

            // distincts
            (Ty::Distinct { sub_ty: from, .. }, Ty::Distinct { sub_ty: to, .. }) => {
                from.can_cast_to(to)
            }
            (Ty::Distinct { sub_ty: from, .. }, to) => from.can_cast_to(to),
            (from, Ty::Distinct { sub_ty: to, .. }) => from.can_cast_to(to),

            // variants
            (Ty::Variant { sub_ty: from, .. }, Ty::Variant { sub_ty: to, .. }) => {
                from.can_cast_to(to)
            }
            (Ty::Variant { sub_ty: from, .. }, to) => from.can_cast_to(to),
            (from, Ty::Variant { sub_ty: to, .. }) => from.can_cast_to(to),

            // pointers
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
                    || found_sub_ty.is_weak_replaceable_by(expected_sub_ty))
            }
            // raw pointer casts just need to maintain mutability
            (
                Ty::Pointer {
                    mutable: found_mutable,
                    sub_ty: _,
                },
                Ty::RawPtr {
                    mutable: expected_mutable,
                },
            )
            | (
                Ty::RawPtr {
                    mutable: found_mutable,
                },
                Ty::Pointer {
                    mutable: expected_mutable,
                    sub_ty: _,
                },
            )
            | (
                Ty::RawPtr {
                    mutable: found_mutable,
                },
                Ty::RawPtr {
                    mutable: expected_mutable,
                },
            ) => {
                matches!(
                    (found_mutable, expected_mutable),
                    (true, _) | (false, false)
                )
            }
            // string to and from ^char and ^u8
            (
                Ty::String,
                Ty::Pointer {
                    sub_ty,
                    mutable: false,
                },
            )
            | (
                Ty::Pointer {
                    sub_ty,
                    mutable: false,
                },
                Ty::String,
            ) => {
                matches!(sub_ty.as_ref(), Ty::Char | Ty::UInt(8))
            }
            // string to and from rawptr
            (Ty::String, Ty::RawPtr { mutable: false })
            | (Ty::RawPtr { mutable: false }, Ty::String) => true,
            // string to and from [_]char and [_]u8
            (Ty::String, Ty::Array { sub_ty, .. }) | (Ty::Array { sub_ty, .. }, Ty::String) => {
                matches!(sub_ty.as_ref(), Ty::Char | Ty::UInt(8))
            }

            (Ty::Slice { sub_ty: from, .. }, Ty::Slice { sub_ty: to }) => {
                from == to || from.is_weak_replaceable_by(to)
            }
            // `rawslice` casts are pretty much the same as `rawptr` casts
            (Ty::Slice { .. }, Ty::RawSlice)
            | (Ty::RawSlice, Ty::Slice { .. })
            | (Ty::RawSlice, Ty::RawSlice) => true,

            (Ty::Array { sub_ty: from, .. }, Ty::Slice { sub_ty: to })
            | (Ty::Slice { sub_ty: from }, Ty::Array { sub_ty: to, .. }) => from.can_cast_to(to),
            // TODO: maybe allow array -> rawslice
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

            (found, Ty::Any) => !found.might_be_weak(),

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

                let expected_members: FxHashMap<_, _> = expected_members
                    .iter()
                    .map(|MemberTy { name, ty }| (*name, *ty))
                    .collect();

                for MemberTy { name, ty: found_ty } in found_members {
                    let Some(expected_ty) = expected_members.get(name) else {
                        return false;
                    };

                    if !found_ty.can_cast_to(expected_ty) {
                        return false;
                    }
                }

                let found_members: FxHashMap<_, _> = found_members
                    .iter()
                    .map(|MemberTy { name, ty }| (*name, *ty))
                    .collect();

                for (name, _) in expected_members {
                    if !found_members.contains_key(&name) {
                        return false;
                    }
                }

                true
            }
            _ => self.is_functionally_equivalent_to(cast_into, true),
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

    /// JUST BECAUSE THIS FUNCTION RETURNS TRUE, THAT DOES NOT MEAN THAT THIS TYPE IS *ACTUALLY*
    /// WEAK TYPE REPLACEABLE BY ANOTHER OTHER TYPE
    ///
    /// USE `is_weak_replaceable_by` INSTEAD IF YOU NEED THAT
    pub(crate) fn might_be_weak(&self) -> bool {
        match self {
            Ty::IInt(0) | Ty::UInt(0) | Ty::Float(0) => true,
            Ty::Array { sub_ty, .. } => sub_ty.might_be_weak(),
            // todo: is this slice branch needed? i just added it because i thought it was missing
            Ty::Slice { sub_ty, .. } => sub_ty.might_be_weak(),
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
                    anonymous: true,
                    size: found_size,
                    sub_ty: found_sub_ty,
                },
                Ty::Array {
                    anonymous: false,
                    size: expected_size,
                    sub_ty: expected_sub_ty,
                },
            ) => {
                found_size == expected_size
                    && (found_sub_ty.is_weak_replaceable_by(expected_sub_ty)
                        || found_sub_ty.is_equal_to(expected_sub_ty))
            }
            (
                Ty::Array {
                    anonymous: true,
                    size: _,
                    sub_ty: found_sub_ty,
                },
                Ty::Slice {
                    sub_ty: expected_sub_ty,
                },
            ) => {
                found_sub_ty.is_weak_replaceable_by(expected_sub_ty)
                    || found_sub_ty.is_equal_to(expected_sub_ty)
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
            ) => self.can_fit_into(expected),
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
    fn absolute_intern_ty(self, unwrap_variants: bool) -> Intern<Ty>;
}

impl InternTyExt for Intern<Ty> {
    /// The same as `Ty::absolute_ty` except that it returns `Intern<Ty>`
    fn absolute_intern_ty(self, unwrap_variants: bool) -> Intern<Ty> {
        let mut curr_ty = self;

        loop {
            match curr_ty.as_ref() {
                Ty::Variant { sub_ty, .. } if unwrap_variants => {
                    curr_ty = sub_ty.absolute_intern_ty(unwrap_variants)
                }
                Ty::Distinct { sub_ty, .. } => curr_ty = sub_ty.absolute_intern_ty(unwrap_variants),
                _ => return curr_ty,
            }
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
        match self {
            hir::BinaryOp::Add
            | hir::BinaryOp::Sub
            | hir::BinaryOp::Mul
            | hir::BinaryOp::Div
            | hir::BinaryOp::Xor => matches!(
                found.absolute_ty(),
                Ty::IInt(_) | Ty::UInt(_) | Ty::Float(_)
            ),
            hir::BinaryOp::BAnd | hir::BinaryOp::BOr => matches!(
                found.absolute_ty(),
                Ty::IInt(_) | Ty::UInt(_) | Ty::Float(_) | Ty::Bool
            ),
            hir::BinaryOp::Mod | hir::BinaryOp::LShift | hir::BinaryOp::RShift => {
                matches!(found.absolute_ty(), Ty::IInt(_) | Ty::UInt(_))
            }
            hir::BinaryOp::Lt | hir::BinaryOp::Gt | hir::BinaryOp::Le | hir::BinaryOp::Ge => {
                matches!(
                    found.absolute_ty(),
                    Ty::IInt(_) | Ty::UInt(_) | Ty::Float(_) | Ty::Bool
                )
            }
            hir::BinaryOp::Eq | hir::BinaryOp::Ne => {
                // TODO: allow comparing aggregates
                // todo: make sure this is consistent with codegen
                !matches!(
                    found.absolute_ty(),
                    Ty::String | Ty::Slice { .. } | Ty::Pointer { .. }
                ) && !found.is_aggregate()
            }
            hir::BinaryOp::LAnd | hir::BinaryOp::LOr => *found.absolute_ty() == Ty::Bool,
        }
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

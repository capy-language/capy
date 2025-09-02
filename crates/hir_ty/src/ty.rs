use std::{cell::RefCell, collections::hash_map, fmt::Display};

use hir::{PrimitiveTy, UnaryOp};
use interner::Interner;
use internment::Intern;
use itertools::Itertools;
use rustc_hash::FxHashMap;

thread_local! {
    // enum uid's to enum types
    //
    // this has to be thread local because all the capy unit tests run in multiple threads,
    // and the enum data will overwrite each other and cause errors.
    //
    // todo: there is probably a much, much cleaner way to do all this
    // the only reason I do this is because `Ty::max` needs to convert a `Ty::Variant` back into
    // its `Ty::Enum`, but this is impossible because they'd both contain references to each other,
    // and it'd be a chicken and egg situation.
    pub static ENUM_MAP: RefCell<FxHashMap<u32, Intern<Ty>>> = RefCell::new(FxHashMap::default());

    pub static TYPE_NAMES: RefCell<FxHashMap<Intern<Ty>, TyName>> = RefCell::new(FxHashMap::default());
}

#[track_caller]
pub(crate) fn get_enum_from_uid(enum_uid: u32) -> Intern<Ty> {
    ENUM_MAP
        .with_borrow(|map| map.get(&enum_uid).copied())
        .unwrap()
}

#[track_caller]
pub(crate) fn set_enum_uid(enum_uid: u32, ty: Intern<Ty>) {
    let Ty::Enum { uid, .. } = ty.as_ref() else {
        panic!("passed in non-enum");
    };

    assert_eq!(enum_uid, *uid);

    ENUM_MAP.with_borrow_mut(|map| map.insert(enum_uid, ty));
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TyName {
    Global(hir::Fqn),
    Local(hir::Name),
}

#[cfg(test)]
pub(crate) fn get_all_named_types() -> Vec<Intern<Ty>> {
    TYPE_NAMES.with(|map| map.borrow().keys().copied().collect_vec())
}

pub(crate) fn get_type_name(ty: Intern<Ty>) -> Option<TyName> {
    if !ty.can_have_a_name() {
        return None;
    }

    TYPE_NAMES.with(|map| map.borrow().get(&ty).copied())
}

#[track_caller]
pub(crate) fn set_type_name(ty: Intern<Ty>, name: TyName) {
    assert!(ty.can_have_a_name(), "{ty:?} is not allowed to have a name");

    TYPE_NAMES.with(|map| match map.borrow_mut().entry(ty) {
        hash_map::Entry::Occupied(mut occupied_entry) => {
            if matches!(occupied_entry.get(), TyName::Local(_)) && matches!(name, TyName::Global(_))
            {
                occupied_entry.insert(name);
            }
        }
        hash_map::Entry::Vacant(vacant_entry) => {
            vacant_entry.insert(name);
        }
    });
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    AnonArray {
        size: u64,
        sub_ty: Intern<Ty>,
    },
    ConcreteArray {
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
    AnonStruct {
        members: Vec<MemberTy>,
    },
    ConcreteStruct {
        uid: u32,
        members: Vec<MemberTy>,
    },
    Enum {
        uid: u32,
        /// this is always an array of `Ty::Variant`s
        variants: Vec<Intern<Ty>>,
    },
    /// An enum variant is very similar to a distinct type.
    /// the main difference is more strict autocasting rules,
    /// and more information in the type related to the enum
    /// (like the enum's fqn and the discriminant)
    EnumVariant {
        enum_uid: u32,
        variant_name: hir::Name,
        uid: u32,
        sub_ty: Intern<Ty>,
        discriminant: u64,
    },
    Nil,
    Optional {
        sub_ty: Intern<Ty>,
    },
    ErrorUnion {
        // todo: make error_ty an option and implement inferred error unions
        error_ty: Intern<Ty>,
        payload_ty: Intern<Ty>,
    },
    Void,
    /// Used for blocks that always break.
    /// The block will never reach it's own end,
    /// but the blocks above it might reach theirs.
    ///
    /// This can't be used for a `noreturn` type because this type is currently used by codegen so
    /// it knows when it has to stop making instructions, but that doesn't really work for e.g.
    /// function calls that return `Ty::AlwaysJumps`, because they actually *do* need a
    /// finishing instruction after them.
    AlwaysJumps,
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
            Ty::AnonArray { sub_ty, .. } | Ty::ConcreteArray { sub_ty, .. } => {
                sub_ty.has_default_value()
            }
            Ty::Slice { .. } => false,
            Ty::Pointer { .. } => false,
            Ty::Distinct { sub_ty, .. } => sub_ty.has_default_value(),
            Ty::Type => false,
            Ty::Any => false,
            Ty::RawPtr { .. } => false,
            Ty::RawSlice => false,
            Ty::File(_) => false,
            Ty::Function { .. } => false,
            Ty::AnonStruct { members } | Ty::ConcreteStruct { members, .. } => members
                .iter()
                .all(|MemberTy { ty, .. }| ty.has_default_value()),
            // todo: create an @(default) annotation that allows you to set a default variant
            Ty::Enum { .. } => false,
            Ty::EnumVariant { sub_ty, .. } => sub_ty.has_default_value(),
            Ty::Nil => true,
            Ty::Optional { .. } => true,
            Ty::ErrorUnion { .. } => false,
            Ty::Void => true,
            Ty::AlwaysJumps => true,
        }
    }

    /// Returns the "absolute" type.
    /// If the type is distinct, it will return the true underlying type.
    pub fn absolute_ty(&self) -> &Self {
        let mut curr_ty = self;

        loop {
            match curr_ty {
                Ty::EnumVariant { sub_ty, .. } => curr_ty = sub_ty,
                Ty::Distinct { sub_ty, .. } => curr_ty = sub_ty,
                _ => return curr_ty,
            }
        }
    }

    pub fn absolute_ty_keep_variants(&self) -> &Self {
        let mut curr_ty = self;

        loop {
            match curr_ty {
                Ty::Distinct { sub_ty, .. } => curr_ty = sub_ty,
                _ => return curr_ty,
            }
        }
    }

    // if self is a result union or optional, gets the error/nil type
    pub fn propagated_ty(&self) -> Option<Intern<Ty>> {
        match self.absolute_ty() {
            Ty::Optional { .. } => Some(Ty::Nil.into()),
            Ty::ErrorUnion { error_ty, .. } => Some(*error_ty),
            _ => None,
        }
    }

    /// If self is a struct, this returns the fields
    pub fn as_struct(&self) -> Option<Vec<MemberTy>> {
        match self.absolute_ty() {
            Ty::AnonStruct { members } | Ty::ConcreteStruct { members, .. } => {
                Some(members.clone())
            }
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
            Ty::AnonArray { size, sub_ty } | Ty::ConcreteArray { size, sub_ty, .. } => {
                Some((*size, *sub_ty))
            }
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

    // Note that `?u64` is an aggregate type but `?^u64` isn't
    pub fn is_aggregate(&self) -> bool {
        match self.absolute_ty() {
            Ty::ConcreteStruct { .. }
            | Ty::AnonStruct { .. }
            | Ty::Enum { .. }
            | Ty::ErrorUnion { .. }
            | Ty::ConcreteArray { .. }
            | Ty::AnonArray { .. }
            | Ty::Slice { .. }
            | Ty::RawSlice
            | Ty::Any => true,
            Ty::Optional { sub_ty } => !sub_ty.is_non_zero(),
            _ => false,
        }
    }

    pub fn can_have_a_name(&self) -> bool {
        matches!(
            self,
            Ty::Distinct { .. } | Ty::ConcreteStruct { .. } | Ty::Enum { .. }
        )
    }

    pub fn is_array(&self) -> bool {
        matches!(
            self.absolute_ty(),
            Ty::AnonArray { .. } | Ty::ConcreteArray { .. }
        )
    }

    pub fn is_slice(&self) -> bool {
        matches!(self.absolute_ty(), Ty::Slice { .. } | Ty::RawSlice)
    }

    pub fn is_pointer(&self) -> bool {
        matches!(self.absolute_ty(), Ty::Pointer { .. } | Ty::RawPtr { .. })
    }

    pub fn is_function(&self) -> bool {
        matches!(self.absolute_ty(), Ty::Function { .. })
    }

    pub fn is_struct(&self) -> bool {
        matches!(
            self.absolute_ty(),
            Ty::AnonStruct { .. } | Ty::ConcreteStruct { .. }
        )
    }

    // todo: should distinct nil's be allowed to transform into optionals?
    pub fn is_nil(&self) -> bool {
        matches!(self.absolute_ty(), Ty::Nil)
    }

    pub fn is_optional(&self) -> bool {
        matches!(self.absolute_ty(), Ty::Optional { .. })
    }

    pub fn is_error_union(&self) -> bool {
        matches!(self.absolute_ty(), Ty::ErrorUnion { .. })
    }

    pub fn is_enum(&self) -> bool {
        matches!(self.absolute_ty(), Ty::Enum { .. })
    }

    /// Note: `ty.is_sum_ty()==true` does not imply `ty.is_tagged_union()==true`
    pub fn is_sum_ty(&self) -> bool {
        matches!(
            self.absolute_ty(),
            Ty::Enum { .. } | Ty::ErrorUnion { .. } | Ty::Optional { .. }
        )
    }

    /// This returns true if the internal representation of a type is a tagged union
    ///
    /// This might be false for `?^bool`, because that will get compiled to a nullable pointer
    pub fn is_tagged_union(&self) -> bool {
        match self.absolute_ty() {
            Ty::Enum { .. } | Ty::ErrorUnion { .. } => true,
            Ty::Optional { sub_ty } => !sub_ty.is_non_zero(),
            _ => false,
        }
    }

    // For nullable optionals (optionals of non-zero types), this returns None
    pub fn get_tagged_union_discrim(&self, variant: &Ty) -> Option<u64> {
        match (self.absolute_ty(), variant) {
            (Ty::Optional { sub_ty }, Ty::Nil) if !sub_ty.is_non_zero() => Some(0),
            (Ty::Optional { sub_ty }, _) if !sub_ty.is_non_zero() => {
                assert!(**sub_ty == *variant);
                Some(1)
            }
            (Ty::ErrorUnion { error_ty, .. }, _) if *variant == **error_ty => Some(0),
            (Ty::ErrorUnion { payload_ty, .. }, _) if *variant == **payload_ty => Some(1),
            (Ty::ErrorUnion { .. }, _) => panic!("{variant:?} is not a variant of {self:?}"),
            (
                Ty::Enum { uid, .. },
                Ty::EnumVariant {
                    enum_uid,
                    discriminant,
                    ..
                },
            ) => {
                assert_eq!(uid, enum_uid);
                Some(*discriminant)
            }
            (Ty::Enum { .. }, _) => panic!("{variant:?} is not a variant of {self:?}"),
            _ => None,
        }
    }

    /// For union types (optionals, error unions, and enums) this returns every possible "type"
    /// which the sum type might represent.
    ///
    /// E.g.
    /// `?i32` => [i32, nil]
    /// `str!u64` => [str, u64]
    /// `enum { Dog, Cat }` => [Dog, Cat]
    ///
    /// Non-sum types always return false
    pub fn has_sum_variant(&self, possible_variant: &Ty) -> bool {
        match self.absolute_ty() {
            Ty::Optional { sub_ty } => {
                // todo: should this be `is_nil`? what happens to distinct types?
                *possible_variant == **sub_ty || possible_variant.is_nil()
            }
            Ty::ErrorUnion {
                error_ty,
                payload_ty,
            } => *possible_variant == **error_ty || *possible_variant == **payload_ty,
            Ty::Enum { variants, .. } => variants.iter().any(|v| **v == *possible_variant),
            _ => false,
        }
    }

    /// the type can NEVER have the value zero.
    ///
    /// used by optionals to allow things like `?^i32` to just be a nullable pointer
    pub fn is_non_zero(&self) -> bool {
        self.is_pointer()
    }

    /// zero-sized types should compile to nothing.
    pub fn is_zero_sized(&self) -> bool {
        match self.absolute_ty() {
            Ty::NotYetResolved | Ty::Unknown => true,
            Ty::Void => true,
            Ty::Nil => true,
            Ty::File(_) => true,
            Ty::AlwaysJumps => true,
            Ty::ConcreteArray { size, sub_ty, .. } => *size == 0 || sub_ty.is_zero_sized(),
            // todo: a zero-sized struct will produce a nullable aggregate optional
            // currently the code expects only nullable non-aggregate optionals
            Ty::ConcreteStruct { members, .. } => {
                members.is_empty() || members.iter().all(|MemberTy { ty, .. }| ty.is_zero_sized())
            }
            Ty::Distinct { sub_ty, .. } => sub_ty.is_zero_sized(),
            _ => false,
        }
    }

    pub fn is_void(&self) -> bool {
        matches!(self.absolute_ty(), Ty::Void)
    }

    /// This might be useful in detecting if a type *needs* an explicit value to be instanced.
    ///
    /// E.g.
    /// ```text
    /// my_block : void = {
    ///     core.println("Hello!");
    /// };
    /// ```
    ///
    /// In the above example, we don't supply a tail expression for `void` but the block still
    /// works because `void` can be created from nothing.
    ///
    /// ```text
    /// my_block : ?void = {
    ///     core.println("Hello!");
    /// };
    /// ```
    ///
    /// This one is slightly less obvious but has the same principle.
    /// `?void` can be formed from a `void` and `void` doesn't require an explicit value to be
    /// instanced.
    ///
    /// todo: make sure this doesn't get activated for Ty::Any
    pub fn can_be_created_from_nothing(&self) -> bool {
        match self.absolute_ty() {
            Ty::Void => true,
            // this uses `max` and `can_fit_into` because the Block type checking code uses
            // `expect_block_match` with `Ty::Void`, which internally uses those two
            //
            // todo: is this a good way to do it?
            other => Ty::Void.max(other).is_some() || Ty::Void.can_fit_into(other),
        }
    }

    pub fn is_int(&self) -> bool {
        matches!(self.absolute_ty(), Ty::IInt(_) | Ty::UInt(_))
    }

    pub fn is_float(&self) -> bool {
        matches!(self.absolute_ty(), Ty::Float(_))
    }

    /// Note that unlike the other `is_*` functions, this does not get the absolute type
    pub fn is_distinct(&self) -> bool {
        matches!(self, Ty::Distinct { .. })
    }

    /// returns true if the type is unknown, or contains unknown, or is an unknown array, etc.
    pub fn is_unknown(&self) -> bool {
        // todo: maybe make this a small vec
        let mut to_check = vec![self];

        loop {
            let Some(next_ty) = to_check.pop() else {
                return false;
            };

            match next_ty {
                Ty::NotYetResolved => return true,
                Ty::Unknown => return true,
                Ty::Pointer { sub_ty, .. } => to_check.push(sub_ty),
                Ty::ConcreteArray { sub_ty, .. } => to_check.push(sub_ty),
                Ty::ConcreteStruct { members, .. } => {
                    to_check.extend(members.iter().map(|MemberTy { ty, .. }| &**ty));
                }
                Ty::Distinct { sub_ty, .. } => to_check.push(sub_ty),
                Ty::EnumVariant { sub_ty, .. } => to_check.push(sub_ty),
                Ty::Function {
                    param_tys,
                    return_ty,
                } => {
                    to_check.extend(param_tys.iter().map(|ParamTy { ty, .. }| &**ty));
                    to_check.push(return_ty);
                }
                _ => {}
            }
        }
    }

    /// An equality check that ignores distinct types and anonymity.
    /// All other types must be exactly equal (i32 == i32, i32 != i64)
    ///
    /// if `self_can_lose_distinction` is false, &self=distinct will maintain its distinction and
    /// will return false when compared to other=<its own inner value>
    ///
    /// setting `self_can_lose_distinction=true` is recommended if you're just trying to see that
    /// the types are equivalent.
    ///
    /// This function guarentees that if `A` is functionally equivalent to `B`,
    /// then the bytes that make up `A` are also valid bytes for `B`
    pub fn is_functionally_equivalent_to(
        &self,
        other: &Self,
        self_can_lose_distinction: bool,
    ) -> bool {
        match (self, other) {
            (
                Ty::ConcreteArray {
                    size: first_size,
                    sub_ty: first_sub_ty,
                }
                | Ty::AnonArray {
                    size: first_size,
                    sub_ty: first_sub_ty,
                },
                Ty::ConcreteArray {
                    size: second_size,
                    sub_ty: second_sub_ty,
                }
                | Ty::AnonArray {
                    size: second_size,
                    sub_ty: second_sub_ty,
                },
            ) => {
                first_size == second_size
                    && first_sub_ty
                        .is_functionally_equivalent_to(second_sub_ty, self_can_lose_distinction)
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
                    && first_sub_ty
                        .is_functionally_equivalent_to(second_sub_ty, self_can_lose_distinction)
            }
            (
                Ty::Slice {
                    sub_ty: first_sub_ty,
                },
                Ty::Slice {
                    sub_ty: second_sub_ty,
                },
            ) => {
                first_sub_ty.is_functionally_equivalent_to(second_sub_ty, self_can_lose_distinction)
            }
            (Ty::Distinct { sub_ty: first, .. }, Ty::Distinct { sub_ty: second, .. }) => {
                first.is_functionally_equivalent_to(second, self_can_lose_distinction)
            }
            (
                Ty::Distinct {
                    sub_ty: distinct_inner,
                    ..
                },
                other,
            ) => {
                self_can_lose_distinction
                    && distinct_inner
                        .is_functionally_equivalent_to(other, self_can_lose_distinction)
            }
            (
                other,
                Ty::Distinct {
                    sub_ty: distinct_inner,
                    ..
                },
            ) => {
                // println!("  {:?} as {:?}", other, resolved_arena[distinct]);
                other.is_functionally_equivalent_to(distinct_inner, self_can_lose_distinction)
            }
            (Ty::EnumVariant { sub_ty: first, .. }, Ty::EnumVariant { sub_ty: second, .. }) => {
                first.is_functionally_equivalent_to(second, self_can_lose_distinction)
            }
            (
                Ty::EnumVariant {
                    sub_ty: variant_inner,
                    ..
                },
                other,
            ) => {
                self_can_lose_distinction
                    && variant_inner.is_functionally_equivalent_to(other, self_can_lose_distinction)
            }
            (
                other,
                Ty::EnumVariant {
                    sub_ty: variant_inner,
                    ..
                },
            ) => {
                // println!("  {:?} as {:?}", other, resolved_arena[distinct]);
                other.is_functionally_equivalent_to(variant_inner, self_can_lose_distinction)
            }
            (
                Ty::ConcreteStruct {
                    members: first_members,
                    ..
                }
                | Ty::AnonStruct {
                    members: first_members,
                },
                Ty::ConcreteStruct {
                    members: second_members,
                    ..
                }
                | Ty::AnonStruct {
                    members: second_members,
                },
            ) => {
                first_members.len() == second_members.len()
                    && first_members
                        .iter()
                        .zip_eq(second_members.iter())
                        .all(|(first, second)| {
                            first.name == second.name
                                && first.ty.is_functionally_equivalent_to(
                                    &second.ty,
                                    self_can_lose_distinction,
                                )
                        })
            }
            (Ty::Optional { sub_ty: first }, Ty::Optional { sub_ty: second }) => {
                first.is_functionally_equivalent_to(second, self_can_lose_distinction)
            }
            (
                Ty::ErrorUnion {
                    error_ty: first_error_ty,
                    payload_ty: first_payload_ty,
                },
                Ty::ErrorUnion {
                    error_ty: second_error_ty,
                    payload_ty: second_payload_ty,
                },
            ) => {
                first_error_ty
                    .is_functionally_equivalent_to(second_error_ty, self_can_lose_distinction)
                    && first_payload_ty
                        .is_functionally_equivalent_to(second_payload_ty, self_can_lose_distinction)
            }
            (first, second) => first == second,
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
    pub fn max(&self, other: &Ty) -> Option<Ty> {
        if self == other {
            return Some(self.clone());
        }

        match (self, other) {
            // numbers
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
            // distincts
            (non_distinct, Ty::Distinct { .. }) => {
                assert_eq!(self, non_distinct);
                if other.has_semantics_of(self) {
                    Some(other.clone())
                } else {
                    None
                }
            }
            (Ty::Distinct { .. }, non_distinct) => {
                assert_eq!(other, non_distinct);
                if self.has_semantics_of(non_distinct) {
                    Some(self.clone())
                } else {
                    None
                }
            }
            // enums
            (
                Ty::EnumVariant {
                    enum_uid: first_enum_uid,
                    ..
                },
                Ty::EnumVariant {
                    enum_uid: second_enum_uid,
                    ..
                },
            ) => {
                if first_enum_uid == second_enum_uid {
                    Some((*get_enum_from_uid(*first_enum_uid)).clone())
                } else if self.is_zero_sized() && other.is_zero_sized() {
                    // todo: should this be explicit?
                    Some(Ty::Type)
                } else {
                    None
                }
            }
            (Ty::EnumVariant { enum_uid, .. }, Ty::Enum { uid, .. }) if enum_uid == uid => {
                Some(other.clone())
            }
            (Ty::Enum { uid, .. }, Ty::EnumVariant { enum_uid, .. }) if enum_uid == uid => {
                Some(self.clone())
            }
            // optionals
            (Ty::Optional { sub_ty: l_sub }, Ty::Optional { sub_ty: r_sub }) => l_sub
                .max(r_sub)
                .map(|max| Ty::Optional { sub_ty: max.into() }),
            (Ty::Optional { sub_ty }, Ty::Nil) | (Ty::Nil, Ty::Optional { sub_ty }) => {
                Some(Ty::Optional { sub_ty: *sub_ty })
            }
            (Ty::Nil, Ty::Nil) => Some(self.clone()),
            // max(?i32, i32) == ?i32
            // todo: should max(?i32, {usize}) be ?i32
            (Ty::Optional { sub_ty }, non_opt) | (non_opt, Ty::Optional { sub_ty })
                if non_opt.can_fit_into(sub_ty) =>
            {
                Some(Ty::Optional { sub_ty: *sub_ty })
            }
            (Ty::Nil, other) | (other, Ty::Nil) => Some(Ty::Optional {
                sub_ty: other.clone().into(),
            }),
            // error unions
            (
                Ty::ErrorUnion {
                    error_ty: l_error_ty,
                    payload_ty: l_payload_ty,
                },
                Ty::ErrorUnion {
                    error_ty: r_error_ty,
                    payload_ty: r_payload_ty,
                },
            ) => Some(Ty::ErrorUnion {
                error_ty: l_error_ty.max(r_error_ty)?.into(),
                payload_ty: l_payload_ty.max(r_payload_ty)?.into(),
            }),
            (
                Ty::ErrorUnion {
                    error_ty,
                    payload_ty,
                },
                non_err_union,
            )
            | (
                non_err_union,
                Ty::ErrorUnion {
                    error_ty,
                    payload_ty,
                },
            ) if non_err_union.can_fit_into(error_ty) || non_err_union.can_fit_into(payload_ty) => {
                Some(Ty::ErrorUnion {
                    error_ty: *error_ty,
                    payload_ty: *payload_ty,
                })
            }
            // void singletons -> types
            (other, Ty::Type) | (Ty::Type, other) if other.is_zero_sized() => Some(Ty::Type),

            // we can't spread Ty::AlwaysJumps because of case like this:
            // ```text
            // if condition {
            //      return true;
            // } else {
            //      // ... do stuff
            //      42
            // }
            // ```
            // the entire if statement should resolve to `{uint}`, and not to Ty::AlwaysJumps
            (Ty::Unknown | Ty::AlwaysJumps, other) | (other, Ty::Unknown | Ty::AlwaysJumps) => {
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
        if self == expected {
            return true;
        }

        match (self, expected) {
            // the callers of can_fit_into should probably
            // execute their own logic if one of the types is unknown
            (Ty::Unknown, _) | (_, Ty::Unknown) => true,
            (Ty::AlwaysJumps, _) => true,
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
                    sub_ty: found_sub_ty,
                },
                Ty::Pointer {
                    mutable: expected_mutable,
                    sub_ty: expected_sub_ty,
                },
            ) => {
                // Since the data is behind a pointer, we can't autocast it
                // so this has to be `is_functionally_equivalent_to`.
                // The only exception is for things like `^{uint}` -> `^i32`
                // TODO: maybe don't allow weak types
                matches!(
                    (found_mutable, expected_mutable),
                    (true, _) | (false, false)
                ) && ((found_sub_ty.might_be_weak()
                    && found_sub_ty.is_weak_replaceable_by(expected_sub_ty))
                    || found_sub_ty.is_functionally_equivalent_to(expected_sub_ty, false))
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
            ) => found_ty.is_functionally_equivalent_to(expected_ty, false),
            (Ty::Slice { sub_ty: found_ty }, Ty::RawSlice) => !found_ty.might_be_weak(),
            (
                Ty::AnonArray {
                    sub_ty: found_ty, ..
                },
                Ty::Slice {
                    sub_ty: expected_ty,
                },
            ) => found_ty.can_fit_into(expected_ty),
            (
                Ty::ConcreteArray {
                    sub_ty: found_ty, ..
                },
                Ty::Slice {
                    sub_ty: expected_ty,
                },
            ) => found_ty.is_functionally_equivalent_to(expected_ty, false),
            (
                Ty::AnonArray {
                    size: found_size,
                    sub_ty: found_ty,
                },
                Ty::ConcreteArray {
                    size: expected_size,
                    sub_ty: expected_ty,
                },
            )
            | (
                Ty::ConcreteArray {
                    size: found_size,
                    sub_ty: found_ty,
                },
                Ty::ConcreteArray {
                    size: expected_size,
                    sub_ty: expected_ty,
                },
            ) => found_size == expected_size && found_ty.can_fit_into(expected_ty),
            (_, Ty::Any) => true,
            (
                Ty::ConcreteStruct { uid: found_uid, .. },
                Ty::ConcreteStruct {
                    uid: expected_uid, ..
                },
            ) => found_uid == expected_uid,
            (
                Ty::AnonStruct {
                    members: found_members,
                    ..
                },
                Ty::ConcreteStruct {
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
                Ty::EnumVariant { uid: found_uid, .. },
                Ty::EnumVariant {
                    uid: expected_uid, ..
                },
            ) => found_uid == expected_uid,
            (Ty::EnumVariant { enum_uid, .. }, Ty::Enum { uid, .. }) => enum_uid == uid,
            (Ty::Nil, Ty::Optional { .. }) => true,
            (
                Ty::Optional { sub_ty: found_sub },
                Ty::Optional {
                    sub_ty: expected_sub,
                },
            ) => found_sub.can_fit_into(expected_sub),
            (found, Ty::Optional { sub_ty }) => found.can_fit_into(sub_ty),
            (
                Ty::ErrorUnion {
                    error_ty: found_error_ty,
                    payload_ty: found_payload_ty,
                },
                Ty::ErrorUnion {
                    error_ty: expected_error_ty,
                    payload_ty: expected_payload_ty,
                },
            ) => {
                found_error_ty.can_fit_into(expected_error_ty)
                    && found_payload_ty.can_fit_into(expected_payload_ty)
            }
            (
                found,
                Ty::ErrorUnion {
                    error_ty,
                    payload_ty,
                },
            ) => found.can_fit_into(error_ty) || found.can_fit_into(payload_ty),
            (found, expected) => found.is_functionally_equivalent_to(expected, false),
        }
    }

    /// returns true if two types are too similar to the point that they share common autocasts
    ///
    /// e.g. i64 and u64 can not be differentiated from each other because {uint} can autocast to
    /// either.
    ///
    /// This can be useful for functions with varargs, because it's impossible to tell when the
    /// varargs start and when they end.
    ///
    /// It's also used for disallowing things like `u64!u64`, because a return type of `{uint}`
    /// won't know whether to autocast to the ok variant or the err variant
    pub(crate) fn can_differentiate_from(&self, other: &Ty) -> bool {
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
            ) => left_ty.can_differentiate_from(right_ty),
            (Ty::Pointer { .. }, Ty::RawPtr { .. }) | (Ty::RawPtr { .. }, Ty::Pointer { .. }) => {
                false
            }
            (Ty::RawPtr { .. }, Ty::RawPtr { .. }) => false,
            (Ty::Slice { sub_ty: left_ty }, Ty::Slice { sub_ty: right_ty }) => {
                left_ty.can_differentiate_from(right_ty)
            }
            (Ty::Slice { .. }, Ty::RawSlice) | (Ty::RawPtr { .. }, Ty::Slice { .. }) => false,
            (
                Ty::ConcreteArray {
                    sub_ty: left_ty, ..
                },
                Ty::Slice { sub_ty: right_ty },
            )
            | (
                Ty::Slice { sub_ty: left_ty },
                Ty::ConcreteArray {
                    sub_ty: right_ty, ..
                },
            ) => {
                // this is perhaps much more strict than `can_fit_into`
                left_ty.can_differentiate_from(right_ty)
            }
            (
                Ty::ConcreteArray {
                    size: left_size,
                    sub_ty: left_ty,
                    ..
                },
                Ty::ConcreteArray {
                    size: right_size,
                    sub_ty: right_ty,
                    ..
                },
            ) => left_size != right_size || left_ty.can_differentiate_from(right_ty),
            (_, Ty::Any) | (Ty::Any, _) => false,
            (
                Ty::ConcreteStruct { uid: found_uid, .. },
                Ty::ConcreteStruct {
                    uid: expected_uid, ..
                },
            ) => found_uid != expected_uid,
            (
                Ty::AnonStruct {
                    members: left_members,
                },
                Ty::AnonStruct {
                    members: right_members,
                },
            )
            | (
                Ty::AnonStruct {
                    members: left_members,
                },
                Ty::ConcreteStruct {
                    members: right_members,
                    ..
                },
            )
            | (
                Ty::ConcreteStruct {
                    members: right_members,
                    ..
                },
                Ty::AnonStruct {
                    members: left_members,
                },
            ) => {
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

                    if !left_ty.can_differentiate_from(right_ty) {
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
                other.can_differentiate_from(sub_ty)
            }
            (Ty::EnumVariant { uid: left_uid, .. }, Ty::EnumVariant { uid: right_uid, .. }) => {
                left_uid != right_uid
            }
            (Ty::EnumVariant { enum_uid, .. }, Ty::Enum { uid, .. }) => enum_uid != uid,
            _ => {
                !((self.can_be_created_from_nothing() && other.can_be_created_from_nothing())
                    || self.can_fit_into(other)
                    || other.can_fit_into(self))
            }
        }
    }

    /// This is used for the `as` operator to see whether something can be casted into something else
    ///
    /// This only allows primitives to be casted to each other, or types that are already equal.
    pub fn can_cast_to(&self, cast_into: &Ty) -> bool {
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
            (Ty::EnumVariant { sub_ty: from, .. }, Ty::EnumVariant { sub_ty: to, .. }) => {
                from.can_cast_to(to)
            }
            (Ty::EnumVariant { sub_ty: from, .. }, to) => from.can_cast_to(to),
            (from, Ty::EnumVariant { sub_ty: to, .. }) => from.can_cast_to(to),

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
            (Ty::String, Ty::ConcreteArray { sub_ty, .. } | Ty::AnonArray { sub_ty, .. })
            | (Ty::ConcreteArray { sub_ty, .. } | Ty::AnonArray { sub_ty, .. }, Ty::String) => {
                matches!(sub_ty.as_ref(), Ty::Char | Ty::UInt(8))
            }

            (Ty::Slice { sub_ty: from, .. }, Ty::Slice { sub_ty: to }) => {
                from == to || from.is_weak_replaceable_by(to)
            }
            // `rawslice` casts are pretty much the same as `rawptr` casts
            (Ty::Slice { .. }, Ty::RawSlice)
            | (Ty::RawSlice, Ty::Slice { .. })
            | (Ty::RawSlice, Ty::RawSlice) => true,

            (
                Ty::ConcreteArray { sub_ty: from, .. } | Ty::AnonArray { sub_ty: from, .. },
                Ty::Slice { sub_ty: to },
            )
            | (
                Ty::Slice { sub_ty: from },
                Ty::ConcreteArray { sub_ty: to, .. } | Ty::AnonArray { sub_ty: to, .. },
            ) => from.can_cast_to(to),
            // TODO: maybe allow array -> rawslice
            (
                Ty::ConcreteArray {
                    size: found_size,
                    sub_ty: found_ty,
                }
                | Ty::AnonArray {
                    size: found_size,
                    sub_ty: found_ty,
                },
                Ty::ConcreteArray {
                    size: expected_size,
                    sub_ty: expected_ty,
                }
                | Ty::AnonArray {
                    size: expected_size,
                    sub_ty: expected_ty,
                },
            ) => found_size == expected_size && found_ty.can_cast_to(expected_ty),

            (found, Ty::Any) => !found.might_be_weak(),

            (
                Ty::ConcreteStruct {
                    members: found_members,
                    ..
                }
                | Ty::AnonStruct {
                    members: found_members,
                },
                Ty::ConcreteStruct {
                    members: expected_members,
                    ..
                }
                | Ty::AnonStruct {
                    members: expected_members,
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

            (other, Ty::Type) if other.is_zero_sized() => true,

            (Ty::Nil, Ty::Optional { .. }) => true,
            // todo: include tests for this
            (Ty::Optional { sub_ty: l_sub_ty }, Ty::Optional { sub_ty: r_sub_ty }) => {
                l_sub_ty.can_cast_to(r_sub_ty)
            }
            (other, Ty::Optional { sub_ty }) => other.can_cast_to(sub_ty),

            _ => self.is_functionally_equivalent_to(cast_into, true),
        }
    }

    /// allows `distinct` types to have the same semantics as other types as long as the inner type matches
    pub(crate) fn has_semantics_of(&self, expected: &Ty) -> bool {
        match (self, expected) {
            (
                Ty::Distinct { sub_ty: ty, .. } | Ty::EnumVariant { sub_ty: ty, .. },
                Ty::IInt(0) | Ty::UInt(0),
            ) => {
                if ty.has_semantics_of(expected) {
                    return true;
                }
            }
            (Ty::Distinct { .. } | Ty::EnumVariant { .. }, Ty::IInt(_) | Ty::UInt(_)) => {
                return false;
            }
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
                Ty::EnumVariant { uid: found_uid, .. },
                Ty::EnumVariant {
                    uid: expected_uid, ..
                },
            ) => {
                if found_uid == expected_uid {
                    return true;
                }
            }
            (Ty::Distinct { sub_ty, .. } | Ty::EnumVariant { sub_ty, .. }, expected) => {
                if sub_ty.has_semantics_of(expected) {
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
            Ty::ConcreteArray { sub_ty, .. } => sub_ty.might_be_weak(),
            // todo: is this slice branch needed? i just added it because i thought it was missing
            Ty::Slice { sub_ty, .. } => sub_ty.might_be_weak(),
            Ty::Pointer { sub_ty, .. } => sub_ty.might_be_weak(),
            Ty::Optional { sub_ty, .. } => sub_ty.might_be_weak(),
            _ => false,
        }
    }

    pub(crate) fn is_weak_replaceable_by(&self, expected: &Ty) -> bool {
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
                Ty::AnonArray {
                    size: found_size,
                    sub_ty: found_sub_ty,
                },
                Ty::ConcreteArray {
                    size: expected_size,
                    sub_ty: expected_sub_ty,
                },
            ) => {
                found_size == expected_size
                    && (found_sub_ty.is_weak_replaceable_by(expected_sub_ty)
                        || found_sub_ty.is_functionally_equivalent_to(expected_sub_ty, false))
            }
            (
                Ty::AnonArray {
                    size: _,
                    sub_ty: found_sub_ty,
                },
                Ty::Slice {
                    sub_ty: expected_sub_ty,
                },
            ) => {
                found_sub_ty.is_weak_replaceable_by(expected_sub_ty)
                    || found_sub_ty.is_functionally_equivalent_to(expected_sub_ty, false)
            }
            (
                Ty::Slice {
                    sub_ty: found_sub_ty,
                },
                Ty::Slice {
                    sub_ty: expected_sub_ty,
                },
            ) => found_sub_ty.is_functionally_equivalent_to(expected_sub_ty, false),
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
                ) && found_sub_ty.might_be_weak()
                    && found_sub_ty.is_weak_replaceable_by(expected_sub_ty)
            }
            // todo: is this correct?
            (Ty::ConcreteStruct { .. } | Ty::AnonStruct { .. }, Ty::ConcreteStruct { .. }) => {
                self.can_fit_into(expected)
            }
            (found, Ty::Distinct { sub_ty: ty, .. }) => found.is_weak_replaceable_by(ty),
            (
                Ty::Optional {
                    sub_ty: found_sub_ty,
                },
                Ty::Optional {
                    sub_ty: expected_sub_ty,
                },
            ) => found_sub_ty.is_weak_replaceable_by(expected_sub_ty),
            (
                found_ty,
                Ty::Optional {
                    sub_ty: expected_sub_ty,
                },
            ) => found_ty.is_weak_replaceable_by(expected_sub_ty),
            _ => false,
        }
    }

    /// returns true if the two types are almost but not quite the same
    ///
    /// can be used when running `.display()` on two types so that extra information like uid's
    /// are only displayed when needed
    pub fn is_similar_to(&self, other: &Self) -> bool {
        if self == other {
            return false;
        }

        match (self, other) {
            (
                Ty::Pointer {
                    sub_ty: l_sub_ty, ..
                },
                Ty::Pointer {
                    sub_ty: r_sub_ty, ..
                },
            ) => l_sub_ty.is_similar_to(r_sub_ty),
            (
                Ty::AnonArray {
                    sub_ty: l_sub_ty,
                    size: l_size,
                },
                Ty::ConcreteArray {
                    sub_ty: r_sub_ty,
                    size: r_size,
                },
            )
            | (
                Ty::ConcreteArray {
                    sub_ty: r_sub_ty,
                    size: r_size,
                },
                Ty::AnonArray {
                    sub_ty: l_sub_ty,
                    size: l_size,
                },
            ) => l_size == r_size && l_sub_ty.is_similar_to(r_sub_ty),
            (
                Ty::ConcreteArray {
                    sub_ty: r_sub_ty,
                    size: r_size,
                },
                Ty::ConcreteArray {
                    sub_ty: l_sub_ty,
                    size: l_size,
                },
            ) => l_size == r_size && l_sub_ty.is_similar_to(r_sub_ty),
            (Ty::Slice { sub_ty: l_sub_ty }, Ty::Slice { sub_ty: r_sub_ty }) => {
                l_sub_ty.is_similar_to(r_sub_ty)
            }
            (Ty::AnonStruct { members: l_members }, Ty::AnonStruct { members: r_members })
            | (
                Ty::AnonStruct { members: l_members },
                Ty::ConcreteStruct {
                    members: r_members, ..
                },
            )
            | (
                Ty::ConcreteStruct {
                    members: l_members, ..
                },
                Ty::AnonStruct { members: r_members },
            ) => {
                l_members.len() == r_members.len()
                    && l_members
                        .iter()
                        .zip_eq(r_members.iter())
                        .all(|(l, r)| l.ty.is_similar_to(&r.ty))
            }
            (
                Ty::ConcreteStruct {
                    uid: l_uid,
                    members: l_members,
                },
                Ty::ConcreteStruct {
                    uid: r_uid,
                    members: r_members,
                },
            ) => {
                l_uid != r_uid
                    && l_members.len() == r_members.len()
                    && l_members
                        .iter()
                        .zip_eq(r_members.iter())
                        .all(|(l, r)| l.ty.is_similar_to(&r.ty))
            }
            (
                Ty::Distinct {
                    uid: l_uid,
                    sub_ty: l_sub_ty,
                },
                Ty::Distinct {
                    uid: r_uid,
                    sub_ty: r_sub_ty,
                },
            ) => l_uid != r_uid && l_sub_ty.is_similar_to(r_sub_ty),
            (
                Ty::EnumVariant {
                    variant_name: l_variant_name,
                    uid: l_uid,
                    ..
                },
                Ty::EnumVariant {
                    variant_name: r_variant_name,
                    uid: r_uid,
                    ..
                },
            ) => l_uid != r_uid && l_variant_name != r_variant_name,
            (
                Ty::Function {
                    param_tys: l_param_tys,
                    return_ty: l_return_ty,
                },
                Ty::Function {
                    param_tys: r_param_tys,
                    return_ty: r_return_ty,
                },
            ) => {
                l_return_ty.is_similar_to(r_return_ty)
                    && l_param_tys.len() == r_param_tys.len()
                    && l_param_tys
                        .iter()
                        .zip_eq(r_param_tys.iter())
                        .all(|(l, r)| l.ty.is_similar_to(&r.ty))
            }
            (
                Ty::Optional {
                    sub_ty: l_sub_ty, ..
                },
                Ty::Optional {
                    sub_ty: r_sub_ty, ..
                },
            ) => l_sub_ty.is_similar_to(r_sub_ty),
            (
                Ty::ErrorUnion {
                    error_ty: l_error_ty,
                    payload_ty: l_payload_ty,
                    ..
                },
                Ty::ErrorUnion {
                    error_ty: r_error_ty,
                    payload_ty: r_payload_ty,
                    ..
                },
            ) => l_error_ty.is_similar_to(r_error_ty) && l_payload_ty.is_similar_to(r_payload_ty),
            (_, _) => false,
        }
    }

    pub fn simple_display<'a>(&'a self, interner: &'a Interner, show_ids: bool) -> TyDisplay<'a> {
        TyDisplay {
            ty: self,
            interner,
            show_ids,
            kind: TyDisplayKind::Simple,
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
                Ty::EnumVariant { sub_ty, .. } if unwrap_variants => {
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
                    Ty::Any | Ty::RawPtr { .. } | Ty::RawSlice | Ty::Unknown
                )
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

enum TyDisplayKind<'a> {
    Simple,
    ShowNames {
        mod_dir: &'a std::path::Path,
        interned: Intern<Ty>,
    },
}

pub struct TyDisplay<'a> {
    interner: &'a Interner,
    ty: &'a Ty,
    show_ids: bool,
    kind: TyDisplayKind<'a>,
}

impl TyDisplay<'_> {
    fn try_named_self(&self, f: &mut std::fmt::Formatter) -> Result<bool, std::fmt::Error> {
        match self.kind {
            TyDisplayKind::ShowNames { interned, .. } => self.try_named(f, interned),
            TyDisplayKind::Simple => Ok(false),
        }
    }

    fn try_named(
        &self,
        f: &mut std::fmt::Formatter,
        ty: Intern<Ty>,
    ) -> Result<bool, std::fmt::Error> {
        match self.kind {
            TyDisplayKind::ShowNames { mod_dir, .. } => match get_type_name(ty) {
                Some(TyName::Global(fqn)) => {
                    write!(f, "{}", fqn.to_string(mod_dir, self.interner))?;

                    Ok(true)
                }
                Some(TyName::Local(name)) => {
                    write!(f, "{}", self.interner.lookup(name.0))?;

                    Ok(true)
                }
                None => Ok(false),
            },
            TyDisplayKind::Simple => Ok(false),
        }
    }

    fn display_sub<'a>(&'a self, ty: &'a Intern<Ty>) -> TyDisplay<'a> {
        match self.kind {
            TyDisplayKind::Simple => ty.simple_display(self.interner, self.show_ids),
            TyDisplayKind::ShowNames { mod_dir, .. } => {
                ty.named_display(mod_dir, self.interner, self.show_ids)
            }
        }
    }
}

impl Display for TyDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.try_named_self(f)? {
            return Ok(());
        }

        match self.ty {
            Ty::NotYetResolved => write!(f, "!"),
            Ty::Unknown => write!(f, "<unknown>"),
            Ty::IInt(bit_width) => match *bit_width {
                u8::MAX => write!(f, "isize"),
                0 => write!(f, "{{int}}"),
                _ => write!(f, "i{}", bit_width),
            },
            Ty::UInt(bit_width) => match *bit_width {
                u8::MAX => write!(f, "usize"),
                0 => write!(f, "{{uint}}"),
                _ => write!(f, "u{}", bit_width),
            },
            Ty::Float(bit_width) => match *bit_width {
                0 => write!(f, "{{float}}"),
                _ => write!(f, "f{}", bit_width),
            },
            Ty::Bool => write!(f, "bool"),
            Ty::String => write!(f, "str"),
            Ty::Char => write!(f, "char"),
            Ty::AnonArray { size, sub_ty } if self.show_ids => {
                write!(f, "~[{size}]{}", self.display_sub(sub_ty))
            }
            Ty::AnonArray { size, sub_ty } | Ty::ConcreteArray { size, sub_ty, .. } => {
                write!(f, "[{size}]{}", self.display_sub(sub_ty))
            }
            Ty::Slice { sub_ty } => {
                write!(f, "[]{}", self.display_sub(sub_ty))
            }
            Ty::Pointer { mutable, sub_ty } => {
                write!(f, "^")?;
                if *mutable {
                    write!(f, "mut ")?;
                }
                write!(f, "{}", self.display_sub(sub_ty))
            }
            Ty::Distinct { uid, sub_ty: ty } => {
                write!(f, "distinct")?;
                if self.show_ids {
                    write!(f, "'{uid}")?;
                }
                write!(f, " {}", self.display_sub(ty))
            }
            Ty::Function {
                param_tys: params,
                return_ty,
            } => {
                write!(f, "(")?;

                for (idx, param) in params.iter().enumerate() {
                    if param.varargs {
                        write!(f, "...")?;
                    }

                    write!(f, "{}", self.display_sub(&param.ty))?;

                    if idx != params.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ") -> ")?;
                write!(f, "{}", self.display_sub(return_ty))
            }
            Ty::ConcreteStruct { uid, members } => {
                write!(f, "struct")?;
                if self.show_ids {
                    write!(f, "'{uid}")?;
                }
                write!(f, " {{")?;

                for (idx, MemberTy { name, ty }) in members.iter().enumerate() {
                    write!(f, "{}", self.interner.lookup(name.0))?;
                    write!(f, ": ")?;

                    write!(f, "{}", self.display_sub(ty))?;

                    if idx != members.len() - 1 {
                        write!(f, ", ")?;
                    }
                }

                write!(f, "}}")
            }
            Ty::AnonStruct { members } => {
                write!(f, "~struct {{")?;

                for (idx, MemberTy { name, ty }) in members.iter().enumerate() {
                    write!(f, "{}", self.interner.lookup(name.0))?;
                    write!(f, ": ")?;

                    write!(f, "{}", self.display_sub(ty))?;

                    if idx != members.len() - 1 {
                        write!(f, ", ")?;
                    }
                }

                write!(f, "}}")
            }
            Ty::Enum { uid, variants } => {
                write!(f, "enum")?;
                if self.show_ids {
                    write!(f, "'{uid}")?;
                }
                write!(f, " {{")?;

                for (idx, variant_ty) in variants.iter().enumerate() {
                    let Ty::EnumVariant {
                        variant_name,
                        sub_ty,
                        discriminant,
                        ..
                    } = variant_ty.as_ref()
                    else {
                        unreachable!("the variants of an enum should be `Ty::Variant`")
                    };

                    write!(f, "{}", self.interner.lookup(variant_name.0))?;

                    if !sub_ty.is_void() {
                        write!(f, ": ")?;
                        write!(f, "{}", self.display_sub(sub_ty))?;
                    }

                    if self.show_ids {
                        write!(f, " | {discriminant}")?;
                    }

                    if idx != variants.len() - 1 {
                        write!(f, ", ")?;
                    }
                }

                write!(f, "}}")
            }
            Ty::EnumVariant {
                variant_name,
                enum_uid,
                uid,
                ..
            } => {
                let enum_ty = get_enum_from_uid(*enum_uid);
                let named = self.try_named(f, enum_ty)?;

                write!(f, ".{}", self.interner.lookup(variant_name.0))?;

                if self.show_ids && !named {
                    write!(f, "'{uid}")?;
                }

                Ok(())
            }
            Ty::Nil => write!(f, "nil"),
            Ty::Optional { sub_ty } => {
                write!(f, "?{}", self.display_sub(sub_ty))
            }
            Ty::ErrorUnion {
                error_ty,
                payload_ty,
            } => write!(
                f,
                "{}!{}",
                self.display_sub(error_ty),
                self.display_sub(payload_ty)
            ),
            Ty::Type => write!(f, "type"),
            Ty::Any => write!(f, "any"),
            Ty::RawPtr { mutable: false } => write!(f, "rawptr"),
            Ty::RawPtr { mutable: true } => write!(f, "mut rawptr"),
            Ty::RawSlice => write!(f, "rawslice"),
            Ty::Void => write!(f, "void"),
            Ty::File(file_name) => match self.kind {
                TyDisplayKind::Simple => write!(f, "file {}", file_name.debug(self.interner)),
                TyDisplayKind::ShowNames { mod_dir, .. } => {
                    write!(f, "file {}", file_name.to_string(mod_dir, self.interner))
                }
            },
            Ty::AlwaysJumps => write!(f, "noeval"),
        }
    }
}

pub trait InternTyDisplay {
    fn named_display<'a>(
        &'a self,
        mod_dir: &'a std::path::Path,
        interner: &'a interner::Interner,
        show_ids: bool,
    ) -> TyDisplay<'a>;
}

impl InternTyDisplay for Intern<Ty> {
    fn named_display<'a>(
        &'a self,
        mod_dir: &'a std::path::Path,
        interner: &'a interner::Interner,
        show_ids: bool,
    ) -> TyDisplay<'a> {
        TyDisplay {
            interner,
            ty: self,
            show_ids,
            kind: TyDisplayKind::ShowNames {
                mod_dir,
                interned: *self,
            },
        }
    }
}

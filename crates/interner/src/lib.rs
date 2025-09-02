use std::mem;

use lasso::Spur;

macro_rules! impl_interner {
    ($($keyword:ident => $text:expr,)*) => {
        impl Default for Interner {
            fn default() -> Self {
                let mut interner = Self(lasso::Rodeo::default());
                $(interner.intern($text);)*
                interner
            }
        }

        impl Key {
            impl_interner!(@step 1u32, $($keyword,)*);
        }
    };
    (@step $idx:expr, $head:ident, $($tail:ident,)*) => {
        pub fn $head() -> Self {
            Self::from_raw($idx)
        }

        impl_interner!(@step ($idx + 1u32), $($tail,)*);
    };
    (@step $_idx:expr,) => {};
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Key(lasso::Spur);

pub struct Interner(lasso::Rodeo);

impl_interner! {
    void => "void",
    nil => "nil",
    isize => "isize",
    i128 => "i128",
    i64 => "i64",
    i32 => "i32",
    i16 => "i16",
    i8 => "i8",
    usize => "usize",
    u128 => "u128",
    u64 => "u64",
    u32 => "u32",
    u16 => "u16",
    u8 => "u8",
    f64 => "f64",
    f32 => "f32",
    bool => "bool",
    str => "str",
    char => "char",
    r#type => "type",
    any => "any",
    rawptr => "rawptr",
    rawslice => "rawslice",
    // these are included for the types returned from `#builtin(..)`
    name => "name",
    len => "len",
    size => "size",
    align => "align",
    mutable => "mutable",
    ty => "ty",
    sub_ty => "sub_ty",
    error_ty => "error_ty",
    payload_ty => "payload_ty",
    is_non_zero => "is_non_zero",
    discriminant => "discriminant",
    discriminant_offset => "discriminant_offset",
    offset => "offset",
    variants => "variants",
    members => "members",
}

impl Interner {
    pub fn intern(&mut self, s: &str) -> Key {
        Key(self.0.get_or_intern(s))
    }

    pub fn get_interned(&self, s: &str) -> Option<Key> {
        self.0.get(s).map(Key)
    }

    pub fn lookup(&self, key: Key) -> &str {
        self.0.resolve(&key.0)
    }
}

impl Key {
    pub fn from_raw(raw: u32) -> Self {
        unsafe { Self(mem::transmute::<u32, Spur>(raw)) }
    }

    pub fn to_raw(self) -> u32 {
        unsafe { mem::transmute(self.0) }
    }
}

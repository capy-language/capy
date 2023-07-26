use std::mem;

pub struct Interner(lasso::Rodeo);

impl Default for Interner {
    fn default() -> Self {
        let mut interner = Self(lasso::Rodeo::default());
        interner.intern("void");
        interner.intern("isize");
        interner.intern("i128");
        interner.intern("i64");
        interner.intern("i32");
        interner.intern("i16");
        interner.intern("i8");
        interner.intern("usize");
        interner.intern("u128");
        interner.intern("u64");
        interner.intern("u32");
        interner.intern("u16");
        interner.intern("u8");
        interner.intern("bool");
        interner.intern("string");
        interner.intern("type");
        interner
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Key(lasso::Spur);

impl Interner {
    pub fn intern(&mut self, s: &str) -> Key {
        Key(self.0.get_or_intern(s))
    }

    pub fn lookup(&self, key: Key) -> &str {
        self.0.resolve(&key.0)
    }
}

impl Key {
    pub fn void() -> Self {
        Self::from_raw(1)
    }

    pub fn isize() -> Self {
        Self::from_raw(2)
    }

    pub fn i128() -> Self {
        Self::from_raw(3)
    }

    pub fn i64() -> Self {
        Self::from_raw(4)
    }

    pub fn i32() -> Self {
        Self::from_raw(5)
    }

    pub fn i16() -> Self {
        Self::from_raw(6)
    }

    pub fn i8() -> Self {
        Self::from_raw(7)
    }

    pub fn usize() -> Self {
        Self::from_raw(8)
    }

    pub fn u128() -> Self {
        Self::from_raw(9)
    }

    pub fn u64() -> Self {
        Self::from_raw(10)
    }

    pub fn u32() -> Self {
        Self::from_raw(11)
    }

    pub fn u16() -> Self {
        Self::from_raw(12)
    }

    pub fn u8() -> Self {
        Self::from_raw(13)
    }

    pub fn bool() -> Self {
        Self::from_raw(14)
    }

    pub fn string() -> Self {
        Self::from_raw(15)
    }

    pub fn r#type() -> Self {
        Self::from_raw(16)
    }

    pub fn from_raw(raw: u32) -> Self {
        unsafe { Self(mem::transmute(raw)) }
    }

    pub fn to_raw(self) -> u32 {
        unsafe { mem::transmute(self.0) }
    }
}

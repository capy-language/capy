use std::mem;

pub struct Interner(lasso::Rodeo);

impl Default for Interner {
    fn default() -> Self {
        let mut interner = Self(lasso::Rodeo::default());
        interner.intern("void");
        interner.intern("s32");
        interner.intern("string");
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

    pub fn s32() -> Self {
        Self::from_raw(2)
    }

    pub fn string() -> Self {
        Self::from_raw(3)
    }

    pub fn from_raw(raw: u32) -> Self {
        unsafe { Self(mem::transmute(raw)) }
    }

    pub fn to_raw(self) -> u32 {
        unsafe { mem::transmute(self.0) }
    }
}

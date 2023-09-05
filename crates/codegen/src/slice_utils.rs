use std::rc::Rc;

pub(crate) trait IntoBoxedSlice {
    fn into_boxed_slice(self) -> Box<[u8]>;
}

impl IntoBoxedSlice for Rc<[u8]> {
    fn into_boxed_slice(self) -> Box<[u8]> {
        self.to_vec().into_boxed_slice()
    }
}

impl IntoBoxedSlice for Vec<u8> {
    fn into_boxed_slice(self) -> Box<[u8]> {
        self.into_boxed_slice()
    }
}

pub(crate) trait IntoRcSlice {
    fn into_rc_slice(self) -> Rc<[u8]>;
}

impl<const N: usize> IntoRcSlice for [u8; N] {
    fn into_rc_slice(self) -> Rc<[u8]> {
        Rc::new(self)
    }
}

impl IntoRcSlice for &[u8] {
    fn into_rc_slice(self) -> Rc<[u8]> {
        self.into()
    }
}

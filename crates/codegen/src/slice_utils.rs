use std::rc::Rc;

pub(crate) trait IntoBoxedSlice {
    fn into_boxed_slice(self) -> Box<[u8]>;
}

impl IntoBoxedSlice for Rc<[u8]> {
    fn into_boxed_slice(self) -> Box<[u8]> {
        if self.len() == 0 {
            return Box::default();
        }
        let mut result = unsafe { Box::<[u8]>::new_uninit_slice(self.len()).assume_init() };
        result.clone_from_slice(&self);

        result
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
        if self.is_empty() {
            return Rc::<[u8; 0]>::default();
        }

        let result = unsafe { Rc::<[u8]>::new_uninit_slice(self.len()).assume_init() };
        let ptr = Rc::into_raw(result);
        unsafe {
            std::ptr::copy(
                (self as *const [u8]) as *const u8,
                ptr as *mut u8,
                self.len(),
            )
        }

        unsafe { Rc::from_raw(ptr) }
    }
}

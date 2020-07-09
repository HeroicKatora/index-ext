//! Not quite dependent typing for eliding bounds checks.
//!
//! The main idea is to use lifetimes as a compile time tag to identify a particular exact slice
//! without keeping a direct reference of it.
use core::marker::PhantomData;

/// The length of a particular slice.
#[derive(Clone, Copy)]
pub struct Len<'r> {
    len: usize,
    lifetime: PhantomData<&'r fn(&'r [()])>,
}

#[derive(Clone, Copy)]
pub struct Idx<'r> {
    idx: usize,
    lifetime: PhantomData<&'r fn(&'r [()])>,
}

impl Len<'_> {
    pub fn with<T, U>(
        slice: &[T],
        f: impl for<'r> FnOnce(Len<'r>, &'r [T]) -> U
    ) -> U {
        let len = Len {
            len: slice.len(),
            lifetime: PhantomData,
        };

        f(len, slice)
    }

    pub fn with_mut<T, U>(
        slice: &mut [T],
        f: impl for<'r> FnOnce(Len<'r>, &'r mut [T]) -> U
    ) -> U {
        let len = Len {
            len: slice.len(),
            lifetime: PhantomData,
        };

        f(len, slice)
    }
}

impl<'slice> Len<'slice> {
    pub fn index(&self, idx: usize) -> Option<Idx<'slice>> {
        if self.len < idx {
            Some(Idx { idx, lifetime: self.lifetime })
        } else {
            None
        }
    }
}

impl<'slice> Idx<'slice> {
    pub fn get_ref<T>(self, slice: &'slice [T]) -> &'slice T {
        unsafe { slice.get_unchecked(self.idx) }
    }

    pub fn get_mut<T>(self, slice: &'slice mut [T]) -> &'slice mut T {
        unsafe { slice.get_unchecked_mut(self.idx) }
    }
}

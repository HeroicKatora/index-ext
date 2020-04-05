use core::ops::{Index, IndexMut};

/// A marker struct for statically sized range to (`..n`).
///
/// This can make use of parameter deduction in many cases, for example if assigning the slice to a
/// right hand side array pattern.
///
/// ```
/// use index_ext::RangeTo;
/// # let buf = &[0u8; 3][..];
/// let [r, g, b] = buf[RangeTo];
/// ```
pub struct RangeTo<const N: usize>;

/// An alias for `RangeTo` which may sometimes be more expressive.
pub type Prefix<const N: usize> = RangeTo<N>;

impl<T, const N: usize> Index<RangeTo<N>> for [T] {
    type Output = [T; N];
    fn index(&self, _: RangeTo<{N}>) -> &[T; N] {
        let slice = &self[..N];
        unsafe {
            // SAFETY: the layout of slices and arrays of the same length are the same. We'd like
            // to use TryFrom/TryInto here but that currently would require the relaxed bounds on
            // array impls.
            &*(slice.as_ptr() as *const [T; N])
        }
    }
}

impl<T, const N: usize> IndexMut<RangeTo<N>> for [T] {
    fn index_mut(&mut self, _: RangeTo<{N}>) -> &mut [T; N] {
        let slice = &mut self[..N];
        unsafe {
            // SAFETY: the layout of slices and arrays of the same length are the same. We'd like
            // to use TryFrom/TryInto here but that currently would require the relaxed bounds on
            // array impls.
            &mut *(slice.as_mut_ptr() as *mut [T; N])
        }
    }
}

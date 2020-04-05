use core::ops::{Index, IndexMut};

/// A marker struct for statically sized range to (`..n`).
///
/// This can make use of parameter deduction in many cases, for example if assigning the slice to a
/// right hand side array pattern.
///
/// ```
/// # let buf = &[0u8, 3][..];
/// let [r, g, b] = &buf[RangeTo];
/// ```
pub struct RangeTo<const N: usize>;

type Prefix<const N: usize> = RangeTo<N>;

impl<T, const N: usize> Index<[T]> for RangeTo<N> {
    type Output = [T; N];
    fn index(&self) -> &[T; N] {
        let slice = &self[..N];
        unsafe {
            // SAFETY: the layout of slices and arrays of the same length are the same. We'd like
            // to use TryFrom/TryInto here but that currently would require the relaxed bounds on
            // array impls.
            &*(slice as *const T as *const [T; N])
        }
    }
}

impl<T, const N: usize> IndexMut<[T]> for RangeTo<N> {
    fn index_mut(&mut self) -> &mut [T; N] {
        let slice = &mut self[..N];
        unsafe {
            // SAFETY: the layout of slices and arrays of the same length are the same. We'd like
            // to use TryFrom/TryInto here but that currently would require the relaxed bounds on
            // array impls.
            &mut *(slice as *mut T as *mut [T; N])
        }
    }
}

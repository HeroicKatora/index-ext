//! Index types that produce arrays.
//!
//! The default rust index types, that is `usize` and those constructed with special range syntax,
//! produce slices. That's not necessarily bad as designing them with `const` in mind would have
//! delay their introduction and have problems of coherency. The ergonomic overhead however muddles
//! the intent and requires writing a never failing, but semantically fallible conversion.
//!
//! With the introduction of `const` generic parameters we can design a better solution with which
//! the length of the range is statically determined and which consequently can return a proper
//! array reference instead of a dynamically sized slice. Even better, as this happens in the type
//! system, some parameter values can be deduced where the compiler can match with another array
//! type!
//!
//! Having to decide on the length introduces new complications that are usually put off to the
//! actual execution of indexing. If the given indices are inconsistent, i.e. the end is smaller
//! than the start or the end of an inclusive range is the maximum possible index, then there is no
//! possible type to represent the output. We will not solve this dilemma at the moment, and only
//! define the simple indices which is precisely `RangeTo<usize>`.
use core::ops::{Index, IndexMut};

/// A marker struct for statically sized range to (`..n`).
///
/// This can make use of parameter deduction in many cases, for example if assigning the slice to a
/// right hand side array pattern.
///
/// ```
/// use index_ext::array::ArrayPrefix;
/// # let buf = &[0u8; 3][..];
/// let [r, g, b] = buf[ArrayPrefix];
/// ```
///
/// To slice off an array in the middle of a slice, utilize the common pattern of indexing twice.
///
/// ```
/// use index_ext::array::ArrayPrefix;
/// # let buf = &[0u8; 3][..];
/// let [u, v] = buf[1..][ArrayPrefix];
/// ```
pub struct ArrayPrefix<const N: usize>;

impl<T, const N: usize> Index<ArrayPrefix<N>> for [T] {
    type Output = [T; N];
    fn index(&self, _: ArrayPrefix<{ N }>) -> &[T; N] {
        let slice = &self[..N];
        unsafe {
            // SAFETY: the layout of slices and arrays of the same length are the same. We'd like
            // to use TryFrom/TryInto here but that currently would require the relaxed bounds on
            // array impls.
            &*(slice.as_ptr() as *const [T; N])
        }
    }
}

impl<T, const N: usize> IndexMut<ArrayPrefix<N>> for [T] {
    fn index_mut(&mut self, _: ArrayPrefix<{ N }>) -> &mut [T; N] {
        let slice = &mut self[..N];
        unsafe {
            // SAFETY: the layout of slices and arrays of the same length are the same. We'd like
            // to use TryFrom/TryInto here but that currently would require the relaxed bounds on
            // array impls.
            &mut *(slice.as_mut_ptr() as *mut [T; N])
        }
    }
}

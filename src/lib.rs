//! Adds more index types.
//!
//! There are cases where an index type might not be `usize`, many of them for compatibility
//! reasons. For example, an archive format may choose to always represent its offsets as `u32` or
//! the `io::Seek` trait which uses `i64` for that purpose. Translating these indices into the
//! platform native offset type is error prone, potentially lossy, and in case it is done
//! incorrectly leads to subtle platform dependent bugs.
//!
//! Wouldn't it be better for this conversion to happen implicitly and correctly where the actual
//! indexing takes place? That's precisely what `Index` provides. (It's a method and a trait of
//! the same name, for both panicking and fallible accessors).
//!
//! ```
//! use index_ext::IntIndex;
//!
//! let fine = [0u8; 2][IntIndex(1u32)];
//! let also = [0u8; 2][IntIndex(1u128)];
//!
//! assert_eq!([0u8; 2].get_int(u128::max_value()), None);
//! ```
//!
//! ## Unfinished features
//!
//! The marker WIP means it is worked on, Planned that it will be worked on, and Idea that it is
//! still unevaluated but might be interesting.
//!
//! [Planned]: An index type `CharAt(n: usize)` that dereferences to the characters of a string at
//! a particular position, represented by a string wrapper that allows converting into a `char`.
//! Note that a generic `Chars` would not be constant time which may be surprising if used in index
//! position.
//!
//! [Planned]: An index type `InsertWith` for `HashMap` and `BTreeMap` that will construct an
//! element when an entry is missing, similar to C++, and thus be a panic free alternative. _Maybe_
//! we could index a `Vec<_>` with this type as well, extending as necessary, but this would again
//! not be constant time.
//!
//! [Idea]: An adapter `OrEmpty` that uses `get` internally and substitutes an empty slice instead
//! of panicking.
//!
//! ## Design notes
//!
//! The extension traits offered here have a slight ergonomic problem compared to being included in
//! the standard library. Its `ops::Index` impls on slices are provided by the `SliceIndex` trait.
//! Since this is a nightly trait _and_ sealed by design we can not use it. However, we also can
//! not use a generic impl for all `T: crate::SliceIndex<[U]>` as this is forbidden by coherence
//! rules for foreign types. We thus utilize two kinds of indexing: Implement the Index trait
//! directly for all concrete applicable types and provide a single newtype which acts as a proxy
//! for the otherwise unconstrained type parameter of the generic impl. If the types were added to
//! `core` then this indirection would not be necessary and ergonomics would improve.
//!
//! ## Nightly features
//! 
//! [WIP]: const generics enabled index types that return arrays `[T; N]` instead of slices. Due to
//! recent advances in parameter deduction, the length parameter need not even be named.
//!
//! ```ignore
//! // Grab an array of three element from a slice.
//! let [r, g, b] = &slice[RangeTo];
//! ```
//!
//! [WIP]: 
#![no_std]
#![cfg_attr(feature = "nightly", feature(const_generics))]

use core::slice::SliceIndex;

#[cfg(feature = "nightly")]
mod const_;
pub mod int;

pub(crate) mod sealed {
    pub trait Same<T> {
        fn identity(this: T) -> Self;
    }

    impl<T> Same<T> for T {
        fn identity(this: T) -> T { this }
    }
}

pub mod idx {
}

pub trait IntSliceIndex<T: ?Sized>: int::sealed::IntSliceIndex<T> { }

/// An extension trait allowing slices to be indexed by everything convertible to `usize`.
pub trait IntIndex {
    fn get_int<T>(&self, idx: T)
        -> Option<&'_ <T::Index as SliceIndex<Self>>::Output>
    where
        T: IntSliceIndex<Self>;

    fn get_int_mut<T>(&mut self, idx: T)
        -> Option<&'_ mut <T::Index as SliceIndex<Self>>::Output>
    where
        T: IntSliceIndex<Self>;
}

use sealed::Same;

impl<U> IntIndex for [U] {
    fn get_int<T>(&self, idx: T)
        -> Option<&'_ <T::Index as SliceIndex<Self>>::Output>
    where
        T: IntSliceIndex<Self>,
    {
        let idx: T::IntoIndex = idx.index().ok()?;
        let idx: T::Index = Same::identity(idx);
        self.get(idx)
    }

    fn get_int_mut<T>(&mut self, idx: T)
        -> Option<&'_ mut <T::Index as SliceIndex<Self>>::Output>
    where
        T: IntSliceIndex<Self>,
    {
        let idx: T::IntoIndex = idx.index().ok()?;
        let idx: T::Index = Same::identity(idx);
        self.get_mut(idx)
    }
}

impl IntIndex for str {
    fn get_int<T>(&self, idx: T)
        -> Option<&'_ <T::Index as SliceIndex<Self>>::Output>
    where
        T: IntSliceIndex<Self>,
    {
        let idx: T::IntoIndex = idx.index().ok()?;
        let idx: T::Index = Same::identity(idx);
        self.get(idx)
    }

    fn get_int_mut<T>(&mut self, idx: T)
        -> Option<&'_ mut <T::Index as SliceIndex<Self>>::Output>
    where
        T: IntSliceIndex<Self>,
    {
        let idx: T::IntoIndex = idx.index().ok()?;
        let idx: T::Index = Same::identity(idx);
        self.get_mut(idx)
    }
}

#[allow(non_snake_case)]
pub fn IntIndex<T>(idx: T) -> int::IntIndex<T> {
    int::IntIndex(idx)
}

#[cfg(test)]
mod test {
    use super::IntIndex;

    #[test]
    #[should_panic = "100"]
    fn panics_with_length_u32() {
        [0u8; 0][IntIndex(100u32)];
    }

    #[test]
    #[should_panic = "100"]
    fn panics_with_length_u8() {
        [0u8; 0][IntIndex(100u8)];
    }

    #[test]
    #[should_panic = "-1"]
    fn panics_with_length_i8() {
        [0u8; 0][IntIndex(-1i8)];
    }

    #[test]
    #[should_panic = "100000000000000000000000000000000000000"]
    fn panics_with_length_u128() {
        [0u8; 0][IntIndex(100000000000000000000000000000000000000u128)];
    }

    #[test]
    fn index_with_all() {
        let slice = [0u8; 10];
        macro_rules! assert_slice_success {
            (@$slice:path, $exp:expr) => {
                assert!($slice.get_int($exp).is_some());
            };
            ($slice:path: $($exp:expr),*) => {
                $(assert_slice_success!(@$slice, $exp);)*
            }
        }

        macro_rules! assert_slice_fail {
            (@$slice:path, $exp:expr) => {
                assert_eq!($slice.get_int($exp), None);
            };
            ($slice:path: $($exp:expr),*) => {
                $(assert_slice_fail!(@$slice, $exp);)*
            }
        }

        assert_slice_success!(slice: 0u8, 0i8, 0u16, 0i16, 0u32, 0i32, 0u64, 0i64);
        assert_slice_success!(slice: ..10u8, ..10i8, ..10u16, ..10i16, ..10u32, ..10i32, ..10u64, ..10i64);
        assert_slice_success!(slice: 0..10u8, 0..10i8, 0..10u16, 0..10i16, 0..10u32, 0..10i32, 0..10u64, 0..10i64);
        assert_slice_success!(slice: 10u8.., 10i8.., 10u16.., 10i16.., 10u32.., 10i32.., 10u64.., 10i64..);

        assert_slice_fail!(slice: -1i8, -1i16, -1i32, -1i64);
    }

    #[test]
    fn str_indices() {
        let text = "What if ascii still has it?";
        assert_eq!(text.get_int(8u8..13), Some("ascii"));
    }
}

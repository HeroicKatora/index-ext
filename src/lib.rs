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
//! use index_ext::Int;
//!
//! let fine = [0u8; 2][Int(1u32)];
//! let also = [0u8; 2][Int(1u128)];
//!
//! assert_eq!([0u8; 2].get_int(u128::max_value()), None);
//! ```
//!
//! ## Nightly features
//!
//! * The `RangeTo` type is a const generics enabled index that return arrays `[T; N]` instead of
//! slices. Due to recent advances in parameter deduction, the length parameter need not even be
//! named.
//!
#![cfg_attr(feature = "nightly", doc = "```")]
#![cfg_attr(not(feature = "nightly"), doc = "```ignore")]
//! # let slice = [0; 4];
//! use index_ext::array::RangeTo;
//! // Grab an array of three element from a slice.
//! let [r, g, b] = &slice[RangeTo];
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
//! [Idea]: An index type `InsertWith` for `HashMap` and `BTreeMap` that will construct an
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
#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;

mod sealed {
    /// Seals the `Int` extension trait.
    /// The methods added there are intended to be like inherent methods on the respective
    /// implementors which means additional implementors are not intended.
    pub trait Sealed {}
}

pub mod array;
pub mod int;
pub mod tag;

/// A trait for integer based indices.
///
/// Any integer can be used as a fallible index where a machine word can be used by first trying to
/// convert it into a `usize` and then indexing with the original method. From the point of the
/// user, the effect is not much different. If `10usize` is out-of-bounds then so is any other
/// integer representing the number `10`, no matter the allowed magnitude of its type. The same
/// holds for integers that permit negative indices.
///
/// The output type of the indexing operation is an element or a slice respectively.
///
/// This trait enables the generic [`Int::get_int`] method.
///
/// [`Int::get_int`]: trait.Int.html#fn.get_int
pub trait IntSliceIndex<T: ?Sized>: int::sealed::SealedSliceIndex<T> {}

/// An extension trait allowing slices to be indexed by everything convertible to `usize`.
pub trait Int: sealed::Sealed {
    /// Return a reference to an element or subslice with an integer index, or `None` if out of
    /// bounds.
    ///
    /// This works like [`slice::get`] but allows arbitrary integers to be used as indices. It will
    /// first try to convert them to an `usize`. For some types (`u8` and `u16`) this can never
    /// fail while other types may refer to negative indices or are out-of-range. These cases are
    /// treated as if the index was out-of-bounds due to the slice being too short.
    ///
    /// ## Examples
    ///
    /// ```
    /// # use index_ext::Int;
    /// let v = [10, 40, 30];
    /// assert_eq!(Some(&40), v.get_int(1u64));
    /// assert_eq!(Some(&[10, 40][..]), v.get_int(0u8..2));
    /// assert_eq!(None, v.get_int(3u8));
    /// assert_eq!(None, v.get_int(0u8..4));
    /// assert_eq!(None, v.get_int(-1i8));
    /// ```
    ///
    /// [`slice::get`]: https://doc.rust-lang.org/stable/std/primitive.slice.html#method.get
    fn get_int<T>(&self, idx: T) -> Option<&'_ <T as int::sealed::IntSliceIndex<Self>>::Output>
    where
        T: IntSliceIndex<Self>;

    /// Return a mutable reference to an element or subslice with an integer index, or `None` if
    /// out of bounds.
    ///
    /// This works like [`slice::get_mut`].
    ///
    /// ## Examples
    ///
    /// ```
    /// # use index_ext::Int;
    /// let x = &mut [0, 1, 2];
    ///
    /// if let Some(elem) = x.get_int_mut(1u8) {
    ///     *elem = 42;
    /// }
    /// assert_eq!(x, &[0, 42, 2]);
    /// ```
    ///
    /// [`slice::get_mut`]: https://doc.rust-lang.org/stable/std/primitive.slice.html#method.get_mut
    fn get_int_mut<T>(
        &mut self,
        idx: T,
    ) -> Option<&'_ mut <T as int::sealed::IntSliceIndex<Self>>::Output>
    where
        T: IntSliceIndex<Self>;

    /// Returns a reference to an element or subslice without doing bounds checking.
    ///
    /// ## Safety
    ///
    /// Like [`slice::get_unchecked`], calling this method with an out of bounds index is undefined
    /// behaviour. _This includes indices for which conversion to a `usize` fails._
    ///
    /// [`slice::get_unchecked`]: https://doc.rust-lang.org/stable/std/primitive.slice.html#method.get_unchecked
    ///
    /// ## Examples
    /// ```
    /// # use index_ext::Int;
    /// let x = &[1, 2, 4];
    ///
    /// unsafe {
    ///     assert_eq!(x.get_int_unchecked(1i8), &2);
    /// }
    /// ```
    unsafe fn get_int_unchecked<T>(
        &self,
        idx: T,
    ) -> &'_ <T as int::sealed::IntSliceIndex<Self>>::Output
    where
        T: IntSliceIndex<Self>;

    /// Returns a mutable reference to an element or subslice without doing bounds checking.
    ///
    /// ## Safety
    ///
    /// Like [`slice::get_unchecked_mut`], calling this method with an out of bounds index is undefined
    /// behaviour. _This includes indices for which conversion to a `usize` fails._
    ///
    /// ## Examples
    ///
    /// ```
    /// # use index_ext::Int;
    /// let x = &mut [1, 2, 4];
    ///
    /// unsafe {
    ///     let elem = x.get_int_unchecked_mut(1u64);
    ///     *elem = 13;
    /// }
    ///
    /// assert_eq!(x, &[1, 13, 4]);
    /// ```
    ///
    /// [`slice::get_unchecked_mut`]: https://doc.rust-lang.org/stable/std/primitive.slice.html#method.get_unchecked_mut
    unsafe fn get_int_unchecked_mut<T>(
        &mut self,
        idx: T,
    ) -> &'_ mut <T as int::sealed::IntSliceIndex<Self>>::Output
    where
        T: IntSliceIndex<Self>;
}

impl<U> sealed::Sealed for [U] {}

impl<U> Int for [U] {
    fn get_int<T>(&self, idx: T) -> Option<&'_ <T as int::sealed::IntSliceIndex<Self>>::Output>
    where
        T: IntSliceIndex<Self>,
    {
        <T as int::sealed::IntSliceIndex<Self>>::get(idx, self)
    }

    fn get_int_mut<T>(
        &mut self,
        idx: T,
    ) -> Option<&'_ mut <T as int::sealed::IntSliceIndex<Self>>::Output>
    where
        T: IntSliceIndex<Self>,
    {
        <T as int::sealed::IntSliceIndex<Self>>::get_mut(idx, self)
    }

    unsafe fn get_int_unchecked<T>(
        &self,
        idx: T,
    ) -> &'_ <T as int::sealed::IntSliceIndex<Self>>::Output
    where
        T: IntSliceIndex<Self>,
    {
        <T as int::sealed::IntSliceIndex<Self>>::get_unchecked(idx, self)
    }

    unsafe fn get_int_unchecked_mut<T>(
        &mut self,
        idx: T,
    ) -> &'_ mut <T as int::sealed::IntSliceIndex<Self>>::Output
    where
        T: IntSliceIndex<Self>,
    {
        <T as int::sealed::IntSliceIndex<Self>>::get_unchecked_mut(idx, self)
    }
}

impl sealed::Sealed for str {}

impl Int for str {
    fn get_int<T>(&self, idx: T) -> Option<&'_ <T as int::sealed::IntSliceIndex<Self>>::Output>
    where
        T: IntSliceIndex<Self>,
    {
        <T as int::sealed::IntSliceIndex<Self>>::get(idx, self)
    }

    fn get_int_mut<T>(
        &mut self,
        idx: T,
    ) -> Option<&'_ mut <T as int::sealed::IntSliceIndex<Self>>::Output>
    where
        T: IntSliceIndex<Self>,
    {
        <T as int::sealed::IntSliceIndex<Self>>::get_mut(idx, self)
    }

    unsafe fn get_int_unchecked<T>(
        &self,
        idx: T,
    ) -> &'_ <T as int::sealed::IntSliceIndex<Self>>::Output
    where
        T: IntSliceIndex<Self>,
    {
        <T as int::sealed::IntSliceIndex<Self>>::get_unchecked(idx, self)
    }

    unsafe fn get_int_unchecked_mut<T>(
        &mut self,
        idx: T,
    ) -> &'_ mut <T as int::sealed::IntSliceIndex<Self>>::Output
    where
        T: IntSliceIndex<Self>,
    {
        <T as int::sealed::IntSliceIndex<Self>>::get_unchecked_mut(idx, self)
    }
}

/// Convert an arbitrary integer into an index.
///
/// This method simply constructs an inner transparent wrapper struct `Int` but can be used as an
/// alternative which is imported with the same name, and at the same time, as the trait.
#[allow(non_snake_case)]
pub fn Int<T>(idx: T) -> int::Int<T> {
    int::Int(idx)
}

macro_rules! doctest_readme {
    { $content:expr } => {
        #[doc = $content] extern {}
    }
}

doctest_readme!(include_str!("../Readme.md"));

#[cfg(test)]
mod test {
    use super::Int;

    #[test]
    #[should_panic = "100"]
    fn panics_with_length_u32() {
        [0u8; 0][Int(100u32)];
    }

    #[test]
    #[should_panic = "100"]
    fn panics_with_length_u8() {
        [0u8; 0][Int(100u8)];
    }

    #[test]
    #[should_panic = "-1"]
    fn panics_with_length_i8() {
        [0u8; 0][Int(-1i8)];
    }

    #[test]
    #[should_panic = "100000000000000000000000000000000000000"]
    fn panics_with_length_u128() {
        [0u8; 0][Int(100_000_000_000_000_000_000_000_000_000_000_000_000u128)];
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
    fn unchecked() {
        let mut slice = [0u8, 1, 2, 3];
        macro_rules! assert_slice_eq {
            (@$slice:path, $idx:expr, $exp:expr) => {
                assert_eq!($slice[Int($idx)], $exp);
                assert_eq!(&mut $slice[Int($idx)], $exp);

                unsafe {
                    assert_eq!($slice.get_int_unchecked($idx), $exp);
                    assert_eq!($slice.get_int_unchecked_mut($idx), $exp);
                }
            };
            ($slice:path[idx], $result:expr, for idx in [$($idx:expr),*]) => {
                $(assert_slice_eq!(@$slice, $idx, $result);)*
            }
        }

        assert_slice_eq!(slice[idx], [1, 2],
            for idx in [1u8..3, 1i8..3, 1u16..3, 1i16..3, 1u32..3, 1i32..3, 1u64..3, 1i64..3]);
    }

    #[test]
    fn str_indices() {
        let text = "What if ascii still has it?";
        assert_eq!(text.get_int(8u8..13), Some("ascii"));
    }
}

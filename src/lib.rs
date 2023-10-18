//! Adds more index types, improving correctness and clarifying intent.
//!
//! The crate is separated by modules which each roughly explore one particular index-related idea.
//! As an overview, the main modules are:
//!
//! - In the [`mod@array`] module, a solution for repetitive try-into-unwrapping in the process of
//!   interpreting slices as fixed-width arrays is presented.
//! - In the [`int`] module, we explore numerical types with fallible conversion to indices on use,
//!   interpreting a failure as out-of-bounds.
//! - In the [`mem`] module, the efficient representation for the type intersection between
//!   integers and pointer sized indices is presented as a set of concrete types.
//! - In the [`tag`] module, we apply fancy type-level mechanisms to move the bounds check inherent
//!   in safe slice accesses from the usage site to the construction of the index. See in
//!   particular the Huffman example that demonstrates the optimization potential.
//!
//! Read the [`readme`] for some examples. In short:
//!
//! ```
//! use index_ext::{Intex, SliceIntExt};
//!
//! let fine = [0u8; 2][Intex(1u32)];
//! let also = [0u8; 2][Intex(1u128)];
//!
//! assert_eq!([0u8; 2].get_int(u128::max_value()), None);
//! ```
//!
//! ## Unfinished features
//!
//! The marker WIP means it is worked on, Planned that it might be worked on due to intrigue of the
//! author, and Idea itself is still unevaluated (looking for a usecase, for instance).
//!
//! `Planned`: An index type `CharAt(n: usize)` that dereferences to the characters of a string
//! _around_ a particular position, represented by a string wrapper that allows converting into a
//! `char`. In contrast to the standard operator, this would only panic for out-of-bounds
//! coordinates and thus match the main expectation with regards to `len`.
//!
//! `Idea`: Note that a generic `PrefixChars<N: usize>`, retrieving the first N characters, would
//! not be constant time which may be surprising if used in index position.
//!
//! `Idea`: An index type `InsertWith` for `HashMap` and `BTreeMap` that will construct an
//! element when an entry is missing, similar to C++, and thus be a panic free alternative. _Maybe_
//! we could index a `Vec<_>` with this type as well, extending as necessary, but this would again
//! not be constant time. The problem here is the super trait relationship `IndexMut: Index` which
//! might lead to many potential misuses. Also the common alternative of `entry.or_insert` is both
//! simple an robust already.
//!
//! `Idea`: An adapter `OrEmpty` that uses `get` internally and substitutes an empty slice instead
//! of panicking. Now this is maybe both clear and cute, I'd actually see some use here. It's
//! unclear for which types to provide it and if there's a SemVer risk.
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
#![deny(clippy::missing_safety_doc)]
#![deny(missing_docs)]
#![deny(unsafe_op_in_unsafe_fn)]

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod array;
pub mod int;
pub mod mem;
pub mod tag;

pub use array::ArrayPrefix;
pub use int::SliceIntExt;

/// Convert an arbitrary integer into an index.
///
/// This method simply constructs an inner transparent wrapper struct `Intex` but can be used as an
/// alternative which is imported with the same name, and at the same time, as the trait.
#[allow(non_snake_case)]
pub fn Intex<T>(idx: T) -> int::Intex<T> {
    int::Intex(idx)
}

macro_rules! doctest_readme {
    { $content:expr } => {
        /// A rendered version of the Readme file, documentation purpose only.
        ///
        #[doc = $content] pub mod readme {}
    }
}

#[cfg(doc)]
doctest_readme!(include_str!("../Readme.md"));

#[cfg(test)]
mod test {
    use super::{Intex, SliceIntExt};

    #[test]
    #[should_panic = "100"]
    fn panics_with_length_u32() {
        [0u8; 0][Intex(100u32)];
    }

    #[test]
    #[should_panic = "100"]
    fn panics_with_length_u8() {
        [0u8; 0][Intex(100u8)];
    }

    #[test]
    #[should_panic = "-1"]
    fn panics_with_length_i8() {
        [0u8; 0][Intex(-1i8)];
    }

    #[test]
    #[should_panic = "100000000000000000000000000000000000000"]
    fn panics_with_length_u128() {
        [0u8; 0][Intex(100_000_000_000_000_000_000_000_000_000_000_000_000u128)];
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
                assert_eq!($slice[Intex($idx)], $exp);
                assert_eq!(&mut $slice[Intex($idx)], $exp);

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

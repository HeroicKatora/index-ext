//! Integer wrappers that are constrained to the range of `usize` or `isize`.
//!
//! This module defines a number of wrappers around the basic integer types which ensure that the
//! stored value can be trivially converted to a `usize` without loss of data. That is these types
//! offer a getter that converts the number with `as usize` but otherwise they are ABI compatible
//! with their underlying integer type.
//!
//! # Usage
//!
//! These are best used in places where the ABI or layout of the type is important but there is a
//! security risk associated with having to write (fallible) conversions all the time. Consider the
//! case of a matrix where dimensions are stored as `u32` for compatibility reasons. We would now
//! like to allocate a buffer for it which requires calculating the number of elements as a `u64`
//! and then convert to `usize`. However, no matter in which number type you intend to store the
//! result you lose semantic meaning because there is no 'proof' attached to the value that it will
//! also fit into the other value range.
//!
//! ```
//! use index_ext::mem::Umem64;
//!
//! struct Matrix {
//!     width: u32,
//!     height: u32,
//! }
//!
//! # fn fake() -> Option<()> {
//! # let mat = Matrix { width: 0, height: 0 };
//! let elements = u64::from(mat.width) * u64::from(mat.height);
//! let length: Umem64 = Umem64::new(elements)?;
//!
//! let matrix = vec![0; length.get()];
//! # Some(()) }
//! ```
macro_rules! lossless_integer {
    (
        $(#[$attr:meta])*
        $sizet:ident $str_name:literal
        pub struct $name:ident ($under:ty)
    ) => {
        $(#[$attr])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        #[repr(transparent)]
        pub struct $name($under);

        impl $name {
            /// Wrap an integer if its value can be losslessly converted to `
            #[doc = $str_name]
            /// `.
            pub fn new(val: $under) -> Option<Self> {
                if <$sizet as core::convert::TryFrom<_>>::try_from(val).is_ok() {
                    Some($name(val))
                } else {
                    None
                }
            }

            /// Get the `
            #[doc = $str_name]
            /// ` value of the integer.
            pub fn get(self) -> $sizet {
                self.0 as $sizet
            }

            /// Get the inner value in the original type.
            pub fn into_inner(self) -> $under {
                self.0
            }
        }
    };
}

macro_rules! integer_mem {
    ($(#[$attr:meta])* pub struct $name:ident ($under:ty)) => {
        lossless_integer!($(#[$attr])*
        usize "usize"
        pub struct $name ($under));

        impl<T> core::ops::Index<$name> for [T] {
            type Output = T;
            fn index(&self, idx: $name) -> &Self::Output {
                &self[idx.get()]
            }
        }
    }
}

macro_rules! integer_diff {
    ($(#[$attr:meta])* pub struct $name:ident ($under:ty)) => {
        lossless_integer!($(#[$attr])*
        isize "isize"
        pub struct $name ($under));
    }
}

integer_mem!(
    /// An i8 that is also in the value range of a usize.
    pub struct Imem8(i8)
);

integer_mem!(
    /// A u8 that is also in the value range of a usize.
    pub struct Umem8(u8)
);

integer_mem!(
    /// An i16 that is also in the value range of a usize.
    pub struct Imem16(i16)
);

integer_mem!(
    /// A u16 that is also in the value range of a usize.
    pub struct Umem16(u16)
);

integer_mem!(
    /// An i32 that is also in the value range of a usize.
    pub struct Imem32(i32)
);

integer_mem!(
    /// A u32 that is also in the value range of a usize.
    pub struct Umem32(u32)
);

integer_mem!(
    /// An i64 that is also in the value range of a usize.
    pub struct Imem64(i64)
);

integer_mem!(
    /// A u64 that is also in the value range of a usize.
    pub struct Umem64(u64)
);

integer_mem!(
    /// An isize that is also in the value range of a usize.
    pub struct Imem(isize)
);

integer_diff!(
    /// An i8 that is also in the value range of an isize.
    pub struct Idiff8(i8)
);

integer_diff!(
    /// A u8 that is also in the value range of an isize.
    pub struct Udiff8(u8)
);

integer_diff!(
    /// An i16 that is also in the value range of an isize.
    pub struct Idiff16(i16)
);

integer_diff!(
    /// A u16 that is also in the value range of an isize.
    pub struct Udiff16(u16)
);

integer_diff!(
    /// An i32 that is also in the value range of an isize.
    pub struct Idiff32(i32)
);

integer_diff!(
    /// A u32 that is also in the value range of an isize.
    pub struct Udiff32(u32)
);

integer_diff!(
    /// An i64 that is also in the value range of an isize.
    pub struct Idiff64(i64)
);

integer_diff!(
    /// A u64 that is also in the value range of an isize.
    pub struct Udiff64(u64)
);

integer_diff!(
    /// A usize that is also in the value range of an isize.
    pub struct Udiff(usize)
);

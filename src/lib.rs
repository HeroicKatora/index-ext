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
#![no_std]
use core::convert::TryInto;
use core::num::TryFromIntError;
use core::ops::{Range, RangeFrom, RangeTo};
use core::slice::SliceIndex;

pub(crate) mod sealed {
    /// Using the actual ops::Index relies on this sealed trait.
    ///
    /// This is for two reasons. Firstly, it would be vastly more confusing than handling the result of
    /// fallible indexing. Secondly, the panic message is improved by mentioning the original inputs.
    /// But this requires the additional bounds of `Copy` and a panic handler, both of which are not
    /// available without specialization or adding additional trait bounds to the public interface. By
    /// not exposing this we can always relax this later when, and if, specialization becomes
    /// available to stable Rust.
    pub trait Sealed {
        fn copy(&self) -> Self;
        #[cold]
        fn panic_msg(limit: usize, idx: Self) -> !;
    }
}

pub mod idx {
    use core::convert::TryInto;
    use core::num::TryFromIntError;
    use core::slice::SliceIndex;

    use super::{sealed::Sealed, IntSliceIndex};

    /// An indexing adaptor for `TryInto`.
    ///
    /// This transparent wrapper allows any type to function as an index as long as it is fallibly
    /// convertible to a `usize`.
    ///
    /// Separating this from the main `IndexType` solves a coherence problem that would occurs when
    /// instantiating it with ranges: The standard library is permitted to add new impls of
    /// `TryInto<usize>`, for example even for `Range<usize>`. Hence, these two impls would overlap
    /// but we would like the first to have another return type than the second. The indirection
    /// over this type means that our impls are only generic for `TryIndex<T>` instead and do not
    /// overlap.
    #[repr(transparent)]
    pub struct TryIndex<T>(pub T);

    impl<T, U> IntSliceIndex<[U]> for TryIndex<T>
    where
        T: TryInto<usize>,
        T::Error: Into<TryFromIntError>,
    {
        type Index = usize;
        fn index(self) -> Result<usize, TryFromIntError> {
            match self.0.try_into() {
                Ok(idx) => Ok(idx),
                Err(err) => Err(err.into()),
            }
        }
    }

    impl<T, U> core::ops::Index<TryIndex<T>> for [U]
    where 
        T: TryInto<usize> + Sealed,
        T::Error: Into<TryFromIntError>,
    {
        type Output = U;
        fn index(&self, idx: TryIndex<T>) -> &U {
            let err = Sealed::copy(&idx.0);
            match IntSliceIndex::<Self>::index(idx) {
                Ok(element) => &self[element],
                Err(_) => Sealed::panic_msg(self.len(), err),
            }
        }
    }

    impl<T, U> core::ops::IndexMut<TryIndex<T>> for [U]
    where 
        T: TryInto<usize> + Sealed,
        T::Error: Into<TryFromIntError>,
    {
        fn index_mut(&mut self, idx: TryIndex<T>) -> &mut Self::Output {
            let err = Sealed::copy(&idx.0);
            let len = self.len();
            match IntSliceIndex::<Self>::index(idx) {
                Ok(element) => &mut self[element],
                Err(_) => Sealed::panic_msg(len, err),
            }
        }
    }

    /// An adaptor for `ops::Index` that uses this crate's `IntIndex` instead of the standard one.
    ///
    /// This is a transparent wrapper.
    #[repr(transparent)]
    pub struct IntIndex<T>(pub T);

    impl<T, U> core::ops::Index<IntIndex<T>> for [U]
    where 
        T: IntSliceIndex<[U]> + Sealed,
    {
        type Output = <T::Index as SliceIndex<[U]>>::Output;

        fn index(&self, idx: IntIndex<T>) -> &Self::Output {
            let err = Sealed::copy(&idx.0);
            match IntSliceIndex::index(idx.0) {
                Ok(element) => &self[element],
                Err(_) => Sealed::panic_msg(self.len(), err),
            }
        }
    }

    impl<T, U> core::ops::IndexMut<IntIndex<T>> for [U]
    where 
        T: IntSliceIndex<[U]> + Sealed,
    {
        fn index_mut(&mut self, idx: IntIndex<T>) -> &mut Self::Output {
            let err = Sealed::copy(&idx.0);
            let len = self.len();
            match IntSliceIndex::index(idx.0) {
                Ok(element) => &mut self[element],
                Err(_) => Sealed::panic_msg(len, err),
            }
        }
    }
}

pub trait IntSliceIndex<T: ?Sized> {
    type Index: SliceIndex<T>;
    fn index(self) -> Result<Self::Index, TryFromIntError>;
}

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

impl<U> IntIndex for [U] {
    fn get_int<T>(&self, idx: T)
        -> Option<&'_ <T::Index as SliceIndex<Self>>::Output>
    where
        T: IntSliceIndex<Self>,
    {
        self.get(IntSliceIndex::index(idx).ok()?)
    }

    fn get_int_mut<T>(&mut self, idx: T)
        -> Option<&'_ mut <T::Index as SliceIndex<Self>>::Output>
    where
        T: IntSliceIndex<Self>,
    {
        self.get_mut(IntSliceIndex::index(idx).ok()?)
    }
}

macro_rules! slice_index { 
($($t:ty),*) => {
    $(slice_index!(@$t);)*
};
(@$t:ty) => {
    impl<U> IntSliceIndex<[U]> for $t {
        type Index = usize;
        fn index(self) -> Result<usize, TryFromIntError> {
            Ok(self.try_into()?)
        }
    }
    
    impl<U> IntSliceIndex<[U]> for Range<$t> {
        type Index = Range<usize>;
        fn index(self) -> Result<Self::Index, TryFromIntError> {
            let Range { start, end } = self;
            let start: usize = start.try_into()?;
            let end: usize = end.try_into()?;
            Ok(start..end)
        }
    }
    
    impl<U> IntSliceIndex<[U]> for RangeTo<$t> {
        type Index = RangeTo<usize>;
        fn index(self) -> Result<Self::Index, TryFromIntError> {
            let end: usize = self.end.try_into()?;
            Ok(..end)
        }
    }
    
    impl<U> IntSliceIndex<[U]> for RangeFrom<$t> {
        type Index = RangeFrom<usize>;
        fn index(self) -> Result<Self::Index, TryFromIntError> {
            let start: usize = self.start.try_into()?;
            Ok(start..)
        }
    }

    impl sealed::Sealed for $t {
        #[inline(always)]
        fn copy(&self) -> Self { *self }
        #[cold]
        fn panic_msg(len: usize, index: Self) -> ! {
            panic!("index {} out of range for slice of length {}", index, len)
        }
    }

    impl sealed::Sealed for Range<$t> {
        #[inline(always)]
        fn copy(&self) -> Self { Range { .. *self } }
        #[cold]
        fn panic_msg(len: usize, index: Self) -> ! {
            panic!("index {} out of range for slice of length {}", index.end, len)
        }
    }

    impl sealed::Sealed for RangeFrom<$t> {
        #[inline(always)]
        fn copy(&self) -> Self { RangeFrom { .. *self } }
        #[cold]
        fn panic_msg(len: usize, index: Self) -> ! {
            panic!("index {} out of range for slice of length {}", index.start, len)
        }
    }

    impl sealed::Sealed for RangeTo<$t> {
        #[inline(always)]
        fn copy(&self) -> Self { RangeTo { .. *self } }
        #[cold]
        fn panic_msg(len: usize, index: Self) -> ! {
            panic!("index {} out of range for slice of length {}", index.end, len)
        }
    }
} }

slice_index!(u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize);

#[allow(non_snake_case)]
pub fn IntIndex<T>(idx: T) -> idx::IntIndex<T> {
    idx::IntIndex(idx)
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
}

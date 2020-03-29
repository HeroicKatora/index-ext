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
use core::num::TryFromIntError;
use core::ops::{Range, RangeFrom, RangeTo};
use core::convert::TryInto;

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
    use core::num::TryFromIntError;
    use core::convert::TryInto;

    use super::{sealed::Sealed, TrySliceIndex};

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

    impl<T, U> TrySliceIndex<[U]> for TryIndex<T>
    where
        T: TryInto<usize>,
    {
        type Output = U;
        type Error = T::Error;

        fn try_get(self, slice: &[U]) -> Result<&Self::Output, Self::Error> {
            let idx: usize = self.0.try_into()?;
            Ok(&slice[idx])
        }
        fn try_get_mut(self, slice: &mut [U]) -> Result<&mut Self::Output, Self::Error> {
            let idx: usize = self.0.try_into()?;
            Ok(&mut slice[idx])
        }
    }

    impl<T, U> core::ops::Index<TryIndex<T>> for [U]
    where 
        T: TryInto<usize> + Sealed,
    {
        type Output = U;
        fn index(&self, idx: TryIndex<T>) -> &U {
            let err = Sealed::copy(&idx.0);
            match TrySliceIndex::try_get(idx, self) {
                Ok(element) => element,
                Err(_) => Sealed::panic_msg(self.len(), err),
            }
        }
    }

    impl<T, U> core::ops::IndexMut<TryIndex<T>> for [U]
    where 
        T: TryInto<usize> + Sealed,
    {
        fn index_mut(&mut self, idx: TryIndex<T>) -> &mut Self::Output {
            let err = Sealed::copy(&idx.0);
            let len = self.len();
            match TrySliceIndex::try_get_mut(idx, self) {
                Ok(element) => element,
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
        T: TrySliceIndex<[U]> + Sealed,
        T::Error: Into<TryFromIntError>,
    {
        type Output = <T as TrySliceIndex<[U]>>::Output;

        fn index(&self, idx: IntIndex<T>) -> &Self::Output {
            let err = Sealed::copy(&idx.0);
            match TrySliceIndex::try_get(idx.0, self) {
                Ok(element) => element,
                Err(_) => Sealed::panic_msg(self.len(), err),
            }
        }
    }

    impl<T, U> core::ops::IndexMut<IntIndex<T>> for [U]
    where 
        T: TrySliceIndex<[U]> + Sealed,
        T::Error: Into<TryFromIntError>,
    {
        fn index_mut(&mut self, idx: IntIndex<T>) -> &mut Self::Output {
            let err = Sealed::copy(&idx.0);
            let len = self.len();
            match TrySliceIndex::try_get_mut(idx.0, self) {
                Ok(element) => element,
                Err(_) => Sealed::panic_msg(len, err),
            }
        }
    }
}

pub trait TrySliceIndex<T: ?Sized> {
    type Output: ?Sized;
    type Error;

    fn try_get(self, slice: &T) -> Result<&Self::Output, Self::Error>;
    fn try_get_mut(self, slice: &mut T) -> Result<&mut Self::Output, Self::Error>;
}

/// A trait for fallible indexing.
pub trait TryIndex {
    fn try_get<T>(&self, idx: T) -> Result<&T::Output, T::Error>
    where
        T: TrySliceIndex<Self>;

    fn try_get_mut<T>(&mut self, idx: T) -> Result<&mut T::Output, T::Error>
    where
        T: TrySliceIndex<Self>;
}

/// An extension trait allowing slices to be indexed by everything convertible to `usize`.
pub trait IntIndex {
    fn get_int<T>(&self, idx: T)
        -> Option<&'_ T::Output>
    where
        T: TrySliceIndex<Self>,
        T::Error: Into<TryFromIntError>;

    fn get_int_mut<T>(&mut self, idx: T)
        -> Option<&'_ mut T::Output>
    where
        T: TrySliceIndex<Self>,
        T::Error: Into<TryFromIntError>;
}

impl<U> IntIndex for [U] {
    fn get_int<T>(&self, idx: T)
        -> Option<&'_ T::Output>
    where
        T: TrySliceIndex<Self>,
        T::Error: Into<TryFromIntError>
    {
        TrySliceIndex::try_get(idx, self).ok()
    }

    fn get_int_mut<T>(&mut self, idx: T)
        -> Option<&'_ mut T::Output>
    where
        T: TrySliceIndex<Self>,
        T::Error: Into<TryFromIntError>
    {
        TrySliceIndex::try_get_mut(idx, self).ok()
    }
}

macro_rules! slice_index { 
($($t:ty,)*) => {
    $(slice_index!($t);)*
};
($t:ty) => {
    impl<U> TrySliceIndex<[U]> for $t {
        type Output = U;
        type Error = <$t as TryInto<usize>>::Error;
        fn try_get(self, slice: &[U]) -> Result<&Self::Output, Self::Error> {
            let idx: usize = self.try_into()?;
            Ok(&slice[idx])
        }
        fn try_get_mut(self, slice: &mut [U]) -> Result<&mut Self::Output, Self::Error> {
            let idx: usize = self.try_into()?;
            Ok(&mut slice[idx])
        }
    }
    
    impl<U> TrySliceIndex<[U]> for Range<$t> {
        type Output = [U];
        type Error = <$t as TryInto<usize>>::Error;
        fn try_get(self, slice: &[U]) -> Result<&Self::Output, Self::Error> {
            let Range { start, end } = self;
            let start: usize = start.try_into()?;
            let end: usize = end.try_into()?;
            Ok(&slice[start..end])
        }
        fn try_get_mut(self, slice: &mut [U]) -> Result<&mut Self::Output, Self::Error> {
            let Range { start, end } = self;
            let start: usize = start.try_into()?;
            let end: usize = end.try_into()?;
            Ok(&mut slice[start..end])
        }
    }
    
    impl<U> TrySliceIndex<[U]> for RangeTo<$t> {
        type Output = [U];
        type Error = <$t as TryInto<usize>>::Error;
        fn try_get(self, slice: &[U]) -> Result<&Self::Output, Self::Error> {
            let end: usize = self.end.try_into()?;
            Ok(&slice[..end])
        }
        fn try_get_mut(self, slice: &mut [U]) -> Result<&mut Self::Output, Self::Error> {
            let end: usize = self.end.try_into()?;
            Ok(&mut slice[..end])
        }
    }
    
    impl<U> TrySliceIndex<[U]> for RangeFrom<$t> {
        type Output = [U];
        type Error = <$t as TryInto<usize>>::Error;
        fn try_get(self, slice: &[U]) -> Result<&Self::Output, Self::Error> {
            let start: usize = self.start.try_into()?;
            Ok(&slice[start..])
        }
        fn try_get_mut(self, slice: &mut [U]) -> Result<&mut Self::Output, Self::Error> {
            let start: usize = self.start.try_into()?;
            Ok(&mut slice[start..])
        }
    }

    impl sealed::Sealed for $t {
        #[inline(always)]
        fn copy(&self) -> Self {
            *self
        }

        #[cold]
        fn panic_msg(len: usize, index: Self) -> ! {
            panic!("index {} out of range for slice of length {}", index, len)
        }
    }
} }

slice_index!(u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize,);

#[allow(non_snake_case)]
pub fn IntIndex<T>(idx: T) -> idx::IntIndex<T> {
    idx::IntIndex(idx)
}

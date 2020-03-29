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
//! use index_ext::Index;
//!
//! let fine = [0u8; 2][Index(1u32)];
//! let also = [0u8; 2][Index(1u128)];
//!
//! let fails = assert!([0u8; 2].index(u128::max_value()).is_none());
//! ```
#![no_std]
use core::ops::{Range, RangeFrom, RangeTo};
use core::convert::TryInto;

pub mod idx {
    use core::convert::TryInto;
    use super::SliceIndex;

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

    impl<T, U> SliceIndex<[U]> for TryIndex<T>
    where
        T: TryInto<usize>,
    {
        type Output = U;
        fn get(self, slice: &[U]) -> Option<&Self::Output> {
            let idx: usize = self.0.try_into().ok()?;
            Some(&slice[idx])
        }
        fn get_mut(self, slice: &mut [U]) -> Option<&mut Self::Output> {
            let idx: usize = self.0.try_into().ok()?;
            Some(&mut slice[idx])
        }
    }

    impl<T, U> core::ops::Index<TryIndex<T>> for [U]
    where 
        T: TryInto<usize>,
    {
        type Output = U;
        fn index(&self, idx: TryIndex<T>) -> &U {
            SliceIndex::get(idx, self).unwrap()
        }
    }

    impl<T, U> core::ops::IndexMut<TryIndex<T>> for [U]
    where 
        T: TryInto<usize>,
    {
        fn index_mut(&mut self, idx: TryIndex<T>) -> &mut Self::Output {
            SliceIndex::get_mut(idx, self).unwrap()
        }
    }

    /// An index that uses this crates `SliceIndex` instead of the standard one.
    ///
    /// This is a transparent wrapper.
    #[repr(transparent)]
    pub struct IndexType<T>(pub T);

    impl<T, U> core::ops::Index<IndexType<T>> for [U]
    where 
        T: SliceIndex<[U]>,
    {
        type Output = <T as SliceIndex<[U]>>::Output;
        fn index(&self, idx: IndexType<T>) -> &Self::Output {
            SliceIndex::get(idx.0, self).unwrap()
        }
    }

    impl<T, U> core::ops::IndexMut<IndexType<T>> for [U]
    where 
        T: SliceIndex<[U]>,
    {
        fn index_mut(&mut self, idx: IndexType<T>) -> &mut Self::Output {
            SliceIndex::get_mut(idx.0, self).unwrap()
        }
    }
}

pub trait SliceIndex<T: ?Sized> {
    type Output: ?Sized;

    fn get(self, slice: &T) -> Option<&Self::Output>;

    fn get_mut(self, slice: &mut T) -> Option<&mut Self::Output>;
}

pub trait Index {
    fn index<T: SliceIndex<Self>>(&self, idx: T)
        -> Option<&'_ T::Output>;
    fn index_mut<T: SliceIndex<Self>>(&mut self, idx: T)
        -> Option<&'_ mut T::Output>;
}

impl<U> Index for [U] {
    fn index<T: SliceIndex<Self>>(&self, idx: T)
        -> Option<&'_ T::Output>
    {
        SliceIndex::get(idx, self)
    }
    
    fn index_mut<T: SliceIndex<Self>>(&mut self, idx: T)
        -> Option<&'_ mut T::Output>
    {
        SliceIndex::get_mut(idx, self)
    }
}

macro_rules! slice_index { 
($($t:ty,)*) => {
    $(slice_index!($t);)*
};
($t:ty) => {
    impl<U> SliceIndex<[U]> for $t {
        type Output = U;
        fn get(self, slice: &[U]) -> Option<&Self::Output> {
            let idx: usize = self.try_into().ok()?;
            Some(&slice[idx])
        }
        fn get_mut(self, slice: &mut [U]) -> Option<&mut Self::Output> {
            let idx: usize = self.try_into().ok()?;
            Some(&mut slice[idx])
        }
    }
    
    impl<U> SliceIndex<[U]> for Range<$t> {
        type Output = [U];
        fn get(self, slice: &[U]) -> Option<&Self::Output> {
            let Range { start, end } = self;
            let start: usize = start.try_into().ok()?;
            let end: usize = end.try_into().ok()?;
            Some(&slice[start..end])
        }
        fn get_mut(self, slice: &mut [U]) -> Option<&mut Self::Output> {
            let Range { start, end } = self;
            let start: usize = start.try_into().ok()?;
            let end: usize = end.try_into().ok()?;
            Some(&mut slice[start..end])
        }
    }
    
    impl<U> SliceIndex<[U]> for RangeTo<$t> {
        type Output = [U];
        fn get(self, slice: &[U]) -> Option<&Self::Output> {
            let end: usize = self.end.try_into().ok()?;
            Some(&slice[..end])
        }
        fn get_mut(self, slice: &mut [U]) -> Option<&mut Self::Output> {
            let end: usize = self.end.try_into().ok()?;
            Some(&mut slice[..end])
        }
    }
    
    impl<U> SliceIndex<[U]> for RangeFrom<$t> {
        type Output = [U];
        fn get(self, slice: &[U]) -> Option<&Self::Output> {
            let start: usize = self.start.try_into().ok()?;
            Some(&slice[start..])
        }
        fn get_mut(self, slice: &mut [U]) -> Option<&mut Self::Output> {
            let start: usize = self.start.try_into().ok()?;
            Some(&mut slice[start..])
        }
    }
} }

slice_index!(u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize,);

#[allow(non_snake_case)]
pub fn Index<T>(idx: T) -> idx::IndexType<T> {
    idx::IndexType(idx)
}

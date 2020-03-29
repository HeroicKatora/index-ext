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

mod idx {
    use core::convert::TryInto;
    pub struct IndexType<T>(pub T);

    impl<T, U> core::ops::Index<IndexType<T>> for [U]
    where 
        T: TryInto<usize>,
    {
        type Output = U;
        fn index(&self, idx: IndexType<T>) -> &U {
            Index::index(self, idx.0).unwrap()
        }
    }
    
    pub trait SliceIndex<T: ?Sized> {
        type Output: ?Sized;
        fn get(self, slice: &T) -> Option<&Self::Output>;
        fn get_mut(self, slice: &mut T) -> Option<&mut Self::Output>;
    }
    
    impl<T, U> SliceIndex<[U]> for T
    where 
        T: TryInto<usize>,
    {
        type Output = U;
        fn get(self, slice: &[U]) -> Option<&Self::Output> {
            let idx = self.try_into().ok()?;
            Some(&slice[idx])
        }
        fn get_mut(self, slice: &mut [U]) -> Option<&mut Self::Output> {
            let idx = self.try_into().ok()?;
            Some(&mut slice[idx])
        }
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
}

pub use idx::{Index};
use idx::IndexType;

#[allow(non_snake_case)]
pub fn Index<T>(idx: T) -> IndexType<T> {
    IndexType(idx)
}

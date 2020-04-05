use core::ops::{Range, RangeTo, RangeFrom};
use core::hint::unreachable_unchecked;
use core::convert::TryInto;
use core::num::TryFromIntError;
use core::slice::SliceIndex;

use super::IntSliceIndex;
use self::sealed::{IndexSealed, IntoIntIndex};

/// Sealed traits for making `Int` work as an index, without exposing too much.
///
/// ## Navigating the jungle of traits
/// The main point here is to properly seal the traits. Parts of this are meant to be adopted by
/// `core` at some point, this prevents some unwanted usage. Also note that user defined types
/// convertible with `TryFromIntError` _should_ require slightly more ceremony.
///
/// So the `IntSliceIndex` is a parallel of `core::slice::SliceIndex` and inherited from the
/// exposed `crate::IntSliceIndex`. It also contains the interface which we use internally. We
/// can't define unstable methods, and methods would be inherited despite the hidden sealed trait.
/// 
/// ```
/// mod sealed {
///     pub trait Seal {
///         fn can_be_observed(&self);
///     }
/// }
///
/// trait Public: sealed::Seal {}
///
/// fn with_public<T: Public>(t: &T) {
///     t.can_be_observed();
/// }
/// ```
///
/// To work around this issue, we use two sealed traits with the same symbols. As neither can be
/// named the necessary disambiguation can not be performed in a downstream crate.
pub(crate) mod sealed {
    use core::num::TryFromIntError;

    /// A trait abstracting slice independent index behaviour, `ops::Index` can use on this.
    ///
    /// This is for two reasons. The panic message is improved by mentioning the original inputs.
    /// But this requires the additional bounds of `Copy`, which is not available for `Range` due
    /// to historical issues. By not exposing this we can always relax this later when, and if,
    /// specialization becomes available to stable Rust.
    pub trait IndexSealed {
        /// Punts the `Copy` bound to the implementor.
        fn copy(&self) -> Self;
        #[cold]
        fn panic_msg(limit: usize, idx: Self) -> !;
    }

    /// Provide one canonical conversion to an index.
    ///
    /// We use this converter to provide the methods of `IntSliceIndex` in the macro expanded
    /// implementation.
    pub trait IntoIntIndex {
        type IntoIndex;
        fn index(self) -> Result<Self::IntoIndex, TryFromIntError>;
    }

    /// Defines actual indexing on a potentially unsized type.
    ///
    /// This is sealed as well, as it contains the otherwise exposed `Index` item whose bounds we
    /// may later want to adjust.
    pub trait IntSliceIndex<T: ?Sized>: Sized {
        type Output: ?Sized;
        fn get(self, slice: &T) -> Option<&Self::Output>;
        fn get_mut(self, slice: &mut T) -> Option<&mut Self::Output>;
        unsafe fn get_unchecked(self, slice: &T) -> &Self::Output;
        unsafe fn get_unchecked_mut(self, slice: &mut T) -> &mut Self::Output;
        fn index(self, slice: &T) -> &Self::Output;
        fn index_mut(self, slice: &mut T) -> &mut Self::Output;
    }

    /// Stops downstream from using the `IntSliceIndex` methods and associate type by having a
    /// redundant pair of the same definitions. Methods do not have the same result type as this
    /// does not influence type deduction and makes it clear that _we_ should never call them.
    /// Hence, all methods provided here are actually unreachable.
    pub trait SealedSliceIndex<T: ?Sized>: IntSliceIndex<T> {
        type Output: ?Sized;
        fn get(self, _: &T) -> ! { unreachable!() }
        fn get_mut(self, _: &mut T) -> ! { unreachable!() }
        unsafe fn get_unchecked(self, _: &T) -> ! { unreachable!() }
        unsafe fn get_unchecked_mut(self, _: &mut T) -> ! { unreachable!() }
        fn index(self, _: &T) -> ! { unreachable!() }
        fn index_mut(self, _: &mut T) -> ! { unreachable!() }
    }

    impl<U: ?Sized, T: IntSliceIndex<U>> SealedSliceIndex<U> for T {
        type Output = <Self as IntSliceIndex<U>>::Output;
    }
}

/// An indexing adaptor for `TryInto`.
///
/// This transparent wrapper allows any type to function as an index as long as it is fallibly
/// convertible to a `usize`. Contrary to the simple integer types, the implementation of
/// `get_unchecked` methods will _not_ unsafely assume that the conversion itself can't fail, only
/// that the resulting index is in-bounds.
///
/// Separating this from the main `IndexType` solves a coherence problem that would occurs when
/// instantiating it with ranges: The standard library is permitted to add new impls of
/// `TryInto<usize>`, for example even for `Range<usize>`. Hence, these two impls would overlap
/// but we would like the first to have another return type than the second. The indirection
/// over this type means that our impls are only generic for `TryIndex<T>` instead and do not
/// overlap.
#[repr(transparent)]
pub struct TryIndex<T>(pub T);

impl<T> TryIndex<T>
where
    T: TryInto<usize>,
    T::Error: Into<TryFromIntError>,
{
    fn as_int_index(self) -> usize {
        match self.0.try_into() {
            Ok(idx) => idx,
            Err(_) => panic!("Invalid index"),
        }
    }
}

impl<T> IntoIntIndex for TryIndex<T>
where
    T: TryInto<usize>,
    T::Error: Into<TryFromIntError>,
{
    type IntoIndex = usize;
    fn index(self) -> Result<usize, TryFromIntError> {
        self.0.try_into().map_err(Into::into)
    }
}

impl<T, U> sealed::IntSliceIndex<[U]> for TryIndex<T>
where
    T: TryInto<usize>,
    T::Error: Into<TryFromIntError>,
{
    type Output = U;
    fn get(self, slice: &[U]) -> Option<&Self::Output> {
        match IntoIntIndex::index(self) {
            Ok(idx) => slice.get(idx),
            Err(_) => None,
        }
    }
    fn get_mut(self, slice: &mut [U]) -> Option<&mut Self::Output> {
        match IntoIntIndex::index(self) {
            Ok(idx) => slice.get_mut(idx),
            Err(_) => None,
        }
    }
    unsafe fn get_unchecked(self, slice: &[U]) -> &Self::Output {
        // Explicitly do __NOT__ make the conversion itself unchecked.
        slice.get_unchecked(self.as_int_index())
    }
    unsafe fn get_unchecked_mut(self, slice: &mut [U]) -> &mut Self::Output {
        // Explicitly do __NOT__ make the conversion itself unchecked.
        slice.get_unchecked_mut(self.as_int_index())
    }
    fn index(self, slice: &[U]) -> &Self::Output {
        &slice[self.as_int_index()]
    }
    fn index_mut(self, slice: &mut [U]) -> &mut Self::Output {
        &mut slice[self.as_int_index()]
    }
}

impl<T, U> IntSliceIndex<[U]> for TryIndex<T>
where
    T: TryInto<usize>,
    T::Error: Into<TryFromIntError>,
{}

impl<T, U> core::ops::Index<TryIndex<T>> for [U]
where 
    T: TryInto<usize> + IndexSealed,
    T::Error: Into<TryFromIntError>,
{
    type Output = U;
    fn index(&self, idx: TryIndex<T>) -> &U {
        sealed::IntSliceIndex::index(idx, self)
    }
}

impl<T, U> core::ops::IndexMut<TryIndex<T>> for [U]
where 
    T: TryInto<usize> + IndexSealed,
    T::Error: Into<TryFromIntError>,
{
    fn index_mut(&mut self, idx: TryIndex<T>) -> &mut Self::Output {
        sealed::IntSliceIndex::index_mut(idx, self)
    }
}

/// An adaptor for `ops::Index` that uses this crate's `IntIndex` instead of the standard one.
///
/// This is a transparent wrapper.
#[repr(transparent)]
pub struct Int<T>(pub T);

impl<T, U> core::ops::Index<Int<T>> for [U]
where 
    T: IntSliceIndex<[U]> + IndexSealed,
{
    type Output = <T as sealed::IntSliceIndex<[U]>>::Output;

    fn index(&self, idx: Int<T>) -> &Self::Output {
        <T as sealed::IntSliceIndex<[U]>>::index(idx.0, self)
    }
}

impl<T, U> core::ops::IndexMut<Int<T>> for [U]
where 
    T: IntSliceIndex<[U]> + IndexSealed,
{
    fn index_mut(&mut self, idx: Int<T>) -> &mut Self::Output {
        <T as sealed::IntSliceIndex<[U]>>::index_mut(idx.0, self)
    }
}

// Core implementations for the basede types. We implement the `IntoIntIndex` trait for generic
// types so we can reuse them in the concrete macro-derived impls of the sealed IntSliceIndex
// trait.

impl<T: TryInto<usize>> sealed::IntoIntIndex for Range<T>
where
    TryFromIntError: From<T::Error>,
{
    type IntoIndex = Range<usize>;
    fn index(self) -> Result<Range<usize>, TryFromIntError> {
        let Range { start, end } = self;
        let start: usize = start.try_into()?;
        let end: usize = end.try_into()?;
        Ok(start..end)
    }
}

impl<T: TryInto<usize>> sealed::IntoIntIndex for RangeTo<T>
where
    TryFromIntError: From<T::Error>,
{
    type IntoIndex = RangeTo<usize>;
    fn index(self) -> Result<RangeTo<usize>, TryFromIntError> {
        let end: usize = self.end.try_into()?;
        Ok(..end)
    }
}

impl<T: TryInto<usize>> sealed::IntoIntIndex for RangeFrom<T>
where
    TryFromIntError: From<T::Error>,
{
    type IntoIndex = RangeFrom<usize>;
    fn index(self) -> Result<RangeFrom<usize>, TryFromIntError> {
        let start: usize = self.start.try_into()?;
        Ok(start..)
    }
}

macro_rules! slice_index { 
($($t:ty),*) => {
    $(slice_index!(@$t);)*
};
(@IntSliceIndex<[U]> for $t:ty: with IntoIntIndex) => {
    impl<U> sealed::IntSliceIndex<[U]> for $t {
        type Output = <<Self as sealed::IntoIntIndex>::IntoIndex as SliceIndex<[U]>>::Output;
        fn get(self, slice: &[U]) -> Option<&Self::Output> {
            match IntoIntIndex::index(self) {
                Ok(idx) => slice.get(idx),
                Err(_) => None,
            }
        }
        fn get_mut(self, slice: &mut [U]) -> Option<&mut Self::Output> {
            match IntoIntIndex::index(self) {
                Ok(idx) => slice.get_mut(idx),
                Err(_) => None,
            }
        }
        unsafe fn get_unchecked(self, slice: &[U]) -> &Self::Output {
            match IntoIntIndex::index(self) {
                Ok(idx) => slice.get_unchecked(idx),
                Err(_) => unreachable_unchecked(),
            }
        }
        unsafe fn get_unchecked_mut(self, slice: &mut [U]) -> &mut Self::Output {
            match IntoIntIndex::index(self) {
                Ok(idx) => slice.get_unchecked_mut(idx),
                Err(_) => unreachable_unchecked(),
            }
        }
        fn index(self, slice: &[U]) -> &Self::Output {
            match sealed::IntSliceIndex::get(IndexSealed::copy(&self), slice) {
                Some(output) => output,
                None => IndexSealed::panic_msg(slice.len(), self),
            }
        }
        fn index_mut(self, slice: &mut [U]) -> &mut Self::Output {
            let len = slice.len();
            match sealed::IntSliceIndex::get_mut(IndexSealed::copy(&self), slice) {
                Some(output) => output,
                None => IndexSealed::panic_msg(len, self),
            }
        }
    }
};
(@IntSliceIndex<str> for $t:ty: with IntoIntIndex) => {
    impl sealed::IntSliceIndex<str> for $t {
        type Output = <<Self as sealed::IntoIntIndex>::IntoIndex as SliceIndex<str>>::Output;
        fn get(self, slice: &str) -> Option<&Self::Output> {
            match IntoIntIndex::index(self) {
                Ok(idx) => slice.get(idx),
                Err(_) => None,
            }
        }
        fn get_mut(self, slice: &mut str) -> Option<&mut Self::Output> {
            match IntoIntIndex::index(self) {
                Ok(idx) => slice.get_mut(idx),
                Err(_) => None,
            }
        }
        unsafe fn get_unchecked(self, slice: &str) -> &Self::Output {
            match IntoIntIndex::index(self) {
                Ok(idx) => slice.get_unchecked(idx),
                Err(_) => unreachable_unchecked(),
            }
        }
        unsafe fn get_unchecked_mut(self, slice: &mut str) -> &mut Self::Output {
            match IntoIntIndex::index(self) {
                Ok(idx) => slice.get_unchecked_mut(idx),
                Err(_) => unreachable_unchecked(),
            }
        }
        fn index(self, slice: &str) -> &Self::Output {
            match sealed::IntSliceIndex::get(IndexSealed::copy(&self), slice) {
                Some(output) => output,
                None => IndexSealed::panic_msg(slice.len(), self),
            }
        }
        fn index_mut(self, slice: &mut str) -> &mut Self::Output {
            let len = slice.len();
            match sealed::IntSliceIndex::get_mut(IndexSealed::copy(&self), slice) {
                Some(output) => output,
                None => IndexSealed::panic_msg(len, self),
            }
        }
    }
};
(@$t:ty) => {
    impl sealed::IntoIntIndex for $t {
        type IntoIndex = usize;
        fn index(self) -> Result<usize, TryFromIntError> {
            Ok(self.try_into()?)
        }
    }

    impl sealed::IndexSealed for $t {
        #[inline(always)]
        fn copy(&self) -> Self { *self }
        #[cold]
        fn panic_msg(len: usize, index: Self) -> ! {
            panic!("index {} out of range for slice of length {}", index, len)
        }
    }

    impl sealed::IndexSealed for Range<$t> {
        #[inline(always)]
        fn copy(&self) -> Self { Range { .. *self } }
        #[cold]
        fn panic_msg(len: usize, index: Self) -> ! {
            panic!("index {} out of range for slice of length {}", index.end, len)
        }
    }

    impl sealed::IndexSealed for RangeFrom<$t> {
        #[inline(always)]
        fn copy(&self) -> Self { RangeFrom { .. *self } }
        #[cold]
        fn panic_msg(len: usize, index: Self) -> ! {
            panic!("index {} out of range for slice of length {}", index.start, len)
        }
    }

    impl sealed::IndexSealed for RangeTo<$t> {
        #[inline(always)]
        fn copy(&self) -> Self { RangeTo { .. *self } }
        #[cold]
        fn panic_msg(len: usize, index: Self) -> ! {
            panic!("index {} out of range for slice of length {}", index.end, len)
        }
    }

    slice_index!(@IntSliceIndex<[U]> for $t: with IntoIntIndex);
    slice_index!(@IntSliceIndex<[U]> for Range<$t>: with IntoIntIndex);
    slice_index!(@IntSliceIndex<[U]> for RangeTo<$t>: with IntoIntIndex);
    slice_index!(@IntSliceIndex<[U]> for RangeFrom<$t>: with IntoIntIndex);
    slice_index!(@IntSliceIndex<str> for Range<$t>: with IntoIntIndex);
    slice_index!(@IntSliceIndex<str> for RangeTo<$t>: with IntoIntIndex);
    slice_index!(@IntSliceIndex<str> for RangeFrom<$t>: with IntoIntIndex);

    impl<U> IntSliceIndex<[U]> for $t {}
    impl<U> IntSliceIndex<[U]> for Range<$t> {}
    impl<U> IntSliceIndex<[U]> for RangeTo<$t> {}
    impl<U> IntSliceIndex<[U]> for RangeFrom<$t> {}

    impl IntSliceIndex<str> for Range<$t> {}
    impl IntSliceIndex<str> for RangeTo<$t> {}
    impl IntSliceIndex<str> for RangeFrom<$t> {}
} }

slice_index!(u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize);

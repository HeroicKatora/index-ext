use core::ops::{Range, RangeTo, RangeFrom};
use core::convert::TryInto;
use core::num::TryFromIntError;
use core::slice::SliceIndex;

use super::{IntSliceIndex, sealed::Same};
use self::sealed::{IndexSealed, IntoIntIndex};

pub(crate) mod sealed {
    use core::slice::SliceIndex;
    use core::num::TryFromIntError;
    use crate::sealed::Same;

    /// Using the actual ops::Index relies on this sealed trait.
    ///
    /// This is for two reasons. Firstly, it would be vastly more confusing than handling the result of
    /// fallible indexing. Secondly, the panic message is improved by mentioning the original inputs.
    /// But this requires the additional bounds of `Copy` and a panic handler, both of which are not
    /// available without specialization or adding additional trait bounds to the public interface. By
    /// not exposing this we can always relax this later when, and if, specialization becomes
    /// available to stable Rust.
    pub trait IndexSealed {
        /// Punts the `Copy` bound to the implementor.
        fn copy(&self) -> Self;
        #[cold]
        fn panic_msg(limit: usize, idx: Self) -> !;
    }

    /// Makes it so there is one canonical conversion to an index.
    ///
    /// With `feature(associated_type_bounds)` we could then derive the trait for `IntSliceIndex`
    /// while simultaneously asserting that the `Index: SliceIndex<T>`. However, for the moment
    /// this is not possible so we instead use another trait, `Same<T, U>`, to perform that
    /// conversion that is only a no-op.
    ///
    /// This implementation trouble motivates keeping the trait `IntSliceIndex` sealed.
    pub trait IntoIntIndex {
        type IntoIndex;
        fn index(self) -> Result<Self::IntoIndex, TryFromIntError>;
    }

    /// Defines actual indexing on a potentially unsized type.
    ///
    /// This is sealed as well, as it contains the otherwise exposed `Index` item whose bounds we
    /// may later want to adjust.
    pub trait IntSliceIndex<T: ?Sized>: IntoIntIndex {
        type Index: SliceIndex<T> + Same<<Self as IntoIntIndex>::IntoIndex>;
    }
}

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
    type Index = usize;
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
        let err = IndexSealed::copy(&idx.0);
        match IntoIntIndex::index(idx) {
            Ok(element) => &self[element],
            Err(_) => IndexSealed::panic_msg(self.len(), err),
        }
    }
}

impl<T, U> core::ops::IndexMut<TryIndex<T>> for [U]
where 
    T: TryInto<usize> + IndexSealed,
    T::Error: Into<TryFromIntError>,
{
    fn index_mut(&mut self, idx: TryIndex<T>) -> &mut Self::Output {
        let err = IndexSealed::copy(&idx.0);
        let len = self.len();
        match IntoIntIndex::index(idx) {
            Ok(element) => &mut self[element],
            Err(_) => IndexSealed::panic_msg(len, err),
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
    T: IntSliceIndex<[U]> + IndexSealed,
{
    type Output = <T::Index as SliceIndex<[U]>>::Output;

    fn index(&self, idx: IntIndex<T>) -> &Self::Output {
        let err = IndexSealed::copy(&idx.0);
        match IntoIntIndex::index(idx.0) {
            Ok(element) => &self[<T::Index as Same<_>>::identity(element)],
            Err(_) => IndexSealed::panic_msg(self.len(), err),
        }
    }
}

impl<T, U> core::ops::IndexMut<IntIndex<T>> for [U]
where 
    T: IntSliceIndex<[U]> + IndexSealed,
{
    fn index_mut(&mut self, idx: IntIndex<T>) -> &mut Self::Output {
        let err = IndexSealed::copy(&idx.0);
        let len = self.len();
        match IntoIntIndex::index(idx.0) {
            Ok(element) => &mut self[<T::Index as Same<_>>::identity(element)],
            Err(_) => IndexSealed::panic_msg(len, err),
        }
    }
}

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
(@$t:ty) => {
    impl sealed::IntoIntIndex for $t {
        type IntoIndex = usize;
        fn index(self) -> Result<usize, TryFromIntError> {
            Ok(self.try_into()?)
        }
    }

    impl<U> sealed::IntSliceIndex<[U]> for $t {
        type Index = usize;
    }
    impl<U> IntSliceIndex<[U]> for $t {}
    
    impl<U> sealed::IntSliceIndex<[U]> for Range<$t> {
        type Index = Range<usize>;
    }
    impl<U> IntSliceIndex<[U]> for Range<$t> {}
    
    impl<U> sealed::IntSliceIndex<[U]> for RangeTo<$t> {
        type Index = RangeTo<usize>;
    }
    impl<U> IntSliceIndex<[U]> for RangeTo<$t> {}
    
    impl<U> sealed::IntSliceIndex<[U]> for RangeFrom<$t> {
        type Index = RangeFrom<usize>;
    }
    impl<U> IntSliceIndex<[U]> for RangeFrom<$t> {}
    
    impl sealed::IntSliceIndex<str> for Range<$t> {
        type Index = Range<usize>;
    }
    impl IntSliceIndex<str> for Range<$t> {}
    
    impl sealed::IntSliceIndex<str> for RangeTo<$t> {
        type Index = RangeTo<usize>;
    }
    impl IntSliceIndex<str> for RangeTo<$t> {}
    
    impl sealed::IntSliceIndex<str> for RangeFrom<$t> {
        type Index = RangeFrom<usize>;
    }
    impl IntSliceIndex<str> for RangeFrom<$t> {}

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
} }

slice_index!(u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize);

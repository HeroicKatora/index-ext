//! Defines wrappers around standard integers to use the as indices.
use core::convert::TryInto;
use core::hint::unreachable_unchecked;
use core::num::TryFromIntError;
/// Defines helper types for more integer indices.
///
/// There are helpers for adapting indices to implement the standard `ops::Index`/`ops::IndexMut`
/// or the crate-wide [`IntSliceIndex`] respectively.
///
/// * [`TryIndex`] uses `TryInto<usize>` to convert an type into an index, slightly making them
///   more convenient to use where the error conditions have been checked through external means or
///   where such panicking is permissible.
/// * [`Intex`] wraps an implementor of [`IntSliceIndex`] to turn it into an implementor of
///   `ops::Index` and `ops::IndexMut` as well.
///
/// [`Intex`]: struct.Intex.html
/// [`IntSliceIndex`]: ../trait.IntSliceIndex.html
/// [`TryIndex`]: struct.TryIndex.html
use core::ops::{Range, RangeFrom, RangeTo};
use core::slice::SliceIndex;

use self::sealed::{IndexSealed, IntoIntIndex};

/// An extension trait allowing slices to be indexed by everything convertible to `usize`.
pub trait SliceIntExt: sealed::SealedSliceIntExt {
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
    /// # use index_ext::SliceIntExt;
    /// let v = [10, 40, 30];
    /// assert_eq!(Some(&40), v.get_int(1u64));
    /// assert_eq!(Some(&[10, 40][..]), v.get_int(0u8..2));
    /// assert_eq!(None, v.get_int(3u8));
    /// assert_eq!(None, v.get_int(0u8..4));
    /// assert_eq!(None, v.get_int(-1i8));
    /// ```
    ///
    /// [`slice::get`]: https://doc.rust-lang.org/stable/std/primitive.slice.html#method.get
    fn get_int<T>(&self, idx: T) -> Option<&'_ <T as sealed::IntSliceIndex<Self>>::Output>
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
    /// # use index_ext::SliceIntExt;
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
    ) -> Option<&'_ mut <T as sealed::IntSliceIndex<Self>>::Output>
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
    /// # use index_ext::SliceIntExt;
    /// let x = &[1, 2, 4];
    ///
    /// unsafe {
    ///     assert_eq!(x.get_int_unchecked(1i8), &2);
    /// }
    /// ```
    unsafe fn get_int_unchecked<T>(&self, idx: T) -> &'_ <T as sealed::IntSliceIndex<Self>>::Output
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
    /// # use index_ext::SliceIntExt;
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
    ) -> &'_ mut <T as sealed::IntSliceIndex<Self>>::Output
    where
        T: IntSliceIndex<Self>;
}

/// A trait for mathematical integer based indices.
///
/// Any integer can be used as a fallible index where a machine word can be used by first trying to
/// convert it into a `usize` and then indexing with the original method. From the point of the
/// user, the effect is not much different. If `10usize` is out-of-bounds then so is any other
/// integer representing the number `10`, no matter the allowed magnitude of its type. The same
/// holds for integers that permit negative indices.
///
/// The output type of the indexing operation is an element or a slice respectively.
///
/// This trait enables the generic [`SliceIntExt::get_int`] method.
///
/// [`SliceIntExt::get_int`]: trait.Intex.html#fn.get_int
pub trait IntSliceIndex<T: ?Sized>: sealed::SealedSliceIndex<T> {}

/// Sealed traits for making `Intex` work as an index, without exposing too much.
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

    /// Seals the `Intex` extension trait.
    /// The methods added there are intended to be like inherent methods on the respective
    /// implementors which means additional implementors are not intended.
    pub trait SealedSliceIntExt {}

    /// Stops downstream from using the `IntSliceIndex` methods and associate type by having a
    /// redundant pair of the same definitions. Methods do not have the same result type as this
    /// does not influence type deduction and makes it clear that _we_ should never call them.
    /// Hence, all methods provided here are actually unreachable.
    pub trait SealedSliceIndex<T: ?Sized>: IntSliceIndex<T> {
        type Output: ?Sized;
        fn get(self, _: &T) -> ! {
            unreachable!()
        }
        fn get_mut(self, _: &mut T) -> ! {
            unreachable!()
        }
        unsafe fn get_unchecked(self, _: &T) -> ! {
            unreachable!()
        }
        unsafe fn get_unchecked_mut(self, _: &mut T) -> ! {
            unreachable!()
        }
        fn index(self, _: &T) -> ! {
            unreachable!()
        }
        fn index_mut(self, _: &mut T) -> ! {
            unreachable!()
        }
    }

    impl<U: ?Sized, T: IntSliceIndex<U>> SealedSliceIndex<U> for T {
        type Output = <Self as IntSliceIndex<U>>::Output;
    }
}

impl<U> sealed::SealedSliceIntExt for [U] {}

impl<U> SliceIntExt for [U] {
    fn get_int<T>(&self, idx: T) -> Option<&'_ <T as sealed::IntSliceIndex<Self>>::Output>
    where
        T: IntSliceIndex<Self>,
    {
        <T as sealed::IntSliceIndex<Self>>::get(idx, self)
    }

    fn get_int_mut<T>(
        &mut self,
        idx: T,
    ) -> Option<&'_ mut <T as sealed::IntSliceIndex<Self>>::Output>
    where
        T: IntSliceIndex<Self>,
    {
        <T as sealed::IntSliceIndex<Self>>::get_mut(idx, self)
    }

    unsafe fn get_int_unchecked<T>(&self, idx: T) -> &'_ <T as sealed::IntSliceIndex<Self>>::Output
    where
        T: IntSliceIndex<Self>,
    {
        // Safety: Propagates the requirements from the caller that this is a valid index.
        unsafe { <T as sealed::IntSliceIndex<Self>>::get_unchecked(idx, self) }
    }

    unsafe fn get_int_unchecked_mut<T>(
        &mut self,
        idx: T,
    ) -> &'_ mut <T as sealed::IntSliceIndex<Self>>::Output
    where
        T: IntSliceIndex<Self>,
    {
        // Safety: Propagates the requirements from the caller that this is a valid index.
        unsafe { <T as sealed::IntSliceIndex<Self>>::get_unchecked_mut(idx, self) }
    }
}

impl sealed::SealedSliceIntExt for str {}

impl SliceIntExt for str {
    fn get_int<T>(&self, idx: T) -> Option<&'_ <T as sealed::IntSliceIndex<Self>>::Output>
    where
        T: IntSliceIndex<Self>,
    {
        <T as sealed::IntSliceIndex<Self>>::get(idx, self)
    }

    fn get_int_mut<T>(
        &mut self,
        idx: T,
    ) -> Option<&'_ mut <T as sealed::IntSliceIndex<Self>>::Output>
    where
        T: IntSliceIndex<Self>,
    {
        <T as sealed::IntSliceIndex<Self>>::get_mut(idx, self)
    }

    unsafe fn get_int_unchecked<T>(&self, idx: T) -> &'_ <T as sealed::IntSliceIndex<Self>>::Output
    where
        T: IntSliceIndex<Self>,
    {
        // Safety: Propagates the requirements from the caller that this is a valid index.
        unsafe { <T as sealed::IntSliceIndex<Self>>::get_unchecked(idx, self) }
    }

    unsafe fn get_int_unchecked_mut<T>(
        &mut self,
        idx: T,
    ) -> &'_ mut <T as sealed::IntSliceIndex<Self>>::Output
    where
        T: IntSliceIndex<Self>,
    {
        // Safety: Propagates the requirements from the caller that this is a valid index.
        unsafe { <T as sealed::IntSliceIndex<Self>>::get_unchecked_mut(idx, self) }
    }
}

/// An indexing adaptor for `TryInto`.
///
/// This transparent wrapper allows any type to function as an index as long as it is fallibly
/// convertible to a `usize`. An indexing operation is successful if the conversion succeeds and
/// the resulting index is in bounds. Contrary to the simple integer types, the implementation of
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
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TryIndex<T>(pub T);

impl<T> TryIndex<T>
where
    T: TryInto<usize>,
    T::Error: Into<TryFromIntError>,
{
    fn into_int_index(self) -> usize {
        match self.0.try_into() {
            Ok(idx) => idx,
            Err(error) => panic!("Invalid index, {}", error.into()),
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
        let idx = self.into_int_index();
        unsafe { slice.get_unchecked(idx) }
    }
    unsafe fn get_unchecked_mut(self, slice: &mut [U]) -> &mut Self::Output {
        // Explicitly do __NOT__ make the conversion itself unchecked.
        let idx = self.into_int_index();
        unsafe { slice.get_unchecked_mut(idx) }
    }
    fn index(self, slice: &[U]) -> &Self::Output {
        &slice[self.into_int_index()]
    }
    fn index_mut(self, slice: &mut [U]) -> &mut Self::Output {
        &mut slice[self.into_int_index()]
    }
}

impl<T, U> IntSliceIndex<[U]> for TryIndex<T>
where
    T: TryInto<usize>,
    T::Error: Into<TryFromIntError>,
{
}

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

/// An adaptor for `ops::Index` that uses this crate's `IntSliceIndex` instead of the standard one.
///
/// This struct can be used to index a slice with an arbitrary integer type, using the standard
/// indexing syntax. It is also constructed by the [`Intex`] method exported in the crate root. The
/// indexing operation will first try to convert the number of a `usize` index and then do the
/// usual indexing.
///
/// [`Intex`]: ../fn.Intex.html
///
/// ```rust
/// use index_ext::int::Intex;
/// let val = [0u8; 2][Intex(1u32)];
/// ```
///
/// This is a transparent wrapper.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Intex<T>(pub T);

impl<T, U> core::ops::Index<Intex<T>> for [U]
where
    T: IntSliceIndex<[U]> + IndexSealed,
{
    type Output = <T as sealed::IntSliceIndex<[U]>>::Output;

    fn index(&self, idx: Intex<T>) -> &Self::Output {
        <T as sealed::IntSliceIndex<[U]>>::index(idx.0, self)
    }
}

impl<T, U> core::ops::IndexMut<Intex<T>> for [U]
where
    T: IntSliceIndex<[U]> + IndexSealed,
{
    fn index_mut(&mut self, idx: Intex<T>) -> &mut Self::Output {
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
                // Safety: the caller promises that the index is valid.
                Ok(idx) => unsafe { slice.get_unchecked(idx) },
                // Safety: the caller promises that the index is valid.
                // This implies that it is in-bounds of the `usize` type.
                Err(_) => unsafe { unreachable_unchecked() },
            }
        }
        unsafe fn get_unchecked_mut(self, slice: &mut [U]) -> &mut Self::Output {
            match IntoIntIndex::index(self) {
                // Safety: the caller promises that the index is valid.
                Ok(idx) => unsafe { slice.get_unchecked_mut(idx) },
                // Safety: the caller promises that the index is valid.
                // This implies that it is in-bounds of the `usize` type.
                Err(_) => unsafe { unreachable_unchecked() },
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
                // Safety: the caller promises that the index is valid.
                Ok(idx) => unsafe { slice.get_unchecked(idx) },
                // Safety: the caller promises that the index is valid.
                // This implies that it is in-bounds of the `usize` type.
                Err(_) => unsafe { unreachable_unchecked() },
            }
        }
        unsafe fn get_unchecked_mut(self, slice: &mut str) -> &mut Self::Output {
            match IntoIntIndex::index(self) {
                // Safety: the caller promises that the index is valid.
                Ok(idx) => unsafe { slice.get_unchecked_mut(idx) },
                // Safety: the caller promises that the index is valid.
                // This implies that it is in-bounds of the `usize` type.
                Err(_) => unsafe { unreachable_unchecked() },
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
        // Clippy warns within here:
        // > warning: question mark operator is useless here
        //
        // This is a 'false-positive' since this question mark not useless in all macro invocation.
        // For `$t = usize` we have `Err=Infallible` instead.
        #[allow(clippy::needless_question_mark)]
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

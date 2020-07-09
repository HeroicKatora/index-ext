//! Not quite dependent typing for eliding bounds checks.
//!
//! The main idea is to use lifetimes as a compile time tag to identify a particular exact slice
//! without keeping a direct reference of it. This means that you can not choose any of the
//! lifetime parameters that you see in this module. Instead, you must be prepared to handle
//! arbitrary lifetime which will make it opaque to you and the compiler. Each lifetime guarantees
//! that all `Ref` and `Mut` with that exact lifetime are at least as long as all the sizes in
//! `Len` structs of the same lifetime and each `Idx` is bounded by some `Len`. While this may seem
//! very restrictive at first, it still allows you to pass information on a slice's length across
//! function boundaries by explicitly mentioning the same lifetime twice. Additionally you're
//! allowed some mutable operations on indices that can not exceed the original bounds.
//!
//! Use `with_ref` and `with_mut` as the main entry constructors.
use core::marker::PhantomData;
use core::num::NonZeroUsize;

/// Enter a region for soundly indexing a slice without bounds checks.
///
/// The supplied function gets a freshly constructed pair of corresponding slice reference and
/// length tag. It has no control over the exact lifetime.
pub fn with_ref<T, U>(
    slice: &[T],
    f: impl for<'r> FnOnce(Ref<'r, T>, Len<'r>) -> U
) -> U {
    let len = Len {
        len: slice.len(),
        lifetime: PhantomData,
    };

    let slice = Ref { slice };

    f(slice, len)
}

/// Enter a region for soundly indexing a mutable slice without bounds checks.
///
/// The supplied function gets a freshly constructed pair of corresponding slice reference and
/// length tag. It has no control over the exact lifetime.
pub fn with_mut<T, U>(
    slice: &mut [T],
    f: impl for<'r> FnOnce(Mut<'r, T>, Len<'r>) -> U
) -> U {
    let len = Len {
        len: slice.len(),
        lifetime: PhantomData,
    };

    let slice = Mut { slice };

    f(slice, len)
}

/// The length of a particular slice (or a number of slices).
///
/// The encapsulated length field is guaranteed to be at most the length of each of the slices with
/// the exact same lifetime. This allows this instance to construct indices that are validated to
/// be able to soundly access the slices without required any particular slice instance. In
/// particular, the construct might happen by a numerical algorithm independent of the slices and
/// across method bounds where the compiler's optimizer and inline pass is no longer aware of the
/// connection and would otherwise insert another check when the slice is indexed later.
#[derive(Clone, Copy)]
pub struct Len<'slice> {
    len: usize,
    /// An invariant lifetime.
    lifetime: PhantomData<&'slice fn(&'slice [()])>,
}

/// The length of a non-empty slice.
#[derive(Clone, Copy)]
pub struct NonZeroLen<'slice> {
    len: NonZeroUsize,
    /// An invariant lifetime.
    lifetime: PhantomData<&'slice fn(&'slice [()])>,
}

/// A slice with a unique lifetime.
///
/// You can only construct this via [`Len::with_ref`].
///
/// [`Len::with_ref`]: struct.Len.html#method.with_ref
#[derive(Clone, Copy)]
pub struct Ref<'slice, T> {
    slice: &'slice [T],
}

/// A mutable slice with a unique lifetime.
///
/// You can only construct this via [`Len::with_mut`].
///
/// [`Len::with_mut`]: struct.Len.html#method.with_mut
pub struct Mut<'slice, T> {
    slice: &'slice mut [T],
}

/// A valid index for all slices of the same length.
///
/// While this has a generic parameter, you can only instantiate this type for specific types
/// through one of the constructors of a corresponding [`Len]` struct.
///
/// [`Len`]: struct.Len.html
#[derive(Clone, Copy)]
pub struct Idx<'slice, I> {
    idx: I,
    /// An invariant lifetime.
    lifetime: PhantomData<&'slice fn(&'slice [()])>,
}

impl<'slice> Len<'slice> {
    /// Returns the stored length.
    pub fn get(self) -> usize {
        self.len
    }

    /// Construct an index to a single element.
    ///
    /// This method return `Some` when the index is smaller than the length.
    pub fn index(self, idx: usize) -> Option<Idx<'slice, usize>> {
        if self.len < idx {
            Some(Idx { idx, lifetime: self.lifetime })
        } else {
            None
        }
    }

    /// Construct an index to a range of element.
    ///
    /// This method return `Some` when the indices are ordered and `to` does not exceed the length.
    pub fn range(self, from: usize, to: usize) -> Option<Idx<'slice, core::ops::Range<usize>>> {
        if self.len < from && self.len < to && from <= to {
            Some(Idx { idx: from..to, lifetime: self.lifetime })
        } else {
            None
        }
    }

    /// Construct an index to a range from an element.
    ///
    /// This method return `Some` when `from` does not exceed the length.
    pub fn range_from(self, from: usize) -> Option<Idx<'slice, core::ops::RangeFrom<usize>>> {
        if self.len <= from {
            Some(Idx { idx: from.., lifetime: self.lifetime })
        } else {
            None
        }
    }

    /// Construct an index to a range up to an element.
    ///
    /// This method return `Some` when `to` does not exceed the length.
    pub fn range_to(self, to: usize) -> Option<Idx<'slice, core::ops::RangeTo<usize>>> {
        if self.len <= to {
            Some(Idx { idx: ..to, lifetime: self.lifetime })
        } else {
            None
        }
    }

    /// Construct an index to all elements.
    ///
    /// This method exists mostly for completeness sake. There is no bounds check when accessing a
    /// complete slice with `..`.
    pub fn range_full(self) -> Idx<'slice, core::ops::RangeFull> {
        Idx { idx: .., lifetime: self.lifetime }
    }
}

impl<'slice> NonZeroLen<'slice> {
    /// Construct the length of a non-empty slice.
    pub fn new(complete: Len<'slice>) -> Option<Self> {
        let len = NonZeroUsize::new(complete.len)?;
        Some(NonZeroLen { len, lifetime: complete.lifetime })
    }

    /// Construct an index to the first element of a non-empty slice.
    pub fn first(self) -> Idx<'slice, usize> {
        Idx { idx: 0, lifetime: self.lifetime }
    }

    /// Construct an index to the last element of a non-empty slice.
    pub fn last(self) -> Idx<'slice, usize> {
        Idx { idx: self.len.get() - 1, lifetime: self.lifetime }
    }

    /// Get the non-zero length.
    pub fn get(self) -> NonZeroUsize {
        self.len
    }
}

impl<'slice> From<NonZeroLen<'slice>> for Len<'slice> {
    fn from(from: NonZeroLen<'slice>) -> Self {
        Len { len: from.len.get(), lifetime: from.lifetime }
    }
}

impl<'slice, I> Idx<'slice, I> {
    /// Get the inner index.
    pub fn into_inner(self) -> I {
        self.idx
    }
}

impl<'slice> Idx<'slice, usize> {
    pub fn saturating_sub(self, sub: usize) -> Self {
        Idx { idx: self.idx.saturating_sub(sub), lifetime: self.lifetime }
    }

    pub fn truncate(self, min: usize) -> Self {
        Idx { idx: self.idx.min(min), lifetime: self.lifetime }
    }
}

impl<'slice, T> Ref<'slice, T> {
    /// Index the slice unchecked but soundly.
    pub fn get_safe<I: core::slice::SliceIndex<[T]>>(&self, index: Idx<'slice, I>) -> &I::Output {
        unsafe { self.slice.get_unchecked(index.idx) }
    }
}

impl<'slice, T> Mut<'slice, T> {
    /// Index the slice unchecked but soundly.
    pub fn get_safe<I: core::slice::SliceIndex<[T]>>(&self, index: Idx<'slice, I>) -> &I::Output {
        unsafe { self.slice.get_unchecked(index.idx) }
    }

    /// Mutably index the slice unchecked but soundly.
    pub fn get_safe_mut<I: core::slice::SliceIndex<[T]>>(&mut self, index: Idx<'slice, I>) -> &mut I::Output {
        unsafe { self.slice.get_unchecked_mut(index.idx) }
    }
}

impl<T> core::ops::Deref for Ref<'_, T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        self.slice
    }
}

impl<T> core::ops::Deref for Mut<'_, T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        self.slice
    }
}

impl<T> core::ops::DerefMut for Mut<'_, T> {
    fn deref_mut(&mut self) -> &mut [T] {
        self.slice
    }
}

impl<'slice, T, I> core::ops::Index<Idx<'slice, I>> for Ref<'slice, T>
where
    I: core::slice::SliceIndex<[T]>
{
    type Output = I::Output;
    fn index(&self, idx: Idx<'slice, I>) -> &Self::Output {
        self.get_safe(idx)
    }
}

impl<'slice, T, I> core::ops::Index<Idx<'slice, I>> for Mut<'slice, T>
where
    I: core::slice::SliceIndex<[T]>
{
    type Output = I::Output;
    fn index(&self, idx: Idx<'slice, I>) -> &Self::Output {
        self.get_safe(idx)
    }
}

impl<'slice, T, I> core::ops::IndexMut<Idx<'slice, I>> for Mut<'slice, T>
where
    I: core::slice::SliceIndex<[T]>
{
    fn index_mut(&mut self, idx: Idx<'slice, I>) -> &mut Self::Output {
        self.get_safe_mut(idx)
    }
}

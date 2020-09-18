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

/// A type suitable for tagging length, indices, and containers.
///
/// It must _not_ be safe to create two instances of the same type and should be impossible except
/// through the `copy` method. Note that this restriction MUST hold for every possible coercion
/// allowed by the language.
pub unsafe trait Tag: Copy {}

/// A generative lifetime.
///
/// This is a simple implementor of `Tag` that allows a _local_ but entirely safe and macro-free
/// use of check indices. The compiler introduces new lifetimes and the design of these types
/// ensure that no other object with the same can be created.
#[derive(Clone, Copy)]
pub struct Generative<'lt> {
    /// An invariant lifetime.
    generated: PhantomData<&'lt fn(&'lt [()])>,
}

/// SAFETY: This is invariant over the lifetime. There are no other coercions.
unsafe impl Tag for Generative<'_> {}

/// A named unique tag.
pub struct Named<T> {
    phantom: PhantomData<T>,
}

/// Enter a region for soundly indexing a slice without bounds checks.
///
/// The supplied function gets a freshly constructed pair of corresponding slice reference and
/// length tag. It has no control over the exact lifetime.
pub fn with_ref<'slice, T, U>(
    slice: &'slice [T],
    f: impl for<'r> FnOnce(Ref<'slice, T, Generative<'r>>, Len<Generative<'r>>) -> U,
) -> U {
    let len = Len {
        len: slice.len(),
        tag: Generative {
            generated: PhantomData,
        },
    };

    let slice = Ref { slice, tag: len.tag };

    f(slice, len)
}

/// Enter a region for soundly indexing a mutable slice without bounds checks.
///
/// The supplied function gets a freshly constructed pair of corresponding slice reference and
/// length tag. It has no control over the exact lifetime.
pub fn with_mut<'slice, T, U>(
    slice: &'slice mut [T],
    f: impl for<'r> FnOnce(Mut<'slice, T, Generative<'r>>, Len<Generative<'r>>) -> U
) -> U {
    let len = Len {
        len: slice.len(),
        tag: Generative {
            generated: PhantomData,
        },
    };

    let slice = Mut { slice, tag: len.tag };

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
pub struct Len<Tag> {
    len: usize,
    tag: Tag,
}

/// The length of a non-empty slice.
#[derive(Clone, Copy)]
pub struct NonZeroLen<Tag> {
    len: NonZeroUsize,
    tag: Tag,
}

/// The _exact_ length separating slices and indices for a tag.
///
/// This serves as an constructor basis for 'importing' lengths and slices that are not previously
/// connected through `with_ref`. This is also useful for cases where you want to create some
/// bounds prior to the slice being available, or for creating bounds of custom tags.
#[derive(Clone, Copy)]
pub struct ExactSize<Tag> {
    len: usize,
    tag: Tag,
}

/// A slice with a unique lifetime.
///
/// You can only construct this via [`Len::with_ref`].
///
/// [`Len::with_ref`]: struct.Len.html#method.with_ref
#[derive(Clone, Copy)]
pub struct Ref<'slice, T, Tag> {
    slice: &'slice [T],
    #[allow(dead_code)]
    tag: Tag,
}

/// A mutable slice with a unique lifetime.
///
/// You can only construct this via [`Len::with_mut`].
///
/// [`Len::with_mut`]: struct.Len.html#method.with_mut
pub struct Mut<'slice, T, Tag> {
    slice: &'slice mut [T],
    #[allow(dead_code)]
    tag: Tag,
}

/// A valid index for all slices of the same length.
///
/// While this has a generic parameter, you can only instantiate this type for specific types
/// through one of the constructors of a corresponding [`Len]` struct.
///
/// [`Len`]: struct.Len.html
#[derive(Clone, Copy)]
pub struct Idx<I, Tag> {
    idx: I,
    /// An invariant lifetime.
    tag: Tag,
}

impl<T: Tag> Len<T> {
    /// Returns the stored length.
    pub fn get(self) -> usize {
        self.len
    }

    /// Construct an index to a single element.
    ///
    /// This method return `Some` when the index is smaller than the length.
    pub fn index(self, idx: usize) -> Option<Idx<usize, T>> {
        if idx < self.len {
            Some(Idx {
                idx,
                tag: self.tag,
            })
        } else {
            None
        }
    }

    /// Construct an index to a range of element.
    ///
    /// This method return `Some` when the indices are ordered and `to` does not exceed the length.
    pub fn range(self, from: usize, to: usize) -> Option<Idx<core::ops::Range<usize>, T>> {
        if from <= to && to <= self.len {
            Some(Idx {
                idx: from..to,
                tag: self.tag,
            })
        } else {
            None
        }
    }

    /// Construct an index to a range from an element.
    ///
    /// This method return `Some` when `from` does not exceed the length.
    pub fn range_from(self, from: usize) -> Option<Idx<core::ops::RangeFrom<usize>, T>> {
        if from <= self.len {
            Some(Idx {
                idx: from..,
                tag: self.tag,
            })
        } else {
            None
        }
    }

    /// Construct an index to a range up to an element.
    ///
    /// This method return `Some` when `to` does not exceed the length.
    pub fn range_to(self, to: usize) -> Option<Idx<core::ops::RangeTo<usize>, T>> {
        if to <= self.len {
            Some(Idx {
                idx: ..to,
                tag: self.tag,
            })
        } else {
            None
        }
    }

    /// Construct an index to all elements.
    ///
    /// This method exists mostly for completeness sake. There is no bounds check when accessing a
    /// complete slice with `..`.
    pub fn range_full(self) -> Idx<core::ops::RangeFull, T> {
        Idx {
            idx: ..,
            tag: self.tag,
        }
    }
}

impl<T: Tag> NonZeroLen<T> {
    /// Construct the length of a non-empty slice.
    pub fn new(complete: Len<T>) -> Option<Self> {
        let len = NonZeroUsize::new(complete.len)?;
        Some(NonZeroLen {
            len,
            tag: complete.tag,
        })
    }

    /// Construct an index to the first element of a non-empty slice.
    pub fn first(self) -> Idx<usize, T> {
        Idx {
            idx: 0,
            tag: self.tag,
        }
    }

    /// Construct an index to the last element of a non-empty slice.
    pub fn last(self) -> Idx<usize, T> {
        Idx {
            idx: self.len.get() - 1,
            tag: self.tag,
        }
    }

    /// Get the non-zero length.
    pub fn get(self) -> NonZeroUsize {
        self.len
    }
}

impl<T: Tag> ExactSize<T> {
    /// Construct a new bound between yet-to-create indices and slices.
    ///
    /// # Safety
    ///
    /// All `ExactSize` instances with the same tag type must also have the same `len` field.
    pub unsafe fn new(len: usize, tag: T) -> Self {
        ExactSize { len, tag }
    }

    /// Construct a new bound from a length.
    ///
    /// #Safety
    ///
    /// You _must_ ensure that no slice with this same tag can be shorter than `len`. In particular
    /// there mustn't be any other `ExactSize` with a differing length.
    pub unsafe fn from_len(len: Len<T>) -> Self {
        ExactSize { len: len.len, tag: len.tag }
    }

    /// Convert this into a simple `Len` without changing the length.
    ///
    /// The `Len` is only required to be _shorter_ than all slices but not required to have the
    /// exact separating size. As such, one can not use it to infer that some particular slice is
    /// long enough to be allowed. This is not safely reversible.
    pub fn len(self) -> Len<T> {
        Len { len: self.len, tag: self.tag }
    }

    /// Construct a new bound from an pair of Len and slice with the same length.
    ///
    /// Note that the invariant of `ExactSize` is that all `Len` are guaranteed to be at most the
    /// size and all `Ref` and `RefMut` are guaranteed to be at least the size. The only possible
    /// overlap between the two is the exact slice length, which we can dynamically check.
    ///
    /// # Panics
    /// This method panics of `len.get()` and `slice.len()` are not equal.
    pub fn with_matching_pair<U>(len: Len<T>, slice: Ref<'_, T, U>) -> Self {
        assert_eq!(len.get(), slice.len(), "Length and slice do not define a precise size");
        ExactSize { len: len.get(), tag: len.tag }
    }
}

impl<T> Named<T> {
    /// Create a new named tag.
    ///
    /// The instance is only to be encouraged to only use types private to your crate or module,
    /// this method immediately *forgets* the instance which is currently required for `const`ness.
    ///
    /// # Safety
    /// This is highly unsafe. You must ensure that no other instance with the same __type__ (not
    /// value, type) can be created by any unrelated code.
    pub const unsafe fn new(t: T) -> Self {
        core::mem::ManuallyDrop::new(t);
        Named { phantom: PhantomData, }
    }
}

unsafe impl<T> Tag for Named<T> {}

impl<T: Tag> From<NonZeroLen<T>> for Len<T> {
    fn from(from: NonZeroLen<T>) -> Self {
        Len {
            len: from.len.get(),
            tag: from.tag,
        }
    }
}

impl<T, I> Idx <I, T> {
    /// Get the inner index.
    pub fn into_inner(self) -> I {
        self.idx
    }
}

impl<T> Idx<usize, T> {
    pub fn saturating_sub(self, sub: usize) -> Self {
        Idx {
            idx: self.idx.saturating_sub(sub),
            tag: self.tag,
        }
    }

    pub fn truncate(self, min: usize) -> Self {
        Idx {
            idx: self.idx.min(min),
            tag: self.tag,
        }
    }
}

impl<'slice, T: Tag, E> Ref<'slice, E, T> {
    /// Try to wrap a slice into a safe index wrapper.
    ///
    /// Returns `Some(_)` if the slice is at least as long as the `size` requires, otherwise
    /// returns `None`.
    pub fn new(slice: &'slice [E], size: ExactSize<T>) -> Option<Self> {
        if slice.len() >= size.len {
            Some(Ref {
                slice,
                tag: size.tag,
            })
        } else {
            None
        }
    }

    /// Index the slice unchecked but soundly.
    pub fn get_safe<I: core::slice::SliceIndex<[E]>>(&self, index: Idx<I, T>) -> &I::Output {
        unsafe { self.slice.get_unchecked(index.idx) }
    }

    /// Unwrap the inner slice, dropping all assertions of safe indexing.
    pub fn into_inner(self) -> &'slice [E] {
        self.slice
    }
}

impl<'slice, T: Tag, E> Mut<'slice, E, T> {
    /// Try to wrap a slice into a safe index wrapper.
    ///
    /// Returns `Some(_)` if the slice is at least as long as the `size` requires, otherwise
    /// returns `None`.
    pub fn new(slice: &'slice mut [E], size: ExactSize<T>) -> Option<Self> {
        if slice.len() >= size.len {
            Some(Mut {
                slice,
                tag: size.tag,
            })
        } else {
            None
        }
    }

    /// Index the slice unchecked but soundly.
    pub fn get_safe<I: core::slice::SliceIndex<[E]>>(&self, index: Idx<I, T>) -> &I::Output {
        unsafe { self.slice.get_unchecked(index.idx) }
    }

    /// Mutably index the slice unchecked but soundly.
    pub fn get_safe_mut<I: core::slice::SliceIndex<[E]>>(
        &mut self,
        index: Idx<I, T>,
    ) -> &mut I::Output {
        unsafe { self.slice.get_unchecked_mut(index.idx) }
    }

    /// Unwrap the inner slice, dropping all assertions of safe indexing.
    pub fn into_inner(self) -> &'slice [E] {
        self.slice
    }
}

impl<E, T> core::ops::Deref for Ref<'_, E, T> {
    type Target = [E];
    fn deref(&self) -> &[E] {
        self.slice
    }
}

impl<E, T> core::ops::Deref for Mut<'_, E, T> {
    type Target = [E];
    fn deref(&self) -> &[E] {
        self.slice
    }
}

impl<E, T> core::ops::DerefMut for Mut<'_, E, T> {
    fn deref_mut(&mut self) -> &mut [E] {
        self.slice
    }
}

impl<T: Tag, E, I> core::ops::Index<Idx<I, T>> for Ref<'_, E, T>
where
    I: core::slice::SliceIndex<[E]>,
{
    type Output = I::Output;
    fn index(&self, idx: Idx<I, T>) -> &Self::Output {
        self.get_safe(idx)
    }
}

impl<T: Tag, E, I> core::ops::Index<Idx<I, T>> for Mut<'_, E, T>
where
    I: core::slice::SliceIndex<[E]>,
{
    type Output = I::Output;
    fn index(&self, idx: Idx<I, T>) -> &Self::Output {
        self.get_safe(idx)
    }
}

impl<T: Tag, E, I> core::ops::IndexMut<Idx<I, T>> for Mut<'_, E, T>
where
    I: core::slice::SliceIndex<[E]>,
{
    fn index_mut(&mut self, idx: Idx<I, T>) -> &mut Self::Output {
        self.get_safe_mut(idx)
    }
}

impl<T> Clone for Named<T> {
    fn clone(&self) -> Self { *self }
}

impl<T> Copy for Named<T> {}

#[cfg(test)]
mod tests {
    #[test]
    fn basics() {
        fn problematic(buf: &mut [u8], offsets: &[u8], idx: usize) {
            super::with_ref(&offsets[..=idx], |offsets, len| {
                let mut idx = len.index(idx).unwrap();
                for b in buf {
                    *b = idx.into_inner() as u8;
                    idx = idx.saturating_sub(usize::from(offsets[idx]));
                }
            })
        }

        let mut output = [0; 3];
        let offsets = [1, 0, 2, 2];
        problematic(&mut output, &offsets[..], 3);
        assert_eq!(output, [3, 1, 1]);
    }
}

/// assertion macros are due to (c) theInkSquid (foobles)
/// ```compile_fail
/// use index_ext::tag;
/// macro_rules! assert_is_covariant {
///     (for[$($gen_params:tt)*] ($type_name:ty) over $lf:lifetime) => {
///         #[allow(warnings)]
///         const _: fn() = || {
///             struct Cov<$lf, $($gen_params)*>($type_name);
/// 
///             fn test_cov<'__s, '__a: '__b, '__b, $($gen_params)*>(
///                 subtype: &'__s Cov<'__a, $($gen_params)*>,
///                 mut _supertype: &'__s Cov<'__b, $($gen_params)*>,
///             ) {
///                 _supertype = subtype;
///             }
///         };
///     };
/// 
///     (($type_name:ty) over $lf:lifetime) => {
///         assert_is_covariant!(for[] ($type_name) over $lf);
///     };
/// }
///
/// assert_is_covariant! {
///     (tag::Len<'r>) over 'r
/// }
/// ```
///
/// ```compile_fail
/// use index_ext::tag;
/// macro_rules! assert_is_contravariant {
///     (for[$($gen_params:tt)*] ($type_name:ty) over $lf:lifetime) => {
///         #[allow(warnings)]
///         const _: fn() = || {
///             struct Contra<$lf, $($gen_params)*>($type_name);
/// 
///             fn test_contra<'__s, '__a: '__b, '__b, $($gen_params)*>(
///                 mut _subtype: &'__s Contra<'__a, $($gen_params)*>,
///                 supertype: &'__s Contra<'__b, $($gen_params)*>,
///             ) {
///                 _subtype = supertype;
///             }
///         };
///     };
/// 
///     (($type_name:ty) over $lf:lifetime) => {
///         assert_is_contravariant!(for[] ($type_name) over $lf);
///     };
/// }
///
/// assert_is_contravariant! {
///     (tag::Len<'r>) over 'r
/// }
/// ```
extern {}

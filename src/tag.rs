//! Not quite dependent typing for eliding bounds checks.
//!
//! ## Rough mechanism
//!
//! The main idea is to use types as a compile time tag to identify a particular exact length bound
//! without storing this bound in all instances associated with it. Thusly, we can construct
//! indices that are guaranteed in-bounds of slices tagged with the same type, while storing them
//! independent of each other and without introducing any borrow coupling. This then _guarantees_ a
//! bounds-check free code path for indexing into the slices.
//!
//! This works particularly well for programs with fixed size buffers, i.e. kernels, bootloaders,
//! embedded, high-assurance programs. If you encapsulate the `ExactSize` instance containing the
//! authoritative source of the associated length then you can have a very high confidence in have
//! ran appropriate access and bounds checks before accesses.
//!
//! ## Built-in Tag types
//!
//! There are a couple of different methods for creating tag types with such associations:
//!
//! 1. As a compile time constant. The [`Constant`] and [`Const`] offer different ways of defining
//!    the associated length as a fixed number. The former let's you give it a type as a name while
//!    the latter is based on generic parameters.
//!
//! 2. The generative way. The [`Generative`]` type is unique for every created instance by having
//!    a unique lifetime parameter.  That is, you can not choose its lifetime parameters freely.
//!    Instead, to create an instance you write a function be prepared to handle arbitrary lifetime
//!    and the library hands an instance to you. This makes the exact lifetime opaque to you and
//!    the compiler which forces all non-local code to assume that it is indeed unique and it can
//!    not be unified with any other. We associate such a [`Generative`] instance with the length
//!    of the one slice provided during its construction.
//!
//! 3. And finally one might come up with an internal naming scheme where types are used to express
//!    unique bounds. This requires some unsafe code and the programmers guarantee of uniqueness of
//!    values but permits the combination of runtime values with `'static` lifetime of the tag.
//!
//! Each tag guarantees that all [`Ref`] and [`Mut`] with that exact same tag are at least as long
//! as all the sizes in [`Len`] structs of the same lifetime and each [`Idx`] is bounded by some
//! [`Len`].  While this may seem very restrictive at first, it still allows you to pass
//! information on a slice's length across function boundaries by explicitly mentioning the same
//! lifetime twice.  Additionally you're allowed some mutable operations on indices that can not
//! exceed the original bounds.
//!
//! Use [`with_ref`] and [`with_mut`] as main entry functions or one the constructors on the type
//! [`Generative`]. Note the interaction with the `generativity` crate which provides a macro that
//! doesn't influence code flow, instead of requiring a closure wrapper like the methods given in
//! this crate.
//!
//! [`with_ref`]: fn.with_ref.html
//! [`with_mut`]: fn.with_mut.html
//!
//! Additionally, the module provides an 'algebra' for tags such that you can dynamically prove two
//! tags to be equivalent, comparable, etc. Then you can leverage these facts (which are also
//! encoded as types) to substitute tags in different manner. See the [`LessEq`] and [`Eq`] types
//! as well as the many combinators on [`ExactSize`], [`Len`], and [`Idx`].
//!
//! ## Checked constant bounds
//!
//! Alternatively we can choose other unique type instances. By that we mean that for any
//! particular type exactly _one_ value must be used to construct [`ExactSize`]. One possible way
//! is if this is simply a constant which is implemented by the `Constant` wrapper and its
//! [`ConstantSource`] trait. For example one may define:
//!
//! ```
//! use index_ext::tag::{Constant, ConstantSource, ExactSize};
//!
//! const BUFFER_SIZE: usize = 4096;
//! struct BufferSize4K;
//!
//! impl ConstantSource for BufferSize4K {
//!     const LEN: usize = BUFFER_SIZE;
//! }
//!
//! const LEN: ExactSize<Constant<BufferSize4K>> = Constant::EXACT_SIZE;
//! ```
use core::marker::PhantomData;
use core::num::NonZeroUsize;
use core::ops::{Range, RangeFrom, RangeTo};

/// A type suitable for tagging length, indices, and containers.
///
/// # Safety
///
/// The manner in which new [`ExactSize`] instances of types implementing this trait can be created
/// is an invariant of each individual type. It must **not** be allowed to subvert the invariants
/// imposed by any other type implementing this trait. In particular you mustn't create an instance
/// that allows coercing a `ExactSize<ATag>` into `ExactSize<BTag>` where you don't control both
/// these types. Note that this restriction MUST hold for every possible coercion allowed by the
/// language. There are no inherently safe constructors for `ExactSize` but each tag type might
/// define some.
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
/// See <https://doc.rust-lang.org/nomicon/coercions.html#coercions>
unsafe impl Tag for Generative<'_> {}

/// A named unique tag.
pub struct Named<T> {
    phantom: PhantomData<T>,
}

/// Enter a region for soundly indexing a slice without bounds checks.
///
/// The supplied function gets a freshly constructed pair of corresponding slice reference and
/// length tag. It has no control over the exact lifetime used for the tag.
pub fn with_ref<'slice, T, U>(
    slice: &'slice [T],
    f: impl for<'r> FnOnce(Ref<'slice, T, Generative<'r>>, ExactSize<Generative<'r>>) -> U,
) -> U {
    let len = ExactSize {
        inner: Len {
            len: slice.len(),
            tag: Generative {
                generated: PhantomData,
            },
        },
    };

    let slice = Ref {
        slice,
        tag: len.inner.tag,
    };

    f(slice, len)
}

/// Enter a region for soundly indexing a mutable slice without bounds checks.
///
/// The supplied function gets a freshly constructed pair of corresponding slice reference and
/// length tag. It has no control over the exact lifetime used for the tag.
pub fn with_mut<'slice, T, U>(
    slice: &'slice mut [T],
    f: impl for<'r> FnOnce(Mut<'slice, T, Generative<'r>>, ExactSize<Generative<'r>>) -> U,
) -> U {
    let len = ExactSize {
        inner: Len {
            len: slice.len(),
            tag: Generative {
                generated: PhantomData,
            },
        },
    };

    let slice = Mut {
        slice,
        tag: len.inner.tag,
    };

    f(slice, len)
}

/// The length of a particular slice (or a number of slices).
///
/// The encapsulated length field is guaranteed to be at most the length of each of the slices with
/// the exact same tag. In other words, all indices _strictly smaller_ than this number are
/// safe.
///
/// This allows this instance to construct indices that are validated to be able to soundly
/// access the slices without required any particular slice instance. In particular, the construct
/// might happen by a numerical algorithm independent of the slices and across method bounds where
/// the compiler's optimizer and inline pass is no longer aware of the connection and would
/// otherwise insert another check when the slice is indexed later.
#[derive(Clone, Copy)]
pub struct Len<Tag> {
    len: usize,
    tag: Tag,
}

/// A number that overestimates the guaranteed size of a number of slices.
///
/// This is the counter part of [`Len`]. It encapsulates a field that is guaranteed to be at least
/// the size of all indices with the exact same tag. In other words, all slices at least as long
/// as this number are safe to be accessed by indices.
#[derive(Clone, Copy)]
pub struct Capacity<Tag> {
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
    inner: Len<Tag>,
}

/// A proof that the length if A is smaller or equal to B.
///
/// This guarantees that indices of `A` can also be used in `B`.
#[derive(Clone, Copy)]
pub struct LessEq<TagA, TagB> {
    a: TagA,
    b: TagB,
}

/// A proof that two tags refer to equal lengths.
///
/// This guarantees that indices of `A` and `B` can be used interchangeably.
#[derive(Clone, Copy)]
pub struct Eq<TagA, TagB> {
    a: TagA,
    b: TagB,
}

/// A slice with a unique type tag.
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

/// A mutable slice with a unique type tag.
///
/// You can only construct this via [`Len::with_mut`].
///
/// [`Len::with_mut`]: struct.Len.html#method.with_mut
pub struct Mut<'slice, T, Tag> {
    slice: &'slice mut [T],
    #[allow(dead_code)]
    tag: Tag,
}

/// An owned, allocated slice with a checked length.
#[cfg(feature = "alloc")]
pub struct Boxed<T, Tag> {
    inner: alloc::boxed::Box<[T]>,
    tag: Tag,
}

/// A type that names a constant buffer size.
///
/// See the module level documentation.
pub trait ConstantSource {
    /// The chosen length separating indices and slices.
    const LEN: usize;
}

/// A tag using a `ConstantSource`.
///
/// The only safe way to construct an `ExactSize` is by copying the associated constant which
/// expresses the length indicated in the trait impl. This implies that the value is unique.
/// (Disregarding unsound rustc issues that allow duplicate trait impls).
pub struct Constant<T>(PhantomData<fn(&mut T) -> T>);

unsafe impl<T: ConstantSource> Tag for Constant<T> {}

/// A tag using a const generic length parameter.
///
/// The only safe way to construct an `ExactSize` is by copying the associated constant which
/// expresses the length indicated in the trait impl. This implies that the value is unique.
///
/// # Usage
///
/// ```
/// use index_ext::tag::{Const, Ref};
///
/// let size = Const::<8>::EXACT_SIZE;
///
/// let data = [0, 1, 2, 3, 4, 5, 6, 7];
/// let slice = Ref::new(&data[..], size).unwrap();
///
/// let prefix = size
///     .into_len()
///     .truncate(4)
///     .range_to_self();
///
/// let prefix = &slice[prefix];
/// assert_eq!(prefix, [0, 1, 2, 3]);
/// ```
#[derive(Clone, Copy)]
pub struct Const<const N: usize>;

unsafe impl<const N: usize> Tag for Const<N> {}

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

/// An allocation of bounded indices that can be retrieved with a bound.
///
/// The usefulness comes from the fact that there is not tag on the type but instead one is
/// assigned when retrieving the contents. In particular you don't need a unique type to construct
/// this container.
#[cfg(feature = "alloc")]
pub struct IdxBox<Idx> {
    indices: alloc::boxed::Box<[Idx]>,
    /// The dynamic bound of indices.
    exact_size: usize,
}

impl<T: Tag> Len<T> {
    /// Interpret this with the tag of a set of potentially longer slices.
    ///
    /// The proof of inequality was performed in any of the possible constructors that allow the
    /// instance of `LessEq` to exist in the first place.
    pub fn with_tag<NewT>(self, less: LessEq<T, NewT>) -> Len<NewT> {
        let len = self.len;
        let tag = less.b;
        Len { len, tag }
    }

    /// Returns the stored length.
    #[must_use = "Is a no-op. Use the returned length."]
    pub fn get(self) -> usize {
        self.len
    }

    /// Construct an index to a single element.
    ///
    /// This method return `Some` when the index is smaller than the length.
    #[must_use = "Returns a new index"]
    pub fn index(self, idx: usize) -> Option<Idx<usize, T>> {
        if idx < self.len {
            Some(Idx { idx, tag: self.tag })
        } else {
            None
        }
    }

    /// Construct an index to a range of element.
    ///
    /// This method return `Some` when the indices are ordered and `to` does not exceed the length.
    #[must_use = "Returns a new index"]
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
    #[must_use = "Returns a new index"]
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

    /// Construct an index to a range starting at this length.
    ///
    /// This method might return an index for an empty range.
    #[must_use = "Returns a new index"]
    pub fn range_from_self(self) -> Idx<core::ops::RangeFrom<usize>, T> {
        Idx {
            idx: self.len..,
            tag: self.tag,
        }
    }

    /// Construct an index to a range up to an element.
    ///
    /// This method return `Some` when `to` does not exceed the length.
    #[must_use = "Returns a new index"]
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

    /// Construct an index to a range up, exclusive, to this length.
    ///
    /// This method might return an index for an empty range.
    #[must_use = "Returns a new index"]
    pub fn range_to_self(self) -> Idx<core::ops::RangeTo<usize>, T> {
        Idx {
            idx: ..self.len,
            tag: self.tag,
        }
    }

    /// Construct an index referring to the unordered range from one element to another.
    ///
    /// This method might return an empty range. The order of arguments does not matter.
    #[must_use = "Returns a new index"]
    pub fn range_between(self, other: Self) -> Idx<core::ops::Range<usize>, T> {
        Idx {
            idx: self.len.min(other.len)..self.len.max(other.len),
            tag: self.tag,
        }
    }

    /// Construct an index to all elements.
    ///
    /// This method exists mostly for completeness sake. There is no bounds check when accessing a
    /// complete slice with `..`.
    #[must_use = "Returns a new index"]
    pub fn range_full(self) -> Idx<core::ops::RangeFull, T> {
        Idx {
            idx: ..,
            tag: self.tag,
        }
    }

    /// Create a smaller length.
    #[must_use = "Returns a new index"]
    pub fn saturating_sub(self, sub: usize) -> Self {
        Len {
            len: self.len.saturating_sub(sub),
            tag: self.tag,
        }
    }

    /// Bound the length from above.
    #[must_use = "Returns a new index"]
    pub fn truncate(self, min: usize) -> Self {
        Len {
            len: self.len.min(min),
            tag: self.tag,
        }
    }
}

impl<T: Tag> Capacity<T> {
    /// Interpret this with the tag of a set of potentially shorter slices.
    ///
    /// The proof of inequality was performed in any of the possible constructors that allow the
    /// instance of `LessEq` to exist in the first place.
    pub fn with_tag<NewT>(self, less: LessEq<NewT, T>) -> Capacity<NewT> {
        let len = self.len;
        let tag = less.a;
        Capacity { len, tag }
    }

    /// Returns the stored length.
    #[must_use = "Is a no-op. Use the returned length."]
    pub fn get(self) -> usize {
        self.len
    }

    /// Create a larger capacity.
    #[must_use = "Returns a new capacity"]
    pub fn saturating_add(self, add: usize) -> Self {
        Capacity {
            len: self.len.saturating_add(add),
            tag: self.tag,
        }
    }

    /// Bound the length from below.
    #[must_use = "Returns a new capacity"]
    pub fn ensure(self, min: usize) -> Self {
        Capacity {
            len: self.len.max(min),
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

    /// Interpret this with the tag of a potentially longer slice.
    ///
    /// The proof of inequality was performed in any of the possible constructors that allow the
    /// instance of `LessEq` to exist in the first place.
    pub fn with_tag<NewT>(self, less: LessEq<T, NewT>) -> NonZeroLen<NewT> {
        let len = self.len;
        let tag = less.b;
        NonZeroLen { len, tag }
    }

    /// Construct an index to the first element of a non-empty slice.
    #[must_use = "Returns a new index"]
    pub fn first(self) -> Idx<usize, T> {
        Idx {
            idx: 0,
            tag: self.tag,
        }
    }

    /// Construct an index to the last element of a non-empty slice.
    #[must_use = "Returns a new index"]
    pub fn last(self) -> Idx<usize, T> {
        Idx {
            idx: self.len.get() - 1,
            tag: self.tag,
        }
    }

    /// Construct the corresponding potentially empty length representation.
    #[must_use = "Returns a new index"]
    pub fn into_len(self) -> Len<T> {
        Len {
            len: self.len.get(),
            tag: self.tag,
        }
    }

    /// Get the non-zero length.
    #[must_use = "Is a no-op. Use the returned length."]
    pub fn get(self) -> NonZeroUsize {
        self.len
    }
}

/// The const methods for `ExactSize`.
///
/// Since trait bounds are not currently usable on stable the selection is limited. **Note**: It is
/// of importance to soundness that it is not possible to construct an instance without the `Tag`
/// bound. Otherwise, one might coerce _into_ an `ExactSize` with an improper tag. This is not
/// likely to be possible but nevertheless the `Tag` does not require it to be impossible.
impl<T> ExactSize<T> {
    /// Construct a new bound between yet-to-create indices and slices.
    ///
    /// # Safety
    ///
    /// All `ExactSize` instances with the same tag type must also have the same `len` field.
    pub const unsafe fn new_untagged(len: usize, tag: T) -> Self {
        ExactSize {
            inner: Len { len, tag },
        }
    }

    /// Construct a new bound from a length.
    ///
    /// # Safety
    ///
    /// You _must_ ensure that no slice with this same tag can be shorter than `len`. In particular
    /// there mustn't be any other `ExactSize` with a differing length.
    ///
    /// `T` should be a type implementing `Tag` but this can not be expressed with `const fn` atm.
    pub const unsafe fn from_len_untagged(bound: Len<T>) -> Self {
        ExactSize { inner: bound }
    }

    /// Returns the length.
    #[must_use = "Is a no-op. Use the returned length."]
    pub const fn get(&self) -> usize {
        self.inner.len
    }
}

impl<'lt> Generative<'lt> {
    /// Construct a size with a generative guard and explicit length.
    ///
    /// The `Guard` instance is a token that verifies that no other instance with that particular
    /// lifetime exists. It is thus not possible to safely construct a second `ExactSize` with the
    /// same tag but a different length. This uniquely ties the value `len` to that lifetime.
    pub fn with_len(len: usize, token: generativity::Guard<'lt>) -> ExactSize<Self> {
        ExactSize::with_guard(len, token)
    }

    pub fn with_ref<'slice, T>(slice: &'slice [T], token: generativity::Guard<'lt>)
        -> (Ref<'slice, T, Self>, ExactSize<Self>)
    {
        let size = ExactSize::with_guard(slice.len(), token);
        // Safety: This tag is associated with the exact length of the slice in the line above
        // which is less or equal to the length of the slice.
        let ref_ = unsafe { Ref::new_unchecked(slice, size.inner.tag) };
        (ref_, size)
    }

    pub fn with_mut<'slice, T>(slice: &'slice mut [T], token: generativity::Guard<'lt>)
        -> (Mut<'slice, T, Self>, ExactSize<Self>)
    {
        let size = ExactSize::with_guard(slice.len(), token);
        // Safety: This tag is associated with the exact length of the slice in the line above
        // which is less or equal to the length of the slice.
        let ref_ = unsafe { Mut::new_unchecked(slice, size.inner.tag) };
        (ref_, size)
    }
}

impl<'lt> ExactSize<Generative<'lt>> {
    /// Construct a size with a generative guard.
    ///
    /// The `Guard` instance is a token that verifies that no other instance with that particular
    /// lifetime exists. It is thus not possible to safely construct a second `ExactSize` with the
    /// same tag but a different length. This uniquely ties the value `len` to that lifetime.
    ///
    /// FIXME: make this `const fn` which requires `PhantomData<fn()>` to be allowed in const
    /// context (a small subset of #57563).
    pub fn with_guard(len: usize, _: generativity::Guard<'lt>) -> Self {
        ExactSize {
            inner: Len {
                len,
                tag: Generative {
                    generated: PhantomData,
                },
            },
        }
    }
}

impl<T: Tag> ExactSize<T> {
    /// Construct a new bound between yet-to-create indices and slices.
    ///
    /// # Safety
    ///
    /// All `ExactSize` instances with the same tag type must also have the same `len` field.
    pub unsafe fn new(len: usize, tag: T) -> Self {
        Self::new_untagged(len, tag)
    }

    /// Construct a new bound from a length.
    ///
    /// # Safety
    ///
    /// You _must_ ensure that no slice with this same tag can be shorter than `len`. In particular
    /// there mustn't be any other `ExactSize` with a differing length.
    pub unsafe fn from_len(len: Len<T>) -> Self {
        Self::from_len_untagged(len)
    }

    /// Construct a new bound from a capacity.
    ///
    /// # Safety
    ///
    /// You _must_ ensure that no index with this same tag can be above `cap`. In particular there
    /// mustn't be any other `ExactSize` with a differing length but the same tag type.
    pub unsafe fn from_capacity(cap: Capacity<T>) -> Self {
        Self::new_untagged(cap.len, cap.tag)
    }

    /// Interpret this with the tag of an equal sized slice.
    ///
    /// The proof of equality was performed in any of the possible constructors that allow the
    /// instance of `Eq` to exist in the first place.
    pub fn with_tag<NewT>(self, equality: Eq<T, NewT>) -> ExactSize<NewT> {
        let len = self.inner.len;
        let tag = equality.b;
        ExactSize {
            inner: Len { len, tag },
        }
    }

    /// Convert this into a simple `Len` without changing the length.
    ///
    /// The `Len` is only required to be _not longer_ than all slices but not required to have the
    /// exact separating size. As such, one can not use it to infer that some particular slice is
    /// long enough to be allowed. This is not safely reversible.
    #[must_use = "Returns a new index"]
    pub fn into_len(self) -> Len<T> {
        self.inner
    }

    /// Convert this into a simple `Capacity` without changing the length.
    ///
    /// The `Capacity` is only required to be _not shorter_ than all slices but not required to
    /// have the exact separating size. As such, one can use it only to infer that some particular
    /// slice is long enough to be allowed. This is not safely reversible.
    #[must_use = "Returns a new index"]
    pub fn into_capacity(self) -> Capacity<T> {
        Capacity {
            len: self.inner.len,
            tag: self.inner.tag,
        }
    }

    /// Construct a new bound from an pair of Len and Capacity with the same value.
    ///
    /// Note that the invariant of `ExactSize` is that all `Len` are guaranteed to be at most the
    /// size and all `Capacity` are guaranteed to be at least the size. The only possible overlap
    /// between the two is the exact length, which we can dynamically check.
    pub fn with_matching_pair(len: Len<T>, cap: Capacity<T>) -> Option<Self> {
        if len.get() == cap.get() {
            Some(ExactSize {
                inner: Len {
                    len: len.get(),
                    tag: len.tag,
                },
            })
        } else {
            None
        }
    }
}

impl<A: Tag> Eq<A, A> {
    /// Construct the reflexive proof.
    pub fn reflexive(tag: A) -> Self {
        Eq { a: tag, b: tag }
    }
}

impl<A: Tag, B: Tag> Eq<A, B> {
    /// Create an equality from evidence `a <= b <= a`.
    pub fn new(lhs: LessEq<A, B>, _: LessEq<B, A>) -> Self {
        Eq { a: lhs.a, b: lhs.b }
    }

    /// Swap the two tags, `a = b` iff `b = a`.
    pub fn transpose(self) -> Eq<B, A> {
        Eq {
            a: self.b,
            b: self.a,
        }
    }

    /// Relax this into a less or equal relation.
    pub fn into_le(self) -> LessEq<A, B> {
        LessEq {
            a: self.a,
            b: self.b,
        }
    }
}

impl<A: Tag> LessEq<A, A> {
    /// Construct the reflexive proof.
    pub fn reflexive(tag: A) -> Self {
        LessEq { a: tag, b: tag }
    }
}

impl<A: Tag, B: Tag> LessEq<A, B> {
    /// Construct the proof from the sizes of A and B.
    pub fn with_sizes(a: ExactSize<A>, b: ExactSize<B>) -> Option<Self> {
        if a.get() <= b.get() {
            Some(LessEq {
                a: a.inner.tag,
                b: b.inner.tag,
            })
        } else {
            None
        }
    }

    /// Construct the proof from a pair of bounds for A and B.
    ///
    /// The `Capacity` upper bounds all indices applicable to A, and the exact size. The `Len`
    /// lower bounds all lengths and the exact size.
    ///
    /// This returns `Some` when the lower bound for B is not smaller than the upper bound for A.
    pub fn with_pair(a: Capacity<A>, b: Len<B>) -> Option<Self> {
        if b.get() >= a.get() {
            Some(LessEq { a: a.tag, b: b.tag })
        } else {
            None
        }
    }
}

impl<T> Named<T> {
    /// Create a new named tag.
    ///
    /// The instance is only to be encouraged to only use types private to your crate or module,
    /// this method immediately *forgets* the instance which is currently required for `const`ness.
    pub const fn new(t: T) -> Self {
        // Const-fn does not allow dropping values. We don't want (and can't have) `T: Copy` so we
        // need to statically prove this to rustc by actually removing the drop call.
        let _ = core::mem::ManuallyDrop::new(t);
        Named {
            phantom: PhantomData,
        }
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

impl<T, I> Idx<I, T> {
    /// Get the inner index.
    pub fn into_inner(self) -> I {
        self.idx
    }

    /// Interpret this as an index into a larger slice.
    pub fn with_tag<NewT>(self, larger: LessEq<T, NewT>) -> Idx<I, NewT> {
        Idx {
            idx: self.idx,
            tag: larger.b,
        }
    }
}

impl<T> Idx<usize, T> {
    /// Create a smaller index.
    #[must_use = "Returns a new index"]
    pub fn saturating_sub(self, sub: usize) -> Self {
        Idx {
            idx: self.idx.saturating_sub(sub),
            tag: self.tag,
        }
    }

    /// Bound the index from above.
    #[must_use = "Returns a new index"]
    pub fn truncate(self, min: usize) -> Self {
        Idx {
            idx: self.idx.min(min),
            tag: self.tag,
        }
    }

    /// Return the range that contains this element.
    #[must_use = "Returns a new index"]
    pub fn into_range(self) -> Idx<core::ops::Range<usize>, T> {
        Idx {
            idx: self.idx..self.idx + 1,
            tag: self.tag,
        }
    }

    /// Get a length up-to, not including this index.
    #[must_use = "Returns a new index"]
    pub fn into_len(self) -> Len<T> {
        Len {
            len: self.idx,
            tag: self.tag,
        }
    }

    /// Get the length beyond this index.
    ///
    /// Unlike turning it into a range and using its end, this guarantees that the end is non-zero
    /// as it knows the range not to be empty.
    #[must_use = "Returns a new index"]
    pub fn into_end(self) -> NonZeroLen<T> {
        NonZeroLen {
            len: NonZeroUsize::new(self.idx + 1).unwrap(),
            tag: self.tag,
        }
    }
}

impl<T> Idx<RangeTo<usize>, T> {
    /// Get a length up-to, not including this index.
    #[must_use = "Returns a new index"]
    pub fn into_end(self) -> Len<T> {
        Len {
            len: self.idx.end,
            tag: self.tag,
        }
    }

    /// Construct an index starting at an element.
    ///
    /// This method return `Some` when `from` does not exceed the end index.
    #[must_use = "Returns a new index"]
    pub fn range_from(self, from: Len<T>) -> Option<Idx<core::ops::Range<usize>, T>> {
        if from.len <= self.idx.end {
            Some(Idx {
                idx: from.len..self.idx.end,
                tag: self.tag,
            })
        } else {
            None
        }
    }
}

impl<T> Idx<RangeFrom<usize>, T> {
    /// Get a length up-to, not including this index.
    #[must_use = "Returns a new index"]
    pub fn into_start(self) -> Len<T> {
        Len {
            len: self.idx.start,
            tag: self.tag,
        }
    }

    /// Construct an index up to at an element.
    ///
    /// This method return `Some` when `to` does not exceed the end index.
    #[must_use = "Returns a new index"]
    pub fn range_to(self, to: Len<T>) -> Option<Idx<core::ops::Range<usize>, T>> {
        if to.len >= self.idx.start {
            Some(Idx {
                idx: self.idx.start..to.len,
                tag: self.tag,
            })
        } else {
            None
        }
    }
}

impl<T> Idx<Range<usize>, T> {
    /// Get a length up-to, not including this index.
    #[must_use = "Returns a new index"]
    pub fn into_start(self) -> Len<T> {
        Len {
            len: self.idx.start,
            tag: self.tag,
        }
    }

    /// Get a length up-to, not including this index.
    #[must_use = "Returns a new index"]
    pub fn into_end(self) -> Len<T> {
        Len {
            len: self.idx.end,
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
        if slice.len() >= size.into_len().get() {
            Some(Ref {
                slice,
                tag: size.inner.tag,
            })
        } else {
            None
        }
    }

    /// Unsafely wrap a slice into an index wrapper.
    ///
    /// # Safety
    ///
    /// The caller must uphold that the _exact size_ associated with the type `Tag` (see
    /// [`ExactSize::new_untagged`]) is at most as large as the length of this slice.
    pub unsafe fn new_unchecked(slice: &'slice [E], tag: T) -> Self {
        Ref { slice, tag }
    }

    /// Get the length as a `Capacity` of all slices with this tag.
    pub fn capacity(&self) -> Capacity<T> {
        Capacity {
            len: self.len(),
            tag: self.tag,
        }
    }

    /// Index the slice unchecked but soundly.
    pub fn get_safe<I: core::slice::SliceIndex<[E]>>(&self, index: Idx<I, T>) -> &I::Output {
        unsafe { self.slice.get_unchecked(index.idx) }
    }

    /// Index the slice unchecked but soundly.
    pub fn into_safe<I: core::slice::SliceIndex<[E]>>(self, index: Idx<I, T>) -> &'slice I::Output {
        unsafe { self.slice.get_unchecked(index.idx) }
    }

    /// Unwrap the inner slice, dropping all assertions of safe indexing.
    pub fn into_inner(self) -> &'slice [E] {
        self.slice
    }

    /// Interpret this as a slice with smaller length.
    pub fn with_tag<NewT>(self, smaller: LessEq<NewT, T>) -> Ref<'slice, E, NewT> {
        Ref {
            slice: self.slice,
            tag: smaller.a,
        }
    }
}

impl<'slice, T: Tag, E> Mut<'slice, E, T> {
    /// Try to wrap a slice into a safe index wrapper.
    ///
    /// Returns `Some(_)` if the slice is at least as long as the `size` requires, otherwise
    /// returns `None`.
    pub fn new(slice: &'slice mut [E], size: ExactSize<T>) -> Option<Self> {
        if slice.len() >= size.into_len().get() {
            Some(Mut {
                slice,
                tag: size.inner.tag,
            })
        } else {
            None
        }
    }

    /// Unsafely wrap a slice into an index wrapper.
    ///
    /// # Safety
    ///
    /// The caller must uphold that the _exact size_ associated with the type `Tag` (see
    /// [`ExactSize::new_untagged`]) is at most as large as the length of this slice.
    pub unsafe fn new_unchecked(slice: &'slice mut [E], tag: T) -> Self {
        Mut { slice, tag }
    }

    /// Get the length as a `Capacity` of all slices with this tag.
    pub fn capacity(&self) -> Capacity<T> {
        Capacity {
            len: self.len(),
            tag: self.tag,
        }
    }

    /// Index the slice unchecked but soundly.
    pub fn get_safe<I: core::slice::SliceIndex<[E]>>(&self, index: Idx<I, T>) -> &I::Output {
        unsafe { self.slice.get_unchecked(index.idx) }
    }

    /// Index the slice unchecked but soundly.
    pub fn into_safe<I: core::slice::SliceIndex<[E]>>(self, index: Idx<I, T>) -> &'slice I::Output {
        unsafe { self.slice.get_unchecked(index.idx) }
    }

    /// Mutably index the slice unchecked but soundly.
    pub fn get_safe_mut<I: core::slice::SliceIndex<[E]>>(
        &mut self,
        index: Idx<I, T>,
    ) -> &mut I::Output {
        unsafe { self.slice.get_unchecked_mut(index.idx) }
    }

    /// Index the slice unchecked but soundly.
    pub fn into_safe_mut<I: core::slice::SliceIndex<[E]>>(
        self,
        index: Idx<I, T>,
    ) -> &'slice mut I::Output {
        unsafe { self.slice.get_unchecked_mut(index.idx) }
    }

    /// Unwrap the inner slice, dropping all assertions of safe indexing.
    pub fn into_inner(self) -> &'slice [E] {
        self.slice
    }

    /// Interpret this as a slice with smaller length.
    pub fn with_tag<NewT>(self, smaller: LessEq<NewT, T>) -> Mut<'slice, E, NewT> {
        Mut {
            slice: self.slice,
            tag: smaller.a,
        }
    }
}

#[cfg(feature = "alloc")]
impl<T: Tag, E> Boxed<E, T> {
    /// Try to construct an asserted box, returning it on error.
    ///
    /// The box slice must have _exactly_ the length indicated.
    pub fn new(
        inner: alloc::boxed::Box<[E]>,
        len: ExactSize<T>,
    ) -> Result<Self, alloc::boxed::Box<[E]>> {
        match Ref::new(&*inner, len) {
            Some(_) => Ok(Boxed {
                inner,
                tag: len.inner.tag,
            }),
            None => Err(inner),
        }
    }

    /// Reference the contents as an asserted `Ref` slice.
    pub fn as_ref(&self) -> Ref<'_, E, T> {
        Ref {
            slice: &*self.inner,
            tag: self.tag,
        }
    }

    /// Reference the contents as an asserted mutable `Mut` slice.
    pub fn as_mut(&mut self) -> Mut<'_, E, T> {
        Mut {
            slice: &mut *self.inner,
            tag: self.tag,
        }
    }

    /// Get the length as a `Capacity` of all slices with this tag.
    pub fn capacity(&self) -> Capacity<T> {
        Capacity {
            len: self.inner.len(),
            tag: self.tag,
        }
    }

    /// Index the boxed slice unchecked but soundly.
    pub fn get_safe<I: core::slice::SliceIndex<[E]>>(&self, index: Idx<I, T>) -> &I::Output {
        self.as_ref().into_safe(index)
    }

    /// Mutably index the boxed slice unchecked but soundly.
    pub fn get_safe_mut<I: core::slice::SliceIndex<[E]>>(
        &mut self,
        index: Idx<I, T>,
    ) -> &mut I::Output {
        self.as_mut().into_safe_mut(index)
    }

    /// Unwrap the inner box, dropping all assertions of safe indexing.
    pub fn into_inner(self) -> alloc::boxed::Box<[E]> {
        self.inner
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
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Named<T> {}

impl<T> Clone for Constant<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Constant<T> {}

impl<T: ConstantSource> Constant<T> {
    pub const EXACT_SIZE: ExactSize<Self> =
        // SAFETY: all instances have the same length, `LEN`.
        unsafe { ExactSize::new_untagged(T::LEN, Constant(PhantomData)) };
}

impl<const N: usize> Const<N> {
    pub const EXACT_SIZE: ExactSize<Self> =
        // SAFETY: all instances have the same length, `N`.
        unsafe { ExactSize::new_untagged(N, Const) };

    pub fn to_ref<'slice, T>(self, arr: &'slice [T; N])
        -> Ref<'slice, T, Self>
    {
        unsafe { Ref::new_unchecked(&arr[..], self) }
    }
}

#[cfg(feature = "alloc")]
mod impl_of_boxed_idx {
    use super::{ExactSize, Idx, IdxBox, Len, Tag};
    use core::ops::{RangeFrom, RangeTo};

    /// Sealed trait, quite unsafe..
    pub trait HiddenMaxIndex: Sized {
        fn exclusive_upper_bound(this: &[Self]) -> Option<usize>;
    }

    impl HiddenMaxIndex for usize {
        fn exclusive_upper_bound(this: &[Self]) -> Option<usize> {
            this.iter()
                .copied()
                .max()
                .map_or(Some(0), |idx| idx.checked_add(1))
        }
    }

    impl HiddenMaxIndex for RangeFrom<usize> {
        fn exclusive_upper_bound(this: &[Self]) -> Option<usize> {
            this.iter().map(|range| range.start).max()
        }
    }

    impl HiddenMaxIndex for RangeTo<usize> {
        fn exclusive_upper_bound(this: &[Self]) -> Option<usize> {
            this.iter().map(|range| range.end).max()
        }
    }

    impl<I: HiddenMaxIndex> IdxBox<I> {
        /// Wrap an allocation of indices.
        /// This will fail if it not possible to express the lower bound of slices for which all
        /// indices are valid, as a `usize`. That is, if any of the indices references the element
        /// with index `usize::MAX` itself.
        pub fn new(indices: alloc::boxed::Box<[I]>) -> Result<Self, alloc::boxed::Box<[I]>> {
            match HiddenMaxIndex::exclusive_upper_bound(&indices[..]) {
                Some(upper_bound) => Ok(IdxBox {
                    indices,
                    exact_size: upper_bound,
                }),
                None => Err(indices),
            }
        }

        /// Return the upper bound over all indices.
        /// This is not guaranteed to be the _least_ upper bound.
        pub fn bound(&self) -> usize {
            self.exact_size
        }

        /// Ensure that the stored `bound` is at least `min`.
        pub fn ensure(&mut self, min: usize) {
            self.exact_size = self.exact_size.max(min);
        }

        /// Set the bound to the least upper bound of all indices.
        ///
        /// This always reduces the `bound` and there can not be any lower bound that is consistent
        /// with all indices stored in this `IdxBox`.
        pub fn truncate(&mut self) {
            let least_bound = HiddenMaxIndex::exclusive_upper_bound(&self.indices)
                // All mutation was performed under some concrete upper bound, and current elements
                // must still be bounded by the largest such bound.
                .expect("Some upper bound must still apply");
            debug_assert!(
                self.exact_size >= least_bound,
                "The exact size was corrupted to be below the least bound."
            );
            self.exact_size = least_bound;
        }

        /// Reinterpret the contents as indices of a given tag.
        ///
        /// The given size must not be smaller than the `bound` of this allocated. This guarantees
        /// that all indices within the box are valid for the Tag. Since you can only _view_ the
        /// indices, they will remain valid.
        pub fn as_ref<T: Tag>(&self, size: Len<T>) -> Option<&'_ [Idx<I, T>]> {
            if size.get() >= self.exact_size {
                Some(unsafe {
                    // SAFETY: `Idx` is a transparent wrapper around `I`, the type of this slice,
                    // and the type `T` is a ZST. The instance `size.tag` also proves that this ZST
                    // is inhabited and it is Copy as per requirements of `Tag`. The index is
                    // smaller than the ExactSize corresponding to `T` by transitivity over `size`.
                    let content: *const [I] = &self.indices[..];
                    &*(content as *const [Idx<I, T>])
                })
            } else {
                None
            }
        }

        /// Reinterpret the contents as mutable indices of a given tag.
        ///
        /// The given exact size must not be exactly the same as the `bound` of this allocated
        /// slice. This guarantees that all indices within the box are valid for the Tag, and that
        /// all stored indices will be valid for all future tags.
        pub fn as_mut<T: Tag>(&mut self, size: ExactSize<T>) -> Option<&'_ mut [Idx<I, T>]> {
            if size.get() == self.exact_size {
                Some(unsafe {
                    // SAFETY: `Idx` is a transparent wrapper around `I`, the type of this slice,
                    // and the type `T` is a ZST. The instance `size.tag` also proves that this ZST
                    // is inhabited and it is Copy as per requirements of `Tag`. The index is
                    // smaller than the ExactSize corresponding to `T` by transitivity over `size`.
                    // Also any instance written will be smaller than `self.exact_size`,
                    // guaranteeing that the invariants of this type hold afterwards.
                    let content: *mut [I] = &mut self.indices[..];
                    &mut *(content as *mut [Idx<I, T>])
                })
            } else {
                None
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{with_ref, Constant, ConstantSource, Eq, LessEq, Mut};

    #[test]
    fn basics() {
        fn problematic(buf: &mut [u8], offsets: &[u8], idx: usize) {
            with_ref(&offsets[..=idx], |offsets, size| {
                let mut idx = size.into_len().index(idx).unwrap();
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

    #[test]
    fn tag_switching() {
        struct ConstantLen;
        impl ConstantSource for ConstantLen {
            const LEN: usize = 4;
        }

        let mut buffer = [0u8; 4];
        let csize = Constant::<ConstantLen>::EXACT_SIZE;

        let slice = Mut::new(&mut buffer[..], csize).unwrap();
        assert_eq!(slice.len(), ConstantLen::LEN);
        let all = csize.into_len().range_to_self();

        with_ref(&buffer[..], |slice, size| {
            let lesseq = LessEq::with_sizes(size, csize).unwrap();
            let moreeq = LessEq::with_sizes(csize, size).unwrap();
            // 'prove': csize = size
            let eq = Eq::new(lesseq, moreeq).transpose();

            // Use this to transport the index.
            let all = all.with_tag(eq.into_le());
            let safe = slice.get_safe(all);
            assert_eq!(safe.len(), ConstantLen::LEN);

            assert_eq!(csize.with_tag(eq).get(), csize.get());
        });
    }

    #[test]
    fn bad_inequalities() {
        struct SmallLen;
        struct LargeLen;
        impl ConstantSource for SmallLen {
            const LEN: usize = 1;
        }
        impl ConstantSource for LargeLen {
            const LEN: usize = 2;
        }

        let small = Constant::<SmallLen>::EXACT_SIZE;
        let large = Constant::<LargeLen>::EXACT_SIZE;

        assert!(
            LessEq::with_pair(small.into_capacity(), large.into_len()).is_some(),
            "Small is in fact less than large"
        );
        assert!(
            LessEq::with_pair(large.into_capacity(), small.into_len()).is_none(),
            "Large should not appear less than small"
        );
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn idx_boxing() {
        use super::IdxBox;
        use alloc::boxed::Box;

        struct ExactBound;
        struct LargerBound;

        impl ConstantSource for ExactBound {
            const LEN: usize = 3;
        }

        impl ConstantSource for LargerBound {
            const LEN: usize = 4;
        }

        let indices = Box::from([0, 1, 2]);

        let mut boxed = IdxBox::new(indices).expect("Have a valid upper bound");
        assert_eq!(boxed.bound(), <ExactBound as ConstantSource>::LEN);

        let exact = Constant::<ExactBound>::EXACT_SIZE;
        boxed.as_ref(exact.into_len()).expect("A valid upper bound");
        let larger = Constant::<LargerBound>::EXACT_SIZE;
        boxed
            .as_ref(larger.into_len())
            .expect("A valid upper bound");

        boxed.as_mut(exact).expect("A valid exact bound");
        assert!(boxed.as_mut(larger).is_none(), "An invalid exact bound");

        // Now increase the bound
        boxed.ensure(larger.get());
        assert_eq!(boxed.bound(), <LargerBound as ConstantSource>::LEN);
        assert!(
            boxed.as_mut(exact).is_none(),
            "No longer a valid exact bound"
        );
        boxed.as_mut(larger).expect("Now a valid exact bound");

        // But we've not _actually_ changed any index, so go back.
        boxed.truncate();
        assert_eq!(boxed.bound(), <ExactBound as ConstantSource>::LEN);

        boxed.as_mut(exact).expect("A valid exact bound");
        assert!(boxed.as_mut(larger).is_none(), "An invalid exact bound");
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
extern "C" {}

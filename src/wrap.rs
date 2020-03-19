use core::{
    borrow::{Borrow, BorrowMut},
    cmp::Ordering,
    convert::TryFrom,
    fmt, hash,
    hash::Hash,
    ops::{Index, IndexMut},
    slice::SliceIndex,
};

use crate::{iter::IterMove, Array, ArrayExt, ArrayShorthand, SizeError};

/// Wrapper over array types. It implements the same[^1] traits as
/// [`array`], but not for only arrays of sizes `0..=32` but **for all arrays,
/// those sizes are supported by the crate**[^2]:
/// - [`Debug`]
/// - [`IntoIterator`]
/// - [`PartialEq`], [`PartialOrd`], [`Eq`], [`Ord`]
/// - [`Hash`]
/// - [`AsRef`], [`AsMut`] (both for `A` and `[A::Item]`)
/// - [`Borrow`], [`BorrowMut`]
/// - [`Index`], [`IndexMut`]
/// - [`Default`]
/// - [`TryFrom`]
///
/// Note: Implementations of the most trai just copy-pasted from std
///
/// [`array`]: https://doc.rust-lang.org/std/primitive.array.html
/// [`Debug`]: core::fmt::Debug
/// [`IntoIterator`]: core::iter::IntoIterator
/// [`PartialEq`]: core::cmp::PartialEq
/// [`PartialOrd`]: core::cmp::PartialOrd
/// [`Eq`]: core::cmp::Eq
/// [`Ord`]: core::cmp::Ord
/// [`Hash`]: core::hash::Hash
/// [`AsRef`]: core::convert::AsRef
/// [`AsMut`]: core::convert::AsMut
/// [`Borrow`]: core::borrow::Borrow
/// [`BorrowMut`]: core::borrow::BorrowMut
/// [`Index`]: core::ops::Index
/// [`IndexMut`]: core::ops::IndexMut
/// [`Default`]: core::default::Default
/// [`TryFrom`]: core::convert::TryFrom
///
/// ## Examples
///
/// [`PartialEq`]/[`Eq`] :
/// ```
/// use arraylib::{ArrayExt, ArrayWrapper};
///
/// let arr = [1, 2, 3].wrap();
/// assert_eq!(arr, [1, 2, 3]);
/// assert_eq!(format!("{:?}", arr), "[1, 2, 3]");
/// assert!(arr < [1, 4, 0]);
/// assert_eq!(arr[1], 2);
///
/// assert!(arr.into_iter().eq(vec![1, 2, 3].into_iter()));
///
/// assert_eq!(<ArrayWrapper<[i32; 3]> as Default>::default(), [0, 0, 0]);
/// ```
///
/// ```
/// use arraylib::{ArrayExt, ArrayWrapper};
/// use std::borrow::{Borrow, BorrowMut};
///
/// let mut arr = [1, 2, 3].wrap();
///
/// let slice: &[i32] = arr.as_ref();
/// assert_eq!(slice, &[1, 2, 3]);
/// ```
/// ```
/// use arraylib::ArrayExt;
/// use std::{
///     collections::hash_map::DefaultHasher,
///     hash::{Hash, Hasher},
/// };
///
/// let mut hasher = DefaultHasher::new();
/// [1, 2, 3].wrap().hash(&mut hasher);
/// let hash0 = hasher.finish();
///
/// let mut hasher = DefaultHasher::new();
/// [1, 2, 3].hash(&mut hasher);
/// let hash1 = hasher.finish();
///
/// assert_eq!(hash0, hash1);
/// ```
/// In difference with std, `ArrayWrapper` _is_ iterable:
/// ```
/// use arraylib::ArrayExt;
///
/// let arr = [0, 3, 45, 91].wrap();
/// for x in arr {}
/// ```
// [^2] goes before [^1] because otherwise rustdoc parses it the wrong way ¯\_(ツ)_/¯
///
/// [^2]: See [Sizes Limitations](./index.html#sizes-limitations) paragraph in
/// crate docs.
///
/// [^1]: differences:
///   - IntoIterator (on std's [`array`] `IntoIterator` is implemented only on
///     `&[T; N]` and on `&mut [T; N]` while on ArrayWrapper it's implemented
///     directly (using [`IterMove`]))
///   - In some traits instead of [`TryFromSliceError`] there is [`SizeError`]
///   - [`Copy`]/[`Clone`] are implemented only when `A: Copy/Clone` and not
///     when `A::Item: Copy/Clone` because we can't use compiler magic :(
///
/// [`TryFromSliceError`]: core::array::TryFromSliceError
/// [`SizeError`]: crate::SizeError
/// [`IterMove`]: crate::iter::IterMove
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct ArrayWrapper<A> {
    array: A,
}

impl<A> ArrayWrapper<A>
where
    A: Array,
{
    /// Create new `ArrayWrapper`
    ///
    /// ```
    /// use arraylib::ArrayWrapper;
    ///
    /// let arr = ArrayWrapper::new([0, 1, 2, 3]);
    /// println!("{:?}", arr);
    /// ```
    #[inline]
    pub fn new(inner: A) -> Self {
        Self { array: inner }
    }

    /// Destruct `ArrayWrapper` into inner array
    ///
    /// ```
    /// use arraylib::ArrayWrapper;
    ///
    /// let arr = ArrayWrapper::new([0, 1, 2, 3]);
    /// // ...
    /// let arr = arr.into_inner();
    /// println!("{:?}", arr);
    /// ```
    #[inline]
    pub fn into_inner(self) -> A {
        self.array
    }
}

impl<A> AsRef<A> for ArrayWrapper<A> {
    #[inline]
    fn as_ref(&self) -> &A {
        &self.array
    }
}

impl<A> AsMut<A> for ArrayWrapper<A> {
    #[inline]
    fn as_mut(&mut self) -> &mut A {
        &mut self.array
    }
}

impl<A> AsRef<[A::Item]> for ArrayWrapper<A>
where
    A: Array,
{
    #[inline]
    fn as_ref(&self) -> &[A::Item] {
        &self[..]
    }
}

impl<A> AsMut<[A::Item]> for ArrayWrapper<A>
where
    A: Array,
{
    #[inline]
    fn as_mut(&mut self) -> &mut [A::Item] {
        &mut self[..]
    }
}

impl<A> Borrow<[A::Item]> for ArrayWrapper<A>
where
    A: Array,
{
    #[inline]
    fn borrow(&self) -> &[A::Item] {
        self.as_slice()
    }
}

impl<A> BorrowMut<[A::Item]> for ArrayWrapper<A>
where
    A: Array,
{
    #[inline]
    fn borrow_mut(&mut self) -> &mut [A::Item] {
        self.as_mut_slice()
    }
}

impl<A> Default for ArrayWrapper<A>
where
    A: Array,
    A::Item: Default,
{
    #[inline]
    fn default() -> Self {
        <_>::from_fn(|_| <_>::default())
    }
}

impl<A> TryFrom<&[A::Item]> for ArrayWrapper<A>
where
    A::Item: Copy,
    A: Array,
{
    type Error = SizeError;

    #[inline]
    fn try_from(slice: &[A::Item]) -> Result<Self, SizeError> {
        Self::from_slice(slice)
    }
}

/// ```
/// use arraylib::ArrayWrapper;
/// use core::convert::TryInto;
///
/// let slice = &[0, 1, 2][..];
/// let arr: &ArrayWrapper<[i32; 3]> = slice.try_into().unwrap();
/// assert_eq!(arr, &ArrayWrapper::new([0, 1, 2]))
/// ```
impl<'a, A> TryFrom<&'a [A::Item]> for &'a ArrayWrapper<A>
where
    A: Array,
{
    type Error = SizeError;

    #[inline]
    fn try_from(slice: &'a [A::Item]) -> Result<Self, SizeError> {
        // TODO: >=?
        if slice.len() == <ArrayWrapper<A>>::SIZE {
            unsafe {
                // ## Safety
                //
                // Slice and array of the same size must have the same ABI, so we can safely get
                // `&ArrayWrapper` from `&[A::Item]`.
                //
                // But we can't transmute slice ref directly to array ref because
                // first is fat pointer and second is not.
                Ok(&*(slice.as_ptr() as *const ArrayWrapper<A>))
            }
        } else {
            Err(SizeError::default())
        }
    }
}

/// ```
/// use arraylib::ArrayWrapper;
/// use core::convert::TryInto;
///
/// let slice = &mut [0, 1, 2][..];
/// let arr: &mut ArrayWrapper<[i32; 3]> = slice.try_into().unwrap();
/// assert_eq!(arr, &ArrayWrapper::new([0, 1, 2]))
/// ```
impl<'a, A> TryFrom<&'a mut [A::Item]> for &'a mut ArrayWrapper<A>
where
    A: Array,
{
    type Error = SizeError;

    #[inline]
    fn try_from(slice: &'a mut [A::Item]) -> Result<Self, SizeError> {
        // TODO: >=?
        if slice.len() == <ArrayWrapper<A>>::SIZE {
            unsafe {
                // ## Safety
                //
                // Slice and array of the same size must have the same ABI, so we can safely get
                // `&mut ArrayWrapper` from `&mut [A::Item]`.
                //
                // But we can't transmute slice ref directly to array ref because
                // first is fat pointer and second is not.
                Ok(&mut *(slice.as_mut_ptr() as *mut ArrayWrapper<A>))
            }
        } else {
            Err(SizeError::default())
        }
    }
}

impl<A> Hash for ArrayWrapper<A>
where
    A::Item: Hash,
    A: Array,
{
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        Hash::hash(&self[..], state)
    }
}

impl<A> Eq for ArrayWrapper<A>
where
    A: Array,
    A::Item: Eq,
{
}

impl<A, B> PartialOrd<B> for ArrayWrapper<A>
where
    A: Array,
    B: Array<Item = A::Item>, /* for some reason there is no impl of PartialOrd<[B]> for [A]
                               * where A: PartialOrd<B> */
    A::Item: PartialOrd,
{
    #[inline]
    fn partial_cmp(&self, other: &B) -> Option<Ordering> {
        PartialOrd::partial_cmp(&self[..], other.as_slice())
    }

    #[inline]
    fn lt(&self, other: &B) -> bool {
        PartialOrd::lt(&self[..], other.as_slice())
    }

    #[inline]
    fn le(&self, other: &B) -> bool {
        PartialOrd::le(&self[..], other.as_slice())
    }

    #[inline]
    fn gt(&self, other: &B) -> bool {
        PartialOrd::gt(&self[..], other.as_slice())
    }

    #[inline]
    fn ge(&self, other: &B) -> bool {
        PartialOrd::ge(&self[..], other.as_slice())
    }
}

impl<A> Ord for ArrayWrapper<A>
where
    A: Array,
    A::Item: Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(&&self[..], &&other[..])
    }
}

impl<A> fmt::Debug for ArrayWrapper<A>
where
    A::Item: fmt::Debug,
    A: Array,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&&self[..], f)
    }
}

impl<A> IntoIterator for ArrayWrapper<A>
where
    A: Array,
{
    type IntoIter = IterMove<Self>;
    type Item = A::Item;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IterMove::new(self)
    }
}

impl<A, B> PartialEq<B> for ArrayWrapper<A>
where
    A::Item: PartialEq<B::Item>,
    A: Array,
    B: Array,
{
    #[inline]
    fn eq(&self, other: &B) -> bool {
        &self[..] == other.as_slice()
    }
}

impl<A, T> PartialEq<ArrayWrapper<A>> for [T]
where
    T: PartialEq<A::Item>,
    A: Array,
{
    #[inline]
    fn eq(&self, other: &ArrayWrapper<A>) -> bool {
        self[..] == other[..]
    }
}

impl<'t, A, T> PartialEq<&'t [T]> for ArrayWrapper<A>
where
    A::Item: PartialEq<T>,
    A: Array,
{
    #[inline]
    fn eq(&self, other: &&'t [T]) -> bool {
        self[..] == other[..]
    }
}

impl<'t, A, T> PartialEq<ArrayWrapper<A>> for &'t [T]
where
    T: PartialEq<A::Item>,
    A: Array,
{
    #[inline]
    fn eq(&self, other: &ArrayWrapper<A>) -> bool {
        self[..] == other[..]
    }
}

impl<'t, A, T> PartialEq<&'t mut [T]> for ArrayWrapper<A>
where
    A::Item: PartialEq<T>,
    A: Array,
{
    #[inline]
    fn eq(&self, other: &&'t mut [T]) -> bool {
        self[..] == other[..]
    }
}

impl<'t, A, T> PartialEq<ArrayWrapper<A>> for &'t mut [T]
where
    T: PartialEq<A::Item>,
    A: Array,
{
    #[inline]
    fn eq(&self, other: &ArrayWrapper<A>) -> bool {
        self[..] == other[..]
    }
}

impl<A, T> PartialEq<[T]> for ArrayWrapper<A>
where
    A::Item: PartialEq<T>,
    A: Array,
{
    #[inline]
    fn eq(&self, other: &[T]) -> bool {
        self[..] == other[..]
    }
}

/// ## Safety
///
/// `ArrayWrapper` has `#[repr(transparent)]` so it has the same ABI as `A`.
/// So if `A` is array then so is `ArrayWrapper`.
unsafe impl<A> Array for ArrayWrapper<A>
where
    A: Array,
{
    type Item = A::Item;
    type Maybe = ArrayWrapper<A::Maybe>;

    const SIZE: usize = A::SIZE;

    #[inline]
    fn as_slice(&self) -> &[Self::Item] {
        self.array.as_slice()
    }

    #[inline]
    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        self.array.as_mut_slice()
    }

    #[inline]
    fn try_unfold<St, F, E>(init: St, f: F) -> Result<Self, E>
    where
        F: FnMut(&mut St) -> Result<Self::Item, E>,
    {
        Ok(Self {
            array: A::try_unfold(init, f)?,
        })
    }

    #[inline]
    fn unfold<St, F>(init: St, f: F) -> Self
    where
        F: FnMut(&mut St) -> Self::Item,
    {
        Self {
            array: A::unfold(init, f),
        }
    }

    #[inline]
    fn try_from_fn<F, E>(f: F) -> Result<Self, E>
    where
        F: FnMut(usize) -> Result<Self::Item, E>,
    {
        Ok(Self {
            array: A::try_from_fn(f)?,
        })
    }

    #[inline]
    fn from_fn<F>(f: F) -> Self
    where
        F: FnMut(usize) -> Self::Item,
    {
        Self {
            array: A::from_fn(f),
        }
    }

    #[inline]
    fn from_iter<I>(iter: I) -> Option<Self>
    where
        I: IntoIterator<Item = Self::Item>,
    {
        A::from_iter(iter.into_iter()).map(|array| Self { array })
    }

    #[inline]
    fn into_uninit(self) -> Self::Maybe {
        Self::Maybe {
            array: self.array.into_uninit(),
        }
    }
}

impl<A, Idx> Index<Idx> for ArrayWrapper<A>
where
    A: Array,
    Idx: SliceIndex<[A::Item]>,
{
    type Output = Idx::Output;

    #[inline]
    fn index(&self, index: Idx) -> &Self::Output {
        self.array.index(index)
    }
}

impl<A, Idx> IndexMut<Idx> for ArrayWrapper<A>
where
    A: Array,
    Idx: SliceIndex<[A::Item]>,
{
    #[inline]
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        self.array.index_mut(index)
    }
}

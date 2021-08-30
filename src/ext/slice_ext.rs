use core::mem::MaybeUninit;

use crate::{iter::ArrayWindows, Array, SizeError};

/// Extension for [`slice`]
///
/// [`slice`]: core::slice
pub trait Slice {
    /// Item of the slice, i.e.
    /// ```
    /// # use arraylib::Slice; fn dummy<T>() where
    /// [T]: Slice<Item = T>
    /// # {}
    /// ```
    type Item;

    /// Copy `self` into an owned array.
    /// Return `Err(SizeError)` if len of `self` is not equal to `A::SIZE`.
    ///
    /// ## Examples
    ///
    /// ```
    /// use arraylib::Slice;
    ///
    /// let slice: &[i32] = &[0, 1, 2, 3, 4];
    /// let array: [i32; 5] = slice.copied().unwrap();
    /// assert_eq!(array, [0, 1, 2, 3, 4]);
    /// ```
    ///
    /// ```
    /// use arraylib::{SizeError, Slice};
    ///
    /// let slice: &[i32] = &[0, 1, 2, 3, 4];
    /// let result = slice.copied::<2>();
    /// assert_eq!(result, Err(SizeError::default()));
    /// ```
    fn copied<const N: usize>(&self) -> Result<[Self::Item; N], SizeError>
    where
        Self::Item: Copy;

    /// Clone `self` into an owned array.
    /// Return `Err(SizeError)` if len of `self` is not equal to `A::SIZE`.
    ///
    /// ## Examples
    ///
    /// ```
    /// use arraylib::Slice;
    /// use core::ops::Range;
    ///
    /// // Range is not `Copy`
    /// let slice: &[Range<usize>] = &[0..1, 1..3, 2..10];
    /// let array: [Range<usize>; 3] = slice.cloned().unwrap();
    /// assert_eq!(array, [0..1, 1..3, 2..10]);
    /// ```
    ///
    /// ```
    /// use arraylib::{SizeError, Slice};
    /// use core::ops::Range;
    ///
    /// let slice: &[Range<usize>] = &[0..1, 1..3, 2..10];
    /// let result = slice.cloned::<5>();
    /// assert_eq!(result, Err(SizeError::default()));
    /// ```
    fn cloned<const N: usize>(&self) -> Result<[Self::Item; N], SizeError>
    where
        Self::Item: Clone;

    /// Returns an iterator over all contiguous windows of type `A` (length
    /// `A::SIZE`). The windows overlap. If the slice is shorter than size
    /// (`A::SIZE`), the iterator returns `None`.
    ///
    /// ## Panics
    ///
    /// Panics if `A::SIZE` is 0 (`A = [T; 0]`).
    ///
    /// ## Examples
    ///
    /// ```
    /// use arraylib::Slice;
    ///
    /// let mut iter = [1, 2, 3, 4].array_windows_();
    /// assert_eq!(iter.next(), Some(&[1, 2]));
    /// assert_eq!(iter.next(), Some(&[2, 3]));
    /// assert_eq!(iter.next(), Some(&[3, 4]));
    /// assert_eq!(iter.next(), None);
    /// ```
    ///
    /// In difference with [`<[T]>::windows`][windows], this method returns
    /// iterator that returns _arrays_, so you can use array destruction:
    ///
    /// [windows]: https://doc.rust-lang.org/std/primitive.slice.html#method.windows
    ///
    /// ```
    /// use arraylib::Slice;
    ///
    /// assert_eq!(
    ///     [1, 2, 3, 4, 5]
    ///         .array_windows_()
    ///         .map(|[a, b, c]| a + b + c)
    ///         .sum::<u32>(),
    ///     27
    /// )
    /// ```
    ///
    /// If the slice is shorter than size:
    ///
    /// ```
    /// use arraylib::Slice;
    ///
    /// let slice = ['f', 'o', 'o'];
    /// let mut iter = slice.array_windows_::<4>();
    /// assert!(iter.next().is_none());
    /// ```
    fn array_windows_<const N: usize>(&self) -> ArrayWindows<Self::Item, N>;
}

/// Extension for maybe uninitialized slices (`[MaybeUninit<_>]`)
pub trait MaybeUninitSlice:
    Slice<Item = MaybeUninit<<Self as MaybeUninitSlice>::InitItem>>
{
    /// Initialized item i.e.
    /// ```
    /// # use std::mem::MaybeUninit;
    /// # use arraylib::MaybeUninitSlice;
    /// # fn dummy<T>()
    /// # where
    /// [MaybeUninit<T>]: MaybeUninitSlice<InitItem = T>
    /// # {}
    /// ```
    type InitItem;

    /// Assume that all items of self are initialized
    ///
    /// ## Safety
    ///
    /// It is up to the caller to guarantee that all elements of the array are
    /// really in an initialized state. Calling this when the content is not
    /// yet fully initialized causes immediate undefined behavior. The
    /// [`MaybeUninit's` type-level documentation][inv] contains
    /// more information about this initialization invariant.
    ///
    /// See also [`MaybeUninit::assume_init`] documentation.
    ///
    /// [inv]: core::mem#initialization-invariant
    /// [`MaybeUninit::assume_init`]: core::mem::MaybeUninit::assume_init
    unsafe fn assume_init(&self) -> &[Self::InitItem];

    /// Assume that all items of self are initialized
    ///
    /// ## Safety
    ///
    /// It is up to the caller to guarantee that all elements of the array are
    /// really in an initialized state. Calling this when the content is not
    /// yet fully initialized causes immediate undefined behavior. The
    /// [`MaybeUninit's` type-level documentation][inv] contains
    /// more information about this initialization invariant.
    ///
    /// See also [`MaybeUninit::assume_init`] documentation.
    ///
    /// [inv]: core::mem#initialization-invariant
    /// [`MaybeUninit::assume_init`]: core::mem::MaybeUninit::assume_init
    unsafe fn assume_init_mut(&mut self) -> &mut [Self::InitItem];
}

impl<T> Slice for [T] {
    type Item = T;

    #[inline]
    fn copied<const N: usize>(&self) -> Result<[Self::Item; N], SizeError>
    where
        Self::Item: Copy,
    {
        Array::from_slice(self)
    }

    #[inline]
    fn cloned<const N: usize>(&self) -> Result<[Self::Item; N], SizeError>
    where
        Self::Item: Clone,
    {
        Array::clone_from_slice(self)
    }

    #[inline]
    fn array_windows_<const N: usize>(&self) -> ArrayWindows<Self::Item, N> {
        ArrayWindows::new(self)
    }
}

impl<T> MaybeUninitSlice for [MaybeUninit<T>] {
    type InitItem = T;

    #[inline]
    unsafe fn assume_init(&self) -> &[Self::InitItem] {
        // # Unsafety
        //
        // Behavior is undefined if any of `MaybeUninit`s in `self` is in the
        // `uninit` state
        //ref_cast::<[MaybeUninit<T>], [T]>(self)
        &*(self as *const [MaybeUninit<T>] as *const [T])
    }

    #[inline]
    unsafe fn assume_init_mut(&mut self) -> &mut [Self::InitItem] {
        // # Unsafety
        //
        // Behavior is undefined if any of `MaybeUninit`s in `self` is in the
        // `uninit` state
        &mut *(self as *mut [MaybeUninit<T>] as *mut [T])
    }
}

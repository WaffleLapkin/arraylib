use core::{mem::MaybeUninit, slice};

use crate::{iter::ArrayWindows, Array, SizeError};

/// Continuous data structure consisting of [`len`] [`Item`]s. ie an [`array`]
/// or a [`slice`].
///
/// [`len`]: Continuous::len
/// [`Item`]: Continuous::Item
/// [`array`]: array
/// [`slice`]: prim@slice
///
/// This trait mostly consists of shorthand methods those just refer to
/// `self.as_slice().smt()`.
///
/// ## Safety
///
/// Implementors of this trait must be layout compatible with an array (slice)
/// and [`Self::Uninit`]. All functions must be pure (ie not have side effects,
/// return the same value for the same output). [`len`] must be identical to
/// `.as_slice().len()` or `.as_mut_slice().len()`. [`as_slice`],
/// [`as_mut_slice`], [`as_ref`] and [`as_mut`] must return the same values
/// (ignoring the reference type).
///
/// [`Self::Uninit`]: Continuous::Uninit
/// [`as_slice`]: Continuous::as_slice
/// [`as_mut_slice`]: Continuous::as_mut_slice
/// [`as_ref`]: AsRef::as_ref
/// [`as_mut`]: AsMut::as_mut
pub unsafe trait Continuous: AsRef<[Self::Item]> + AsMut<[Self::Item]> {
    /// Type of the Items in the array or slice. i.e.
    /// ```
    /// # use arraylib::Continuous; fn dummy<T>() where
    /// [T; 4]: Continuous<Item = T>,
    /// [T]: Continuous<Item = T>
    /// # {}
    /// ```
    type Item;

    /// Same array or slice but item is wrapped with
    /// [`MaybeUninit<_>`](core::mem::MaybeUninit).
    /// ```
    /// # use {arraylib::Continuous, core::mem::MaybeUninit}; fn dummy<T>() where
    /// [T; 4]: Continuous<Uninit = [MaybeUninit<T>; 4]>,
    /// [T]: Continuous<Uninit = [MaybeUninit<T>]>
    /// # {}
    /// ```
    type Uninit: ?Sized + Continuous<Item = MaybeUninit<Self::Item>>;

    /// Extracts a slice containing the entire array or noop for slices.
    ///
    /// ## Example
    ///
    /// ```
    /// use arraylib::Continuous;
    ///
    /// let array = [1, 2, 3];
    /// assert_eq!(array.as_slice()[1..], [2, 3]);
    ///
    /// let slice = &[1, 2, 3] as &[_];
    /// assert_eq!(array.as_slice()[1..], [2, 3]);
    /// ```
    fn as_slice(&self) -> &[Self::Item];

    /// Extracts a mutable slice containing the entire array or noop for slices.
    ///
    /// ## Example
    ///
    /// ```
    /// use arraylib::Continuous;
    ///
    /// let mut array = [1, 0, 1];
    /// array.as_mut_slice()[1] = 2;
    /// assert_eq!(array, [1, 2, 1]);
    /// ```
    fn as_mut_slice(&mut self) -> &mut [Self::Item];

    /// Returns len of the array or slice.
    fn len(&self) -> usize;

    /// Returns true if the array or slice has a length of 0.
    #[inline]
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns an iterator over refs to the array or slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use arraylib::Continuous;
    ///
    /// let arr = [1, 2, 4];
    /// let mut iterator = arr.iter();
    ///
    /// assert_eq!(iterator.next(), Some(&1));
    /// assert_eq!(iterator.next(), Some(&2));
    /// assert_eq!(iterator.next(), Some(&4));
    /// assert_eq!(iterator.next(), None);
    /// ```
    #[inline]
    fn iter(&self) -> slice::Iter<'_, Self::Item> {
        self.as_ref().iter()
    }

    /// Returns an iterator that allows modifying each value.
    ///
    /// # Examples
    ///
    /// ```
    /// use arraylib::Continuous;
    ///
    /// let mut arr = [1, 2, 4];
    /// for elem in arr.iter_mut() {
    ///     *elem += 2;
    /// }
    /// assert_eq!(arr, [3, 4, 6]);
    /// ```
    #[inline]
    fn iter_mut(&mut self) -> slice::IterMut<'_, Self::Item> {
        self.as_mut().iter_mut()
    }

    crate::if_alloc! {
        /// Copies `self` into a new `Vec`.
        ///
        /// ## Examples
        ///
        /// ```
        /// use arraylib::Continuous;
        ///
        /// let arr = [1, 2, 3];
        /// assert_eq!(arr.to_vec(), vec![1, 2, 3])
        /// ```
        ///
        /// See also: [`[T]::to_vec`](https://doc.rust-lang.org/std/primitive.slice.html#method.to_vec)
        #[inline]
        #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
        fn to_vec(&self) -> alloc::vec::Vec<Self::Item>
        where
            Self::Item: Clone,
        {
            self.as_slice().to_vec()
        }
    }

    /// Returns an iterator over all continuous windows of type `&[Item; N]`.
    /// The windows overlap. If the slice is shorter than size
    /// `N`, the iterator returns `None`.
    ///
    /// ## Note
    ///
    /// This function is identical to the
    /// [`<[T]>::array_windows`][array_windows] (unstable as of writing this).
    /// The name is changed to fix collision warning.
    ///
    /// [array_windows]: https://doc.rust-lang.org/std/primitive.slice.html#method.array_windows
    ///
    /// ## Examples
    ///
    /// ```
    /// use arraylib::Continuous;
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
    /// use arraylib::Continuous;
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
    /// use arraylib::Continuous;
    ///
    /// let slice = ['f', 'o', 'o'];
    /// let mut iter = slice.array_windows_::<4>();
    /// assert!(iter.next().is_none());
    /// ```
    ///
    /// ## Panics
    ///
    /// Panics if `N` is 0.
    #[inline]
    fn array_windows_<const N: usize>(&self) -> ArrayWindows<Self::Item, N> {
        ArrayWindows::new(self.as_ref())
    }

    /// Copy `self` into an owned array.
    ///
    /// Returns `Err(SizeError { .. })` if lenght of `self` is not equal to `N`.
    ///
    /// ## Examples
    ///
    /// ```
    /// use arraylib::Continuous;
    ///
    /// let slice: &[i32] = &[0, 1, 2, 3, 4];
    /// let array: [i32; 5] = slice.copied().unwrap();
    /// assert_eq!(array, [0, 1, 2, 3, 4]);
    /// ```
    ///
    /// ```
    /// use arraylib::{Continuous, SizeError};
    ///
    /// let slice: &[i32] = &[0, 1, 2, 3, 4];
    /// let result = slice.copied::<2>();
    ///
    /// let SizeError {
    ///     expected, found, ..
    /// } = result.unwrap_err();
    /// assert_eq!(expected, 2);
    /// assert_eq!(found, 5);
    /// ```
    #[inline]
    fn copied<const N: usize>(&self) -> Result<[Self::Item; N], SizeError>
    where
        Self::Item: Copy,
    {
        Array::from_slice(self.as_ref())
    }

    /// Clone `self` into an owned array.
    ///
    /// Return `Err(SizeError { .. })` if lenght of `self` is not equal to `N`.
    ///
    /// ## Examples
    ///
    /// ```
    /// use arraylib::Continuous;
    /// use core::ops::Range;
    ///
    /// // Range is not `Copy`
    /// let slice: &[Range<usize>] = &[0..1, 1..3, 2..10];
    /// let array: [Range<usize>; 3] = slice.cloned().unwrap();
    /// assert_eq!(array, [0..1, 1..3, 2..10]);
    /// ```
    ///
    /// ```
    /// use arraylib::{Continuous, SizeError};
    /// use core::ops::Range;
    ///
    /// let slice: &[Range<usize>] = &[0..1, 1..3, 2..10];
    /// let result = slice.cloned::<5>();
    ///
    /// let SizeError {
    ///     expected, found, ..
    /// } = result.unwrap_err();
    /// assert_eq!(expected, 5);
    /// assert_eq!(found, 3);
    /// ```
    #[inline]
    fn cloned<const N: usize>(&self) -> Result<[Self::Item; N], SizeError>
    where
        Self::Item: Clone,
    {
        Array::clone_from_slice(self.as_ref())
    }

    /// ## Safety
    unsafe fn assume_init_ref(this: &Self::Uninit) -> &Self;

    /// ## Safety
    unsafe fn assume_init_mut(this: &mut Self::Uninit) -> &mut Self;
}

unsafe impl<T> Continuous for [T] {
    type Item = T;
    type Uninit = [MaybeUninit<T>];

    #[inline]
    fn as_slice(&self) -> &[Self::Item] {
        self
    }

    #[inline]
    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        self
    }

    #[inline]
    fn len(&self) -> usize {
        self.len()
    }

    #[inline]
    unsafe fn assume_init_ref(this: &Self::Uninit) -> &Self {
        &*(this as *const _ as *const _)
    }

    #[inline]
    unsafe fn assume_init_mut(this: &mut Self::Uninit) -> &mut Self {
        &mut *(this as *mut _ as *mut _)
    }
}

unsafe impl<T, const N: usize> Continuous for [T; N] {
    type Item = T;
    type Uninit = [MaybeUninit<T>; N];

    #[inline]
    fn as_slice(&self) -> &[Self::Item] {
        self
    }

    #[inline]
    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        self
    }

    #[inline]
    fn len(&self) -> usize {
        N
    }

    #[inline]
    fn is_empty(&self) -> bool {
        N == 0
    }

    #[inline]
    unsafe fn assume_init_ref(this: &Self::Uninit) -> &Self {
        &*(this as *const _ as *const _)
    }

    #[inline]
    unsafe fn assume_init_mut(this: &mut Self::Uninit) -> &mut Self {
        &mut *(this as *mut _ as *mut _)
    }
}
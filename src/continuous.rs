use core::{mem::MaybeUninit, slice};

/// Shorthand methods those just refer to `self.as_slice().smt()`
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

    /// ## Safety
    #[inline]
    unsafe fn assume_init_ref(this: &Self::Uninit) -> &Self
    where
        Self: Sized,
    {
        &*(this as *const _ as *const _)
    }

    /// ## Safety
    #[inline]
    unsafe fn assume_init_mut(this: &mut Self::Uninit) -> &mut Self
    where
        Self: Sized,
    {
        &mut *(this as *mut _ as *mut _)
    }
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
}

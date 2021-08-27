use crate::{util::transmute::extremely_unsafe_transmute, Array, SizeError};

/// Extension on arrays that provide additional functions.
pub trait ArrayExt<const N: usize>: Array<N> {
    /// ## Example
    /// ```
    /// use arraylib::ArrayExt;
    ///
    /// let arr: [_; 6] = [1, 2, 3].concat_arr([4, 5, 6]);
    /// assert_eq!(arr, [1, 2, 3, 4, 5, 6])
    /// ```
    ///
    /// ## Panics
    ///
    /// Panics if `Self::SIZE` + `A::SIZE` != `R::SIZE`:
    ///
    /// ```should_panic
    /// use arraylib::ArrayExt;
    ///
    /// let arr: [_; 4] = [1, 2, 3].concat_arr([4, 5, 6]);
    /// ```
    #[inline]
    fn concat_arr<const M: usize, const R: usize>(self, other: [Self::Item; M]) -> [Self::Item; R] {
        unsafe {
            // Because of lack of const generics we need to assert this at runtime :(
            assert_eq!(N + M, R);

            #[repr(C, packed)]
            struct Both<Slf, A>(Slf, A);

            // ## Safety
            //
            // We know that all `Self`, `A` and `R` are arrays.
            // Also we know that `Self::SIZE + A::SIZE == R::SIZE`, that means that we can
            // concat `Self` with `A` and we'll obtain `R`.
            //
            // Because of fact that all types are arrays (and fact that `Both` is
            // `#[repr(C, packed)]`), we know that `Both<Self, A>` is equal to `R`, so we
            // can safely transmute one into another.
            let both = Both(self, other);
            extremely_unsafe_transmute::<Both<Self, [Self::Item; M]>, [Self::Item; R]>(both)
        }
    }

    /// Splits self into 2 arrays
    ///
    /// ## Example
    /// ```
    /// use arraylib::ArrayExt;
    ///
    /// let arr = [1, 2, 3, 4, 5];
    /// let (head, tail) = arr.split_arr::<2, 3>();
    ///
    /// assert_eq!(head, [1, 2]);
    /// assert_eq!(tail, [3, 4, 5]);
    /// ```
    #[inline]
    fn split_arr<const L: usize, const R: usize>(self) -> ([Self::Item; L], [Self::Item; R]) {
        unsafe {
            // Because of lack of const generics we need to assert this in runtime :(
            assert_eq!(N, L + R);

            #[repr(C, packed)]
            struct Both<A, B>(A, B);

            // ## Safety
            //
            // We know that all `Self`, `A` and `B` are arrays.
            // Also we know that `Self::SIZE, A::SIZE + B::SIZE`, that means that we can
            // split `Self` into `A` and `B`.
            //
            // Because of fact that all types are arrays (and fact that `Both` is
            // `#[repr(C, packed)]`), we know that `Both<Self, A>` is equal to `R`, so we
            // can safely transmute one into another.
            let Both(a, b): Both<[Self::Item; L], [Self::Item; R]> =
                extremely_unsafe_transmute::<Self, Both<[Self::Item; L], [Self::Item; R]>>(self);

            (a, b)
        }
    }

    crate::if_alloc! {
        /// Copies `self` into a new `Vec`.
        ///
        /// ## Examples
        ///
        /// ```
        /// use arraylib::Array;
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

        /// Converts `self` into a vector without clones.
        ///
        /// The resulting vector can be converted back into a box via
        /// `Vec<T>`'s `into_boxed_slice` method.
        ///
        /// ## Examples
        ///
        /// ```
        /// use arraylib::ArrayExt;
        ///
        /// let s = [10, 40, 30];
        /// let x = s.into_vec();
        /// // `s` cannot be used anymore because it has been converted into `x`.
        ///
        /// assert_eq!(x, vec![10, 40, 30]);
        /// ```
        ///
        /// See also: [`[T]::in to_vec`](https://doc.rust-lang.org/std/primitive.slice.html#method.into_vec)
        #[inline]
        #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
        fn into_vec(self) -> alloc::vec::Vec<Self::Item> {
            self.into_boxed_slice().into_vec()
        }
    }

    /// Create array from slice. Return `Err(())` if `slice.len != Self::SIZE`.
    ///
    /// ## Examples
    /// ```
    /// use arraylib::ArrayExt;
    ///
    /// let slice = &[1, 2, 3];
    /// let arr = <[i32; 3]>::from_slice(slice);
    /// assert_eq!(arr, Ok([1, 2, 3]));
    /// ```
    ///
    /// ```
    /// # use arraylib::{ArrayExt, SizeError};
    /// let slice = &[1, 2, 3, 4];
    /// let arr = <[i32; 2]>::from_slice(slice);
    /// //          ^^^^^^ ---- wrong size, slice len = 4, arr len = 2
    /// assert_eq!(arr, Err(SizeError::default()));
    /// ```
    #[inline]
    fn from_slice(slice: &[Self::Item]) -> Result<Self, SizeError>
    where
        Self::Item: Copy,
    {
        if slice.len() == N {
            Ok(Self::from_iter(slice.iter().copied()).unwrap())
        } else {
            Err(SizeError::default())
        }
    }

    /// Create array from slice. Return `Err(())` if `slice.len != Self::SIZE`.
    ///
    /// Same as [`from_slice`](crate::ArrayExt::from_slice), but doesn't require
    /// items to be `Copy`, instead only require elements to be `Clone`
    ///
    /// ## Examples
    ///
    /// ```
    /// use arraylib::ArrayExt;
    ///
    /// let slice = &[String::from("hi"), 123.to_string(), String::new()];
    /// let arr = <[String; 3]>::clone_from_slice(slice);
    /// assert_eq!(
    ///     arr,
    ///     Ok([String::from("hi"), 123.to_string(), String::new()])
    /// );
    /// ```
    #[inline]
    fn clone_from_slice(slice: &[Self::Item]) -> Result<Self, SizeError>
    where
        Self::Item: Clone,
    {
        if slice.len() == N {
            Ok(Self::from_iter(slice.iter().cloned()).unwrap())
        } else {
            Err(SizeError::default())
        }
    }

    /// Safely cast `&[T]` to `&Self` (`[T; N]`)
    ///
    /// ## Panics
    ///
    /// Panics if size of `slice` is less than size of `Self`.
    ///
    /// ## Examples
    ///
    /// ```
    /// use arraylib::ArrayExt;
    ///
    /// let vec = vec![1, 0, 2, 14];
    /// assert_eq!(<[i32; 4]>::ref_cast(&vec[..]), &[1, 0, 2, 14]);
    /// ```
    ///
    /// ```should_panic
    /// # use arraylib::ArrayExt;
    /// // panics
    /// <[i32; 4]>::ref_cast(&[1, 2][..]);
    /// ```
    #[inline]
    fn ref_cast(slice: &[Self::Item]) -> &Self {
        match Self::try_ref_cast(slice) {
            Ok(x) => x,
            Err(_) => size_expectation_failed(),
        }
    }

    /// Safely cast `&mut [T]` to `&mut Self` (`[T; N]`)
    ///
    /// ## Panics
    ///
    /// Panics if size of `slice` is less than size of `Self`.
    ///
    /// ## Examples
    ///
    /// ```
    /// use arraylib::{ArrayExt, SizeError};
    ///
    /// let mut vec = vec![1, 0, 2, 14];
    /// assert_eq!(<[i32; 4]>::mut_cast(&mut vec[..]), &mut [1, 0, 2, 14]);
    /// ```
    ///
    /// ```should_panic
    /// # use arraylib::ArrayExt;
    /// // panics
    /// <[i32; 4]>::mut_cast(&mut [1, 2][..]);
    /// ```
    #[inline]
    fn mut_cast(slice: &mut [Self::Item]) -> &mut Self {
        match Self::try_mut_cast(slice) {
            Ok(x) => x,
            Err(_) => size_expectation_failed(),
        }
    }

    /// Safely cast `&[T]` to `&Self` (`[T; N]`)
    ///
    /// ## Errors
    ///
    /// If size of `slice` is less than size of `Self`, then an error is
    /// returned.
    ///
    /// ## Examples
    ///
    /// ```
    /// use arraylib::{ArrayExt, SizeError};
    ///
    /// let vec = vec![1, 0, 2, 14];
    /// assert_eq!(<[i32; 4]>::try_ref_cast(&vec[..]), Ok(&[1, 0, 2, 14]));
    /// assert_eq!(<[i32; 4]>::try_ref_cast(&vec[1..=2]), Err(&[0, 2][..]));
    /// ```
    #[inline]
    fn try_ref_cast(slice: &[Self::Item]) -> Result<&Self, &[Self::Item]> {
        unsafe {
            if slice.len() >= N {
                Ok(Self::ref_cast_unchecked(slice))
            } else {
                Err(slice)
            }
        }
    }

    /// Safely cast `&mut [T]` to `&mut Self` (`[T; N]`)
    ///
    /// ## Errors
    ///
    /// If size of `slice` is less than size of `Self`, then an error is
    /// returned.
    ///
    /// ## Examples
    ///
    /// ```
    /// use arraylib::{ArrayExt, SizeError};
    ///
    /// let mut vec = vec![1, 0, 2, 14];
    /// assert_eq!(
    ///     <[i32; 4]>::try_mut_cast(&mut vec[..]),
    ///     Ok(&mut [1, 0, 2, 14])
    /// );
    /// assert_eq!(
    ///     <[i32; 4]>::try_mut_cast(&mut vec[1..=2]),
    ///     Err(&mut [0, 2][..])
    /// );
    /// ```
    #[inline]
    fn try_mut_cast(slice: &mut [Self::Item]) -> Result<&mut Self, &mut [Self::Item]> {
        unsafe {
            if slice.len() >= N {
                Ok(Self::mut_cast_unchecked(slice))
            } else {
                Err(slice)
            }
        }
    }

    /// Unsafety cast `&[T]` to `&Self` (`[T; N]`)
    ///
    /// ## Safety
    ///
    /// To safely call this function you need to ensure that size of slice is
    /// not less than the size of array: `slice.len() >= Self::SIZE`
    ///
    /// ## Examples
    ///
    /// ok usage:
    /// ```
    /// use arraylib::ArrayExt;
    ///
    /// let vec = vec![1, 0, 2, 14];
    ///
    /// let _: &[i32; 4] = unsafe {
    ///     // Safe because we know that size of `vec` is equal 4
    ///     <[i32; 4]>::ref_cast_unchecked(&vec[..])
    /// };
    /// ```
    /// **wrong** (UB) usage:
    /// ```no_run
    /// use arraylib::ArrayExt;
    ///
    /// let vec = vec![1, 0, 2, 14];
    ///
    /// let _: &[i32; 4] = unsafe {
    ///     // size of slice borrowed from `vec` is not equal to 4 so this is UB
    ///     <[i32; 4]>::ref_cast_unchecked(&vec[1..])
    /// };
    /// ```
    #[inline]
    unsafe fn ref_cast_unchecked(slice: &[Self::Item]) -> &Self {
        // ## (Un)Safety
        //
        // Slice and array of the same size must have the same ABI, so we can safely get
        // `&[T; N]` from `&[A::Item]` **if `slice.len()` >= N**. Here it is not
        // checked, so this method is unsafe.
        //
        // We can't transmute slice ref directly to array ref because
        // first is fat pointer and second is not.
        &*(slice.as_ptr() as *const Self)
    }

    /// Unsafety cast `&mut [T]` to `&mut Self` (`[T; N]`)
    ///
    /// ## Safety
    ///
    /// To safely call this function you need to ensure that size of slice is
    /// not less than the size of array: `slice.len() >= Self::SIZE`
    ///
    /// ## Examples
    ///
    /// ok usage:
    /// ```
    /// use arraylib::ArrayExt;
    ///
    /// let mut vec = vec![1, 0, 2, 14];
    ///
    /// let _: &[i32; 4] = unsafe {
    ///     // Safe because we know that size of `vec` is equal 4
    ///     <[i32; 4]>::ref_cast_unchecked(&mut vec[..])
    /// };
    /// ```
    /// **wrong** (UB) usage:
    /// ```no_run
    /// use arraylib::ArrayExt;
    ///
    /// let mut vec = vec![1, 0, 2, 14];
    ///
    /// let _: &[i32; 4] = unsafe {
    ///     // size of slice borrowed from `vec` is not equal to 4 so this is UB
    ///     <[i32; 4]>::ref_cast_unchecked(&mut vec[1..])
    /// };
    /// ```
    #[inline]
    unsafe fn mut_cast_unchecked(slice: &mut [Self::Item]) -> &mut Self {
        // ## (Un)Safety
        //
        // Slice and array of the same size must have the same ABI, so we can safely get
        // `&mut [T; N]` from `&mut [A::Item]` **if `slice.len()` >= N**. Here it is not
        // checked, so this method is unsafe.
        //
        // We can't transmute slice ref directly to array ref because
        // first is fat pointer and second is not.
        &mut *(slice.as_mut_ptr() as *mut Self)
    }
}

impl<A, const N: usize> ArrayExt<N> for A where A: Array<N> {}

// This is a separate function to reduce the code size of ref_cast/mut_cast
// functions.
#[cold]
#[inline(never)]
fn size_expectation_failed() -> ! {
    panic!("size of `slice` must not be less than size of `Self` to ref cast to success")
}

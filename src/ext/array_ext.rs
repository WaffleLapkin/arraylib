use crate::{
    iter::IterMove, util::transmute::extremely_unsafe_transmute, Array, ArrayWrapper, SizeError,
};

/// Extension on arrays that provide additional functions.
pub trait ArrayExt: Array {
    /// Creates iterator which moves elements out of array.
    ///
    /// See also: [IterMove](crate::iter::IterMove)
    #[inline]
    fn iter_move(self) -> IterMove<Self> {
        IterMove::new(self)
    }

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
    fn concat_arr<A, R>(self, other: A) -> R
    where
        A: Array<Item = Self::Item>,
        R: Array<Item = Self::Item>,
    {
        unsafe {
            // Because of lack of const generics we need to assert this in runtime :(
            //
            // It's also possible to add trait like `ArrayConcat<A> { type Output }` but
            // this leads to A LOT of impls and SLOW compile times.
            assert_eq!(Self::SIZE + A::SIZE, R::SIZE);

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
            extremely_unsafe_transmute::<Both<Self, A>, R>(both)
        }
    }

    /// Splits self into 2 arrays
    ///
    /// ## Example
    /// ```
    /// use arraylib::ArrayExt;
    ///
    /// let arr = [1, 2, 3, 4, 5];
    /// let (head, tail) = arr.split_arr::<[_; 2], [_; 3]>();
    ///
    /// assert_eq!(head, [1, 2]);
    /// assert_eq!(tail, [3, 4, 5]);
    /// ```
    #[inline]
    fn split_arr<A, B>(self) -> (A, B)
    where
        A: Array<Item = Self::Item>,
        B: Array<Item = Self::Item>,
    {
        unsafe {
            // Because of lack of const generics we need to assert this in runtime :(
            //
            // It's also possible to add trait like `ArraySplit<A, B> { ... }` but this
            // leads to A LOT of impls and SLOW compile times.
            assert_eq!(Self::SIZE, A::SIZE + B::SIZE);

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
            let Both(a, b): Both<A, B> = extremely_unsafe_transmute::<Self, Both<A, B>>(self);
            (a, b)
        }
    }

    /// Converts `self` into an array. This function will return `Some(_)` if
    /// sizes of `Self` and `A` are the same and `None` otherwise.
    ///
    /// ## Example
    /// ```
    /// use arraylib::{Array, ArrayExt};
    ///
    /// fn function_optimized_for_8(_: [i32; 8]) {
    ///     /* ... */
    /// }
    ///
    /// fn general<A>(array: A)
    /// where
    ///     A: Array<Item = i32>,
    /// {
    ///     match array.into_array::<[i32; 8]>() {
    ///         Ok(array) => function_optimized_for_8(array),
    ///         Err(array) => { /* here `array` is of type `A` */ },
    ///     }
    /// }
    /// ```
    #[inline]
    fn into_array<A>(self) -> Result<A, SizeError<Self>>
    where
        A: Array<Item = Self::Item>,
    {
        let slf = SizeError::expect(Self::SIZE, A::SIZE, self)?;
        // ## Safety
        //
        // Item types and sizes are same for both `Self` and `A`, so it's the same type.
        Ok(unsafe { extremely_unsafe_transmute::<Self, A>(slf) })
    }

    /// Copies `self` into a new `Vec`.
    ///
    /// ## Examples
    ///
    /// ```
    /// use arraylib::{Array, ArrayExt};
    ///
    /// fn generic<A>(arr: A)
    /// where
    ///     A: Array,
    ///     A::Item: Clone,
    /// {
    ///     let x = arr.to_vec();
    ///     // Here, `arr` and `x` can be modified independently.
    /// }
    /// ```
    ///
    /// See also: [`[T]::to_vec`](https://doc.rust-lang.org/std/primitive.slice.html#method.to_vec)
    #[cfg(feature = "alloc")]
    #[inline]
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
    #[cfg(feature = "alloc")]
    #[inline]
    fn into_vec(self) -> alloc::vec::Vec<Self::Item> {
        self.into_boxed_slice().into_vec()
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
    /// assert_eq!(arr, Err(SizeError::Greater(2, ())));
    /// ```
    #[inline]
    fn from_slice(slice: &[Self::Item]) -> Result<Self, SizeError>
    where
        Self::Item: Copy,
    {
        SizeError::expect_size(slice, Self::SIZE, ())?;

        Ok(Self::from_iter(slice.iter().copied()).unwrap())
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
        SizeError::expect_size(slice, Self::SIZE, ())?;

        Ok(Self::from_iter(slice.iter().cloned()).unwrap())
    }

    /// Wrap `self` into [`ArrayWrapper`](crate::ArrayWrapper)
    #[inline]
    fn wrap(self) -> ArrayWrapper<Self> {
        ArrayWrapper::new(self)
    }
}

impl<A> ArrayExt for A where A: Array {}

use core::{convert::Infallible, hint::unreachable_unchecked, mem::MaybeUninit};

use crate::{
    iter::IteratorExt,
    util::{init, transmute::extremely_unsafe_transmute},
    SizeError,
};

/// Represent array of _some_ size. E.g.: `[u8; 32]`, `[&str; 8]`, `[T; N]`.
///
/// ## Sizes
///
/// See [Sizes Limitations](./index.html#sizes-limitations) paragraph in crate
/// docs.
///
/// ## Safety
///
/// By implementing this trait for type `T` you guarantee that
/// 1. `T` has the same **ABI** as `[T::Item; T::Size]`
/// 2. `T::Maybe` is an array of the same type
///    (`[MeybeUninit<T::Item>; T::Size]`)
///
/// Violating these rules will cause **UB**.
///
/// It is **highly not recommended** to implement this trait on your type unless
/// you **really** know what you are doing.
pub unsafe trait Array<const N: usize>: Sized {
    /// Type of the Items in the array. i.e.
    /// ```
    /// # use arraylib::Array; fn dummy<T>() where
    /// [T; 4]: Array<4, Item = T>
    /// # {}
    /// ```
    type Item;

    /// Same array but item is wrapped with
    /// [`MaybeUninit<_>`](core::mem::MaybeUninit).
    /// ```
    /// # use arraylib::Array; fn dummy<T>() where
    /// [T; 4]: Array<4, Maybe = [core::mem::MaybeUninit<T>; 4]>
    /// # {}
    /// ```
    type Maybe: Array<N, Item = MaybeUninit<Self::Item>>;

    /// Extracts a slice containing the entire array.
    ///
    /// ## Example
    ///
    /// ```
    /// use arraylib::Array;
    ///
    /// let array = [1, 2, 3];
    /// assert_eq!(array.as_slice()[1..], [2, 3]);
    /// ```
    fn as_slice(&self) -> &[Self::Item];

    /// Extracts a mutable slice of the entire array.
    ///
    /// ## Example
    ///
    /// ```
    /// use arraylib::Array;
    ///
    /// let mut array = [1, 0, 1];
    /// array.as_mut_slice()[1] = 2;
    /// assert_eq!(array, [1, 2, 1]);
    /// ```
    fn as_mut_slice(&mut self) -> &mut [Self::Item];

    /// Maps elements of the array
    ///
    /// ## Examples
    /// ```
    /// use arraylib::Array;
    ///
    /// let arr = [1, 2, 3, 4, 5];
    /// let res = arr.lift(|x| 2i32.pow(x));
    /// assert_eq!(res, [2, 4, 8, 16, 32])
    /// ```
    ///
    /// **NOTE**: it's highly recommended to use iterators when you need to
    /// perform more that one operation (e.g. map + as_ref) because iterators
    /// are lazy and `ArrayMap` isn't.
    fn lift<U, F>(self, f: F) -> [U; N]
    where
        F: FnMut(Self::Item) -> U;

    /// Convert `&self` to `[&T; N]` (where `T = Self::Item, N = Self::Size`)
    ///
    /// ## Examples
    /// ```
    /// use arraylib::Array;
    ///
    /// let arr = [0, 1, 2, 3];
    /// let ref_arr = arr.as_refs();
    /// assert_eq!(ref_arr, [&0, &1, &2, &3]);
    /// assert_eq!(arr, [0, 1, 2, 3]);
    /// ```
    ///
    /// **NOTE**: it's highly recommended to use iterators when you need to
    /// perform more that one operation (e.g. map + as_ref) because iterators
    /// are lazy and `ArrayAsRef` isn't.
    ///
    /// See also: [`as_mut_refs`](crate::Array::as_mut_refs)
    fn as_refs(&self) -> [&Self::Item; N];

    /// Convert `&mut self` to `[&mut T; N]` (where `T = Self::Item, N =
    /// Self::Size`)
    ///
    /// ## Examples
    /// ```
    /// use arraylib::Array;
    ///
    /// let mut arr = [0, 1, 2, 3];
    /// let ref_arr = arr.as_mut_refs();
    /// assert_eq!(ref_arr, [&mut 0, &mut 1, &mut 2, &mut 3]);
    /// assert_eq!(arr, [0, 1, 2, 3]);
    /// ```
    ///
    /// **NOTE**: it's highly recommended to use iterators when you need to
    /// perform more that one operation (e.g. map + as_ref) because iterators
    /// are lazy and `ArrayAsRef` isn't.
    ///
    /// See also: [`as_refs`](crate::Array::as_refs)
    fn as_mut_refs(&mut self) -> [&mut Self::Item; N];

    ///
    fn iter_move(self) -> core::array::IntoIter<Self::Item, N>;

    /// Create new array, filled with elements returned by `f`. If `f` return
    /// `Err` then this method also return `Err`.
    ///
    /// ## Example
    /// ```
    /// use arraylib::Array;
    ///
    /// let f = |it: &mut u32| {
    ///     let res = Ok(*it);
    ///     *it = it.checked_sub(10).ok_or(())?;
    ///     res
    /// };
    ///
    /// let arr = <[_; 3]>::try_unfold(30, f);
    /// assert_eq!(arr, Ok([30, 20, 10]));
    ///
    /// let arr = <[_; 10]>::try_unfold(40, f);
    /// assert_eq!(arr, Err(()));
    /// ```
    fn try_unfold<St, F, E>(init: St, f: F) -> Result<Self, E>
    where
        // It's better to use `Try` here, instead of `Result` but it's unstable
        F: FnMut(&mut St) -> Result<Self::Item, E>;

    /// Create new array, filled with elements returned by `f`
    ///
    /// ## Example
    /// ```
    /// use arraylib::Array;
    ///
    /// let arr = <[_; 11]>::unfold(1, |it| {
    ///     let res = *it;
    ///     *it *= -2;
    ///     res
    /// });
    /// assert_eq!(arr, [1, -2, 4, -8, 16, -32, 64, -128, 256, -512, 1024]);
    /// ```
    fn unfold<St, F>(init: St, f: F) -> Self
    where
        F: FnMut(&mut St) -> Self::Item;

    /// Create new array, filled with elements returned by `f`. If `f` return
    /// `Err` then this method also return `Err`.
    ///
    /// ## Example
    /// ```
    /// use arraylib::Array;
    ///
    /// let f = |it| 250u8.checked_add(it as u8).ok_or(());
    ///
    /// let arr = <[_; 3]>::try_from_fn(f);
    /// assert_eq!(arr, Ok([250, 251, 252]));
    ///
    /// let arr = <[_; 10]>::try_from_fn(f);
    /// assert_eq!(arr, Err(()));
    /// ```
    fn try_from_fn<F, E>(f: F) -> Result<Self, E>
    where
        F: FnMut(usize) -> Result<Self::Item, E>;

    /// Create new array, filled with elements returned by `f`
    ///
    /// ## Example
    /// ```
    /// use arraylib::Array;
    ///
    /// let arr = <[_; 11]>::from_fn(|it| it.pow(2));
    /// assert_eq!(arr, [0, 1, 4, 9, 16, 25, 36, 49, 64, 81, 100]);
    /// ```
    fn from_fn<F>(f: F) -> Self
    where
        F: FnMut(usize) -> Self::Item;

    /// Creates an array from an iterator.
    ///
    /// This method returns `None` if there are not enough elements to fill the
    /// array.
    ///
    /// ## Examples
    ///
    /// ```
    /// use arraylib::Array;
    /// use std::iter::once;
    ///
    /// let iter = [-2, -1, 0, 1, 2].iter_move().filter(|it| it % 2 == 0);
    /// let arr = <[i32; 2]>::from_iter(iter);
    /// assert_eq!(arr, Some([-2, 0]));
    ///
    /// let arr = <[i32; 2]>::from_iter(once(0));
    /// assert_eq!(arr, None);
    /// ```
    fn from_iter<I>(iter: I) -> Option<Self>
    where
        I: IntoIterator<Item = Self::Item>;

    /// Converts self into `[MaybeUninit<Self::Item>; Self::Size]`. This
    /// function is used internally in this crate for some unsafe code.
    ///
    /// ## Example
    /// ```
    /// use arraylib::Array;
    /// use std::mem::MaybeUninit;
    ///
    /// let _: [MaybeUninit<bool>; 3] = [true, false, false].into_uninit();
    /// ```
    #[inline]
    fn into_uninit(self) -> Self::Maybe {
        // Note: copy-pasted from https://doc.rust-lang.org/nightly/src/core/array/iter.rs.html

        // ## Safety
        //
        // The transmute here is actually safe. The docs of `MaybeUninit` promise:
        //
        // > `MaybeUninit<T>` is guaranteed to have the same size and alignment
        // > as `T`.
        //
        // The docs even show a transmute from an array of `MaybeUninit<T>` to
        // an array of `T`.
        //
        // With that (and the guarantees of the array trait), this
        // initialization satisfies the invariants.
        unsafe { extremely_unsafe_transmute::<Self, Self::Maybe>(self) }
    }

    /// Creates uninitialized array of [`MaybeUninit<T>`].
    ///
    /// ## Example
    /// ```
    /// use arraylib::Array;
    /// use std::mem::MaybeUninit;
    ///
    /// let _: [MaybeUninit<i32>; 3] = <[i32; 3]>::uninit();
    /// ```
    ///
    /// [`MaybeUninit<T>`]: core::mem::MaybeUninit
    #[inline]
    // Initializing generic type with uninitialized state seems insane, but is
    // unsafe trait and `Array` guarantees that it's an array. And `Array::Maybe`
    // is an array of `MaybeUninit` that doesn't require initialization, so
    // everything is ok
    #[allow(clippy::uninit_assumed_init)]
    fn uninit() -> Self::Maybe {
        unsafe {
            // ## Safety
            //
            // Completely safe as `MaybeUninit` don't require initialization
            MaybeUninit::uninit().assume_init()
        }
    }

    // doc is mostly copy-pasted from core::mem::MaybeUninit::assume_init
    /// Extracts the values from the [`MaybeUninit<T>`] containers.
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
    /// [`MaybeUninit<T>`]: core::mem::MaybeUninit
    /// [`MaybeUninit::assume_init`]: core::mem::MaybeUninit::assume_init
    ///
    /// # Examples
    ///
    /// Correct usage of this method:
    ///
    /// ```
    /// use arraylib::Array;
    /// use std::mem::MaybeUninit;
    ///
    /// let mut arr: [MaybeUninit<bool>; 4] = <[bool; 4]>::uninit();
    /// for x in arr.iter_mut() {
    ///     unsafe { x.as_mut_ptr().write(true) };
    /// }
    ///
    /// let arr_init: [bool; 4] = unsafe { <_>::assume_init(arr) };
    /// assert_eq!(arr_init, [true; 4]);
    /// ```
    ///
    /// *Incorrect* usage of this method:
    ///
    /// ```no_run
    /// use arraylib::Array;
    /// use std::mem::MaybeUninit;
    ///
    /// let mut arr: [MaybeUninit<bool>; 4] = <[bool; 4]>::uninit();
    /// for i in 0..3 {
    ///     unsafe { arr[i].as_mut_ptr().write(true) };
    /// }
    ///
    /// let arr_init: [bool; 4] = unsafe { <_>::assume_init(arr) };
    /// // `arr[3]` had not been initialized yet, so this last line caused undefined behavior.
    /// ```
    #[inline]
    unsafe fn assume_init(uninit: Self::Maybe) -> Self {
        // # Unsafety
        //
        // Array trait guarantees that Self::Maybe is an array of the same size
        // as self, but with `MaybeUninit<_>` items.
        //
        // It's safe to transmute `MaybeUninit<T> -> T` **if** MaybeUninit is
        // in the initialized state. It's safe to transmute
        // `[MaybeUninit<T>; N] -> [T; N]` **if** all MaybeUninits are in the
        // initialized state.
        //
        // So this is safe if all items in `uninit` array are initialized.
        extremely_unsafe_transmute::<Self::Maybe, Self>(uninit)
    }

    /// Converts `self` into `Box<[Self::Item]>`
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    fn into_boxed_slice(self) -> alloc::boxed::Box<[Self::Item]>;

    /// ## Example
    /// ```
    /// use arraylib::Array;
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
    /// use arraylib::Array;
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
    /// use arraylib::Array;
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
        /// use arraylib::Array;
        ///
        /// let s = [10, 40, 30];
        /// let x = s.into_vec();
        /// // `s` cannot be used anymore because it has been converted into `x`.
        ///
        /// assert_eq!(x, vec![10, 40, 30]);
        /// ```
        ///
        /// See also: [`[T]::into_vec`](https://doc.rust-lang.org/std/primitive.slice.html#method.into_vec)
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
    /// use arraylib::Array;
    ///
    /// let slice = &[1, 2, 3];
    /// let arr = <[i32; 3]>::from_slice(slice);
    /// assert_eq!(arr, Ok([1, 2, 3]));
    /// ```
    ///
    /// ```
    /// # use arraylib::{Array, SizeError};
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
    /// Same as [`from_slice`](crate::Array::from_slice), but doesn't require
    /// items to be `Copy`, instead only require elements to be `Clone`
    ///
    /// ## Examples
    ///
    /// ```
    /// use arraylib::Array;
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
    /// use arraylib::Array;
    ///
    /// let vec = vec![1, 0, 2, 14];
    /// assert_eq!(<[i32; 4]>::ref_cast(&vec[..]), &[1, 0, 2, 14]);
    /// ```
    ///
    /// ```should_panic
    /// # use arraylib::Array;
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
    /// use arraylib::{Array, SizeError};
    ///
    /// let mut vec = vec![1, 0, 2, 14];
    /// assert_eq!(<[i32; 4]>::mut_cast(&mut vec[..]), &mut [1, 0, 2, 14]);
    /// ```
    ///
    /// ```should_panic
    /// # use arraylib::Array;
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
    /// use arraylib::{Array, SizeError};
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
    /// use arraylib::{Array, SizeError};
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
    /// use arraylib::Array;
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
    /// use arraylib::Array;
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
    /// use arraylib::Array;
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
    /// use arraylib::Array;
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

unsafe impl<T, const N: usize> Array<N> for [T; N] {
    type Item = T;
    type Maybe = [MaybeUninit<T>; N];

    crate::if_alloc! {
        #[inline]
        fn into_boxed_slice(self) -> alloc::boxed::Box<[Self::Item]> {
            alloc::boxed::Box::new(self) as _
        }
    }

    #[inline]
    fn as_slice(&self) -> &[T] {
        &self[..]
    }

    #[inline]
    fn as_mut_slice(&mut self) -> &mut [T] {
        &mut self[..]
    }

    #[inline]
    fn lift<U, F>(self, f: F) -> [U; N]
    where
        F: FnMut(Self::Item) -> U,
    {
        match self.iter_move().map(f).collect_array() {
            Some(ret) => ret,
            None => unsafe {
                debug_assert!(false);
                unreachable_unchecked()
            },
        }
    }

    #[inline]
    fn as_refs(&self) -> [&Self::Item; N] {
        self.iter().collect_array().unwrap()
    }

    #[inline]
    fn as_mut_refs(&mut self) -> [&mut Self::Item; N] {
        self.iter_mut().collect_array().unwrap()
    }

    #[inline]
    fn iter_move(self) -> core::array::IntoIter<Self::Item, N> {
        <_>::into_iter(self)
    }

    #[inline]
    fn try_unfold<St, F, E>(init: St, f: F) -> Result<Self, E>
    where
        F: FnMut(&mut St) -> Result<Self::Item, E>,
    {
        init::try_unfold_array(init, f)
    }

    #[inline]
    fn unfold<St, F>(init: St, mut f: F) -> Self
    where
        F: FnMut(&mut St) -> Self::Item,
    {
        match init::try_unfold_array(init, |st| Ok::<_, Infallible>(f(st))) {
            Ok(ret) => ret,
            Err(inf) => match inf {},
        }
    }

    #[inline]
    fn try_from_fn<F, E>(mut f: F) -> Result<Self, E>
    where
        F: FnMut(usize) -> Result<Self::Item, E>,
    {
        init::try_unfold_array(0, |i| {
            let item = f(*i)?;
            *i += 1;
            Ok(item)
        })
    }

    #[inline]
    fn from_fn<F>(mut f: F) -> Self
    where
        F: FnMut(usize) -> Self::Item,
    {
        let ret = init::try_unfold_array(0, |i| {
            let item = f(*i);
            *i += 1;
            Ok::<_, Infallible>(item)
        });

        match ret {
            Ok(ret) => ret,
            Err(inf) => match inf {},
        }
    }

    #[inline]
    fn from_iter<I>(iter: I) -> Option<Self>
    where
        I: IntoIterator<Item = Self::Item>,
    {
        let mut iter = iter.into_iter();
        init::try_unfold_array((), |&mut ()| iter.next().ok_or(())).ok()
    }
}

// This is a separate function to reduce the code size of ref_cast/mut_cast
// functions.
#[cold]
#[inline(never)]
fn size_expectation_failed() -> ! {
    panic!("size of `slice` must not be less than size of `Self` to ref cast to success")
}

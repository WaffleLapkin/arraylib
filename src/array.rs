use core::mem::MaybeUninit;

use crate::util::transmute::extremely_unsafe_transmute;

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
pub unsafe trait Array: Sized {
    /// Type of the Items in the array. i.e.
    /// ```
    /// # use arraylib::Array; fn dummy<T>() where
    /// [T; 4]: Array<Item = T>
    /// # {}
    /// ```
    type Item;

    /// Same array but item is wrapped with
    /// [`MaybeUninit<_>`](core::mem::MaybeUninit).
    /// ```
    /// # use arraylib::Array; fn dummy<T>() where
    /// [T; 4]: Array<Item = T, Maybe = [core::mem::MaybeUninit<T>; 4]>
    /// # {}
    /// ```
    type Maybe: Array<Item = MaybeUninit<Self::Item>>;

    /// Size of the array.
    ///
    /// ## Example
    ///
    /// ```
    /// use arraylib::Array;
    ///
    /// assert_eq!(<[(); 0]>::SIZE, 0);
    /// assert_eq!(<[(); 2]>::SIZE, 2);
    /// ```
    const SIZE: usize;

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
    /// use arraylib::{Array, ArrayExt};
    /// use std::iter::once;
    ///
    /// let iter = [-2, -1, 0, 1, 2].iter_move().filter(|it| it % 2 == 0);
    /// let arr = <[i32; 2]>::try_from_iter(iter);
    /// assert_eq!(arr, Some([-2, 0]));
    ///
    /// let arr = <[i32; 2]>::try_from_iter(once(0));
    /// assert_eq!(arr, None);
    /// ```
    fn try_from_iter<I>(iter: I) -> Option<Self>
    where
        I: IntoIterator<Item = Self::Item>;

    /// Creates an array from an iterator.
    ///
    /// ## Examples
    ///
    /// ```
    /// use arraylib::{Array, ArrayExt};
    ///
    /// let iter = [-2, -1, 0, 1, 2].iter_move().filter(|it| it % 2 == 0);
    /// let arr = <[i32; 2]>::from_iter(iter);
    ///
    /// assert_eq!(arr, [-2, 0]);
    /// ```
    ///
    /// ## Panics
    ///
    /// If there are not enough elements to fill the array:
    ///
    /// ```should_panic
    /// use arraylib::Array;
    /// use std::iter::once;
    ///
    /// let _ = <[i32; 2]>::from_iter(once(0));
    /// ```
    #[inline]
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Self::Item>,
    {
        Self::try_from_iter(iter)
            .expect("there weren't enough elements to fill an array of that size")
    }

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
    #[inline]
    #[cfg(feature = "alloc")]
    fn into_boxed_slice(self) -> alloc::boxed::Box<[Self::Item]> {
        // This `unimplemented!` is done to allow other crates to not implement this fn
        // and not worrying that the will stop working when end-user would
        // require to turn off or on alloc feature of this crate.
        //
        // ## Example of the problem:
        //
        // Imagine dep tree like this:
        // ```text
        //         [arraylib]
        //        /          \
        // [lib#1]           |
        //    |           [lib#3]
        // [lib#2]       /
        //        \     /
        //         [bin]
        // ```
        // There are 2 bad scenarios:
        // 1:
        // - lib#1 implements Array for own type without `into_boxed_slice`
        // - lib#3 uses `alloc` feature of arraylib
        // - bin can be compiled because lib#1 doesn't implement required method
        //
        // 2:
        // - lib#1 implements Array for own type with `into_boxed_slice`
        // - bin can be compiled without `alloc` because `lib#1` require `alloc` feature
        //   of arraylib
        //
        // There are 3 ways to solve this problems:
        // 1:
        // Add trait `AllocExt` with `into_boxed_slice`
        //   bad: you need to add bound in generic methods which require allocation
        //
        // 2 (currently implemented):
        // Add default implementation to `into_boxed_slice` with `unimplemented!`
        //   bad: this can potentially lead to runtime panics
        //
        // 3:
        // Make `Array` sealed, so no crate will be able to implement it
        //   bad: other crates won't be able to implement `Array` on their types
        unimplemented!()
    }
}

unsafe impl<T> Array for [T; 0] {
    type Item = T;
    type Maybe = [MaybeUninit<T>; 0];

    const SIZE: usize = 0;

    #[inline]
    fn as_slice(&self) -> &[T] {
        &[]
    }

    #[inline]
    fn as_mut_slice(&mut self) -> &mut [T] {
        &mut []
    }

    #[inline]
    fn try_unfold<St, F, E>(_init: St, _f: F) -> Result<Self, E>
    where
        F: FnMut(&mut St) -> Result<Self::Item, E>,
    {
        Ok([])
    }

    #[inline]
    fn unfold<St, F>(_init: St, _f: F) -> Self
    where
        F: FnMut(&mut St) -> Self::Item,
    {
        []
    }

    #[inline]
    fn try_from_fn<F, E>(_f: F) -> Result<Self, E>
    where
        F: FnMut(usize) -> Result<Self::Item, E>,
    {
        Ok([])
    }

    #[inline]
    fn from_fn<F>(_f: F) -> Self
    where
        F: FnMut(usize) -> Self::Item,
    {
        []
    }

    #[inline]
    fn try_from_iter<I>(_iter: I) -> Option<Self>
    where
        I: IntoIterator<Item = Self::Item>,
    {
        Some([])
    }

    #[inline]
    fn into_uninit(self) -> Self::Maybe {
        []
    }

    #[inline]
    #[cfg(feature = "alloc")]
    fn into_boxed_slice(self) -> alloc::boxed::Box<[Self::Item]> {
        alloc::boxed::Box::new(self) as _
    }
}

macro_rules! array_impl {
    ($e:tt) => {
        unsafe impl<T> Array for [T; $e] {
            type Item = T;
            type Maybe = [MaybeUninit<T>; $e];

            const SIZE: usize = $e;

            #[inline]
            fn as_slice(&self) -> &[T] { &self[..] }

            #[inline]
            fn as_mut_slice(&mut self) -> &mut [T] { &mut self[..] }

            #[inline]
            #[allow(unused_mut)]
            fn try_unfold<St, F, E>(mut init: St, mut f: F) -> Result<Self, E>
            where
                F: FnMut(&mut St) -> Result<Self::Item, E>
            {
                Ok(
                    // this expands to
                    // - `[f(&mut init)?, ..., f(&mut init)?]`, for arrays of sizes 1..=32
                    // - `crate::init::unfold_array`, otherwise
                    block_specialisation!(
                        $e,
                        { $crate::util::init::try_unfold_array(init, f)? },
                        { f(&mut init)? }
                    )
                )
            }

            #[inline]
            #[allow(unused_mut)]
            fn unfold<St, F>(mut init: St, mut f: F) -> Self
            where
                F: FnMut(&mut St) -> Self::Item
            {
                // this expands to
                // - `[f(&mut init), ..., f(&mut init)]`, for arrays of sizes 1..=32
                // - `crate::init::unfold_array`, otherwise
                block_specialisation!(
                    $e,
                    { $crate::util::init::unfold_array(init, f) },
                    { f(&mut init) }
                )
            }

            #[inline]
            #[allow(unused_mut)]
            fn try_from_fn<F, E>(mut f: F) -> Result<Self, E>
            where
                F: FnMut(usize) -> Result<Self::Item, E>
            {
                // this expands to
                // - `[f(0)?, f(1)?, f(2)?, ..., f($e - 1)?]`, for arrays of sizes 1..=32
                // - `crate::init::array_init_fn`, otherwise
                Ok(try_from_fn_specialisation!($e, f))
            }


            #[inline]
            #[allow(unused_mut)]
            fn from_fn<F>(mut f: F) -> Self
            where
                F: FnMut(usize) -> Self::Item
            {
                // this expands to
                // - `[f(0), f(1), f(2), ..., f($e - 1)]`, for arrays of sizes 1..=32
                // - `crate::init::array_init_fn`, otherwise
                from_fn_specialisation!($e, f)
            }

            #[inline]
            fn try_from_iter<I>(iter: I) -> Option<Self>
            where
                I: IntoIterator<Item = Self::Item>
            {
                #[allow(unused_mut)]
                let mut iter = iter.into_iter();

                Some(
                    // this expands to
                    // - `[iter.next()?, ..., iter.next()?]`, for arrays of sizes 1..=32
                    // - `crate::init::unfold_array`, otherwise
                    block_specialisation!(
                        $e,
                        { $crate::util::init::array_init_iter(iter)? },
                        { iter.next()? }
                    )
                )
            }

            #[inline]
            #[cfg(feature = "alloc")]
            fn into_boxed_slice(self) -> alloc::boxed::Box<[Self::Item]> {
                alloc::boxed::Box::new(self) as _
            }
        }
    };
}

array_impls!(array_impl);

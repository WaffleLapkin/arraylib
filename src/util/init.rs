//! Internal api for initializing big arrays.
//!
//! For public api see [`Array`]'s [`try_unfold`], [`unfold`], [`try_from_fn`],
//! [`from_fn`] and [`from_iter`].
//!
//! [`Array`]: crate::Array
//! [`try_unfold`]: crate::Array::try_unfold
//! [`unfold`]: crate::Array::unfold
//! [`try_from_fn`]: crate::Array::try_from_fn
//! [`from_fn`]: crate::Array::from_fn
//! [`from_iter`]: crate::Array::from_iter
use core::{
    convert::Infallible,
    mem::{self, MaybeUninit},
    ptr,
};

use crate::{Array, ArrayShorthand, MaybeUninitSlice};

#[inline]
pub(crate) fn array_init_fn<Arr, F>(mut init: F) -> Arr
where
    Arr: Array,
    Arr::Item: Sized,
    F: FnMut(usize) -> Arr::Item,
{
    try_array_init_fn(|i| Ok::<_, Infallible>(init(i))).unwrap_or_else(|inf| match inf {})
}

#[inline]
pub(crate) fn array_init_iter<Arr, I>(mut iter: I) -> Option<Arr>
where
    Arr: Array,
    Arr::Item: Sized,
    I: Iterator<Item = Arr::Item>,
{
    try_unfold_array((), |_| iter.next().ok_or(())).ok()
}

#[inline]
pub(crate) fn try_array_init_fn<Arr, Err, F>(mut f: F) -> Result<Arr, Err>
where
    Arr: Array,
    Arr::Item: Sized,
    F: FnMut(usize) -> Result<Arr::Item, Err>,
{
    try_unfold_array(0usize, |state| {
        let item = f(*state);
        *state += 1;
        item
    })
}

#[inline]
pub(crate) fn unfold_array<Arr, St, F>(init: St, mut f: F) -> Arr
where
    Arr: Array,
    F: FnMut(&mut St) -> Arr::Item,
{
    try_unfold_array(init, |state| Ok::<_, Infallible>(f(state))).unwrap_or_else(|inf| match inf {})
}

#[inline]
pub(crate) fn try_unfold_array<Arr, St, F, E>(init: St, mut f: F) -> Result<Arr, E>
where
    Arr: Array,
    // It's better to use `Try` here, instead of `Result` but it's unstable
    F: FnMut(&mut St) -> Result<Arr::Item, E>,
{
    let mut array = Arr::uninit();
    let mut state = init;

    if !mem::needs_drop::<Arr::Item>() {
        for hole in array.iter_mut() {
            // If `init` panics/fails nothing really happen: panic/fail just go up
            // (Item doesn't need drop, so there are no leaks and everything is ok')
            *hole = MaybeUninit::new(f(&mut state)?)
        }
    } else {
        // Item needs drop, so things came up a bit tricky

        /// Guard that runs drop's of initialized elements on panic or early
        /// return.
        ///
        /// This struct is private to this function, because of the unsafe code
        /// in it's `Drop` impl, which is sound only if:
        /// - all elements of `self.arr[..self.initialized]` are initialized...
        /// - elements behind `arr` slice aren't used after `DropGuard` is
        ///   dropped
        /// - ...so it must be sound to drop these elements using
        ///   `ptr::drop_in_place`
        struct DropGuard<'a, Item> {
            arr: &'a mut [MaybeUninit<Item>],
            initialized: usize,
        }

        impl<Item> Drop for DropGuard<'_, Item> {
            fn drop(&mut self) {
                // ## Safety
                //
                // The contract of the struct guarantees that this is sound
                unsafe {
                    let inited: &mut [Item] = self.arr[..self.initialized].assume_init_mut();

                    // drop initialized elements
                    ptr::drop_in_place(inited);
                }
            }
        }

        // If the `f(&mut state)?` call panics or fails, `guard` is dropped,
        // thus dropping `array[..initialized]` => no memory leak!
        //
        // ## Safety
        //
        // By construction, `array[..initialized]` only contains
        // init elements, thus there is no risk of dropping uninit data.
        let mut guard = DropGuard {
            arr: array.as_mut_slice(),
            initialized: 0,
        };

        // We need `guard` to hold unique reference to the `array`,
        // so we can't access `array` directly
        for (i, hole) in guard.arr.iter_mut().enumerate() {
            // Invariant: `i` elements have already been initialized
            guard.initialized = i;
            // If `f(&mut state)?` panics or fails, `guard` is dropped, thus
            // dropping the elements in `array[..i]`
            *hole = MaybeUninit::new(f(&mut state)?);
        }

        // Next lines return array from the function, so if `panic_guard` will be
        // dropped it could cause "use after free".
        mem::forget(guard);
    }

    // don't be fooled by this unsafe{} block, all the magic is in the previous
    // if/else.
    unsafe {
        // ## Safety
        //
        // We already initialized all elements of the array
        Ok(Arr::assume_init(array))
    }
}

#[cfg(test)]
mod tests {
    // I just don't want to think about ordering
    #![allow(clippy::mutex_atomic)]

    use core::convert::TryFrom;
    use std::sync::Mutex;

    use super::{array_init_fn, try_array_init_fn};
    use crate::util::init::array_init_iter;

    /// Add `1` to mutex on drop
    #[derive(Debug)]
    struct DropCount<'a>(&'a Mutex<usize>);

    impl<'a> Drop for DropCount<'a> {
        fn drop(&mut self) {
            let mut guard = self.0.lock().unwrap();
            *guard += 1;
        }
    }

    #[test]
    fn copy() {
        let arr: [i32; 32] = super::try_array_init_fn(i32::try_from).unwrap();

        assert_eq!(
            arr,
            [
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
                23, 24, 25, 26, 27, 28, 29, 30, 31,
            ]
        );
    }

    #[test]
    fn drop() {
        struct HasDrop;

        impl Drop for HasDrop {
            fn drop(&mut self) {}
        }

        let _: [HasDrop; 16] = array_init_fn(|_| HasDrop);
    }

    #[test]
    fn drop_on_panic() {
        let counter = Mutex::new(0);

        let r = std::panic::catch_unwind(|| {
            let _: [DropCount; 16] = array_init_fn(|i| {
                if i == 10 {
                    panic!()
                } else {
                    DropCount(&counter)
                }
            });
        });

        assert!(r.is_err());
        assert_eq!(*counter.lock().unwrap(), 10);
    }

    #[test]
    fn drop_on_fail() {
        let counter = Mutex::new(0);

        let r: Result<[DropCount; 16], ()> = try_array_init_fn(|i| {
            if i == 10 {
                Err(())
            } else {
                Ok(DropCount(&counter))
            }
        });

        assert!(r.is_err());
        assert_eq!(*counter.lock().unwrap(), 10);
    }

    #[test]
    fn zst() {
        let _: [(); 65536] = array_init_fn(|_| ());
    }

    #[test]
    fn the_biggest() {
        let _: [usize; 16384] = array_init_fn(|i| i);
    }

    #[test]
    fn iter_equal_len() {
        let mut vec = vec![0, 1, 2, 3, 4];
        let arr: [i32; 5] = array_init_iter(vec.drain(..)).unwrap();

        assert_eq!(arr, [0, 1, 2, 3, 4]);
    }

    #[test]
    fn iter_greater_len() {
        let mut vec = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];
        let arr: [i32; 5] = array_init_iter(vec.drain(..)).unwrap();

        assert_eq!(arr, [0, 1, 2, 3, 4]);
    }

    #[test]
    fn iter_less_len() {
        let mut vec = vec![0, 1, 2];
        let arr: Option<[i32; 5]> = array_init_iter(vec.drain(..));

        assert_eq!(arr, None);
    }
}

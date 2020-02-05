//! Internal api for initializing big arrays.
//!
//! For public api see [`Array`]'s [`try_from_fn`], [`from_fn`] and [`from_iter`].
//!
//! [`Array`]: crate::Array
//! [`try_from_fn`]: crate::Array::try_from_fn
//! [`from_fn`]: crate::Array::from_fn
//! [`from_iter`]: crate::Array::from_iter
use core::{
    convert::Infallible,
    mem::{self, MaybeUninit},
    ptr, slice,
};

use crate::{Array, ArrayShorthand, MaybeUninitSlice};

#[inline]
pub(crate) fn array_init_fn<Arr, F>(mut init: F) -> Arr
where
    Arr: Array,
    Arr::Item: Sized,
    F: FnMut(usize) -> Arr::Item,
{
    match try_array_init_fn(|i| Ok::<_, Infallible>(init(i))) {
        Ok(arr) => arr,
        Err(inf) => match inf {},
    }
}

#[inline]
pub(crate) fn array_init_iter<Arr, I>(mut iter: I) -> Option<Arr>
where
    Arr: Array,
    Arr::Item: Sized,
    I: Iterator<Item = Arr::Item>,
{
    try_array_init_fn(|_| iter.next().ok_or(())).ok()
}

#[inline]
pub(crate) fn try_array_init_fn<Arr, Err, F>(mut init: F) -> Result<Arr, Err>
where
    Arr: Array,
    Arr::Item: Sized,
    F: FnMut(usize) -> Result<Arr::Item, Err>,
{
    if !mem::needs_drop::<Arr::Item>() {
        let mut array = Arr::uninit();

        unsafe {
            for i in 0..Arr::SIZE {
                // If `init` panics nothing really happen: panic just go up
                // (Item doesn't need drop, so there are no leaks and everything is ok')
                *array.index_mut(i) = MaybeUninit::new(init(i)?);
            }

            // # Safety
            //
            // We already initialized all elements of the array
            Ok(Arr::assume_init(array))
        }
    } else {
        // Item needs drop, so things came up a bit tricky

        /// Guard that runs drop's of initialized elements on panic or early
        /// return.
        ///
        /// This struct is private to this function, because of the unsafe code
        /// in it's `Drop` impl, which is sound only if:
        /// - `array_base_ptr` is a pointer to the first element of an
        ///   alive array
        /// - all elements of `array[.. initialized_count]` (where `array` is the
        ///   array `array_base_ptr` is pointing to) are initialized...
        /// - ...so it must be sound to drop these elements using `ptr::drop_in_place`
        struct DropGuard<Item> {
            // *mut because we need to mutate array, while holding it in guard
            // (it's used only in drop, so hopefully it's ok)
            array_base_ptr: *mut MaybeUninit<Item>,
            initialized_count: usize,
        }

        impl<Item> Drop for DropGuard<Item> {
            fn drop(&mut self) {
                // # Safety
                //
                // The contract of the struct guarantees that this is sound
                unsafe {
                    let slice =
                        slice::from_raw_parts_mut(self.array_base_ptr, self.initialized_count)
                            .assume_init_mut();

                    ptr::drop_in_place(slice);
                }
            }
        }

        // If the `init(i)?` call panics or fails, `panic_guard` is dropped,
        // dropping `array[.. initialized_count]` => no memory leak!
        //
        // # Safety
        //
        // By construction, array[.. initialized_count] only contains
        // init elements, thus there is no risk of dropping uninit data.
        unsafe {
            let mut array = Arr::uninit();
            let mut panic_guard = DropGuard {
                array_base_ptr: array.as_mut_slice().as_mut_ptr(),
                initialized_count: 0,
            };

            for i in 0..Arr::SIZE {
                // Invariant: `i` elements have already been initialized
                panic_guard.initialized_count = i;
                // If this panics or fails, `panic_guard` is dropped, thus
                // dropping the elements in `base_ptr[.. i]`
                let value = init(i)?;
                *array.index_mut(i) = MaybeUninit::new(value);
            }

            // Next line return array from function, so if `panic_guard` will be
            // dropped it could cause "use after free".
            mem::forget(panic_guard);

            // # Safety
            //
            // We already initialized all elements of the array
            Ok(Arr::assume_init(array))
        }
    }
}

#[cfg(test)]
mod tests {
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

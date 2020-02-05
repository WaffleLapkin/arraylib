use crate::{iter::IteratorExt, Array, ArrayExt};

/// Represent array which elements can be mapped (actually any array)
pub trait ArrayMap<U>: Array {
    /// Type of mapped array. So if `Self = [T; N]` then `Map = [U; N]`
    type Map: Array<Item = U>;

    /// Maps elements of the array
    ///
    /// ## Examples
    /// ```
    /// use arraylib::ArrayMap;
    ///
    /// let arr = [1, 2, 3, 4, 5];
    /// let res = arr.map(|x| 2i32.pow(x));
    /// assert_eq!(res, [2, 4, 8, 16, 32])
    /// ```
    ///
    /// **NOTE**: it's nighly recommended to use iterators when you need to
    /// perform more that one operation (e.g. map + as_ref) because iterators
    /// are lazy and `ArrayMap` isn't.
    #[inline]
    fn map<F>(self, f: F) -> Self::Map
    where
        F: FnMut(Self::Item) -> U,
    {
        // It's probably not the best implementation (if you are mad on
        // performance) due to checks that can be not eliminated, but
        // `collect_array` (`from_iter`) catch all the tricky stuff
        // about memory leaks, so this simple implementation was chosen.
        //
        // In future this implementation may be overwritten for small array
        // sizes using macros.
        self.iter_move().map(f).collect_array()
    }
}

impl<T, U> ArrayMap<U> for [T; 0] {
    type Map = [U; 0];

    #[inline]
    fn map<F>(self, _f: F) -> Self::Map
    where
        F: FnMut(Self::Item) -> U,
    {
        []
    }
}

macro_rules! array_map_impl {
    ($SIZE:expr) => {
        impl<T, U> ArrayMap<U> for [T; $SIZE] {
            type Map = [U; $SIZE];
        }
    };
}

array_impls!(array_map_impl);

use core::{mem, slice};

use crate::Array;

/// Shorthand methods those just refer to `self.as_slice().smt()`
pub trait ArrayShorthand<const N: usize>: Array<N> {
    /// Replace element of the array
    ///
    /// ## Example
    /// ```
    /// use arraylib::ArrayShorthand;
    ///
    /// let mut arr = ["hello", "", "world"];
    /// assert_eq!(arr.replace(1, ", "), "");
    /// assert_eq!(arr, ["hello", ", ", "world"])
    /// ```
    #[inline]
    fn replace(&mut self, idx: usize, item: Self::Item) -> Self::Item {
        mem::replace(&mut self.as_mut_slice()[idx], item)
    }

    /// Take element of the array, replacing it with default
    ///
    /// ## Example
    /// ```
    /// use arraylib::ArrayShorthand;
    ///
    /// let mut arr = [String::from("hello, "), String::from("world")];
    /// assert_eq!(arr.take(1), "world");
    /// assert_eq!(arr, ["hello, ", ""])
    /// ```
    #[inline]
    fn take(&mut self, idx: usize) -> Self::Item
    where
        Self::Item: Default,
    {
        self.replace(idx, <_>::default())
    }

    /// Returns an iterator over refs to the array.
    ///
    /// # Examples
    ///
    /// ```
    /// use arraylib::ArrayShorthand;
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
        self.as_slice().iter()
    }

    /// Returns an iterator that allows modifying each value.
    ///
    /// # Examples
    ///
    /// ```
    /// use arraylib::ArrayShorthand;
    ///
    /// let mut arr = [1, 2, 4];
    /// for elem in arr.iter_mut() {
    ///     *elem += 2;
    /// }
    /// assert_eq!(arr, [3, 4, 6]);
    /// ```
    #[inline]
    fn iter_mut(&mut self) -> slice::IterMut<'_, Self::Item> {
        self.as_mut_slice().iter_mut()
    }
}

impl<A, const N: usize> ArrayShorthand<N> for A where A: Array<N> {}

use core::{mem, slice, slice::SliceIndex};

use crate::Array;

/// Shorthand methods those just refer to `self.as_slice().smt()`
pub trait ArrayShorthand: Array {
    /// Returns a reference to the value corresponding to the supplied index.
    ///
    /// ## Example
    /// ```
    /// use arraylib::{ArrayShorthand, Array};
    ///
    /// fn slice<A>(arr: &A) -> (&A::Item, &[A::Item])
    /// where
    ///     A: Array
    /// {
    ///     (arr.index(0), arr.index(1..))
    /// }
    ///
    /// assert_eq!(slice(&[1, 2, 3]), (&1, &[2, 3][..]))
    /// ```
    ///
    /// See also: [`index_mut`](ArrayShorthand::index_mut)
    #[inline]
    fn index<Idx>(&self, idx: Idx) -> &Idx::Output
    where
        Idx: SliceIndex<[Self::Item]>,
    {
        &self.as_slice()[idx]
    }

    /// Returns a unique reference to the value corresponding to the supplied index.
    ///
    /// ## Example
    /// ```
    /// use arraylib::{ArrayShorthand, Array};
    ///
    /// fn slice<A>(arr: &mut A) -> &mut [A::Item]
    /// where
    ///     A: Array
    /// {
    ///     arr.index_mut(1..)
    /// }
    ///
    /// assert_eq!(slice(&mut [1, 2, 3]), &mut [2, 3])
    /// ```
    ///
    /// See also: [`index`](ArrayShorthand::index)
    #[inline]
    fn index_mut<Idx>(&mut self, idx: Idx) -> &mut Idx::Output
    where
        Idx: SliceIndex<[Self::Item]>,
    {
        &mut self.as_mut_slice()[idx]
    }

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
        mem::replace(self.index_mut(idx), item)
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

impl<A> ArrayShorthand for A where A: Array {}

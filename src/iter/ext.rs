use crate::{iter::ArrayChunks, Array};

/// Extension for [`Iterator`] trait that provides some array-related methods.
pub trait IteratorExt: Iterator {
    /// Returns an iterator over chunks `A`.
    ///
    /// The chunks are arrays and do not overlap. If `A::SIZE` does not divide
    /// the length of the iter, last elements will be dropped.
    ///
    /// ## Examples
    ///
    /// ```
    /// use arraylib::iter::IteratorExt;
    ///
    /// let vec = vec![0, 1, 2, 3, 4];
    /// let mut chunks = vec.into_iter().array_chunks::<[_; 2]>();
    ///
    /// assert_eq!(chunks.next(), Some([0, 1]));
    /// assert_eq!(chunks.next(), Some([2, 3]));
    /// assert_eq!(chunks.next(), None);
    /// ```
    ///
    /// ```
    /// use arraylib::iter::IteratorExt;
    ///
    /// let vec = vec![0, 1, 2, 3, 4];
    /// let mut chunks = vec.into_iter().array_chunks::<[_; 2]>();
    ///
    /// assert_eq!(chunks.next_back(), Some([4, 3]));
    /// assert_eq!(chunks.next_back(), Some([2, 1]));
    /// assert_eq!(chunks.next_back(), None);
    /// ```
    ///
    /// ## Panics
    ///
    /// If `A::SIZE == 0`
    ///
    /// ```should_panic
    /// use arraylib::iter::IteratorExt;
    ///
    /// let vec = vec![0, 1, 2, 3, 4];
    /// let _chunks = vec.into_iter().array_chunks::<[_; 0]>();
    /// ```
    ///
    /// See also [`slice::chunks`][chunks]
    ///
    /// [chunks]: ../../core/primitive.slice.html#method.chunks
    #[inline]
    fn array_chunks<A>(self) -> ArrayChunks<Self, A>
    where
        Self: Sized,
        A: Array<Item = Self::Item>,
    {
        assert!(A::SIZE > 0, "Size of chunks must be greater that zero");
        ArrayChunks::new(self)
    }

    /// Transforms an iterator into an array.
    ///
    /// `collect_array()` can take anything iterable, and turn it into an array
    /// of relevant size.
    ///
    /// See also: [`Iterator::collect`](core::iter::Iterator::collect)
    ///
    /// ## Example
    ///
    /// Basic usage:
    ///
    /// ```
    /// use arraylib::iter::IteratorExt;
    ///
    /// let a = [1, 2, 3];
    /// let doubled: [_; 3] = a.iter().map(|&x| x * 2).collect_array();
    ///
    /// assert_eq!([2, 4, 6], doubled);
    /// ```
    ///
    /// ## Panics
    ///
    /// If there are not enough elements to fill the array:
    ///
    /// ```should_panic
    /// use arraylib::iter::IteratorExt;
    ///
    /// [1, 2, 3].iter().collect_array::<[_; 16]>();
    /// ```
    #[inline]
    fn collect_array<A>(self) -> A
    where
        Self: Sized,
        A: Array<Item = Self::Item>,
    {
        A::from_iter(self)
    }

    /// Transforms an iterator into an array.
    ///
    /// `collect_array()` can take anything iterable, and turn it into an array
    /// of relevant size.
    ///
    /// This method returns `None` if there are not enough elements to fill the
    /// array.
    ///
    /// See also: [`Iterator::collect`](core::iter::Iterator::collect)
    ///
    /// ## Example
    ///
    /// Basic usage:
    ///
    /// ```
    /// use arraylib::iter::IteratorExt;
    ///
    /// let a = [1, 2, 3];
    /// let doubled = a.iter().map(|&x| x * 2).try_collect_array();
    ///
    /// assert_eq!(doubled, Some([2, 4, 6]));
    ///
    /// assert_eq!([1, 2, 3].iter().try_collect_array::<[_; 16]>(), None)
    /// ```
    #[inline]
    fn try_collect_array<A>(self) -> Option<A>
    where
        Self: Sized,
        A: Array<Item = Self::Item>,
    {
        A::try_from_iter(self)
    }
}

impl<I: Iterator + ?Sized> IteratorExt for I {}

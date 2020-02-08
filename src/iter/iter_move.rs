use core::{fmt, iter::FusedIterator, mem::MaybeUninit, ops::Range};

use crate::{Array, ArrayShorthand, MaybeUninitSlice};

/// Iterator that moves values out of an array.
///
/// The implementation is very similar to [`std::vec::IntoIter`], however
/// `ArrayIterMove` stores elements on stack and uses indexes instead of
/// pointers.
///
/// ## Examples
/// ```
/// # use arraylib::iter::IterMove;
/// let arr = [1, 2, 3];
/// let mut iter = IterMove::new(arr);
/// assert_eq!(iter.next(), Some(1));
/// assert_eq!(iter.next(), Some(2));
/// assert_eq!(iter.next(), Some(3));
/// assert_eq!(iter.next(), None);
/// ```
/// It's also possible to constract iter using [`ArrayExt::iter_move`]:
/// ```
/// use arraylib::ArrayExt;
///
/// let mut expected = 1;
/// for i in [1, 2, 4, 8, 16, 32, 64, 128].iter_move() {
///     assert_eq!(i, expected);
///     expected *= 2;
/// }
/// ```
/// This iterator **moves** values out of an array, so it works with `!Copy`
/// types:
/// ```
/// use arraylib::iter::IterMove;
///
/// let array = [String::from("hello"), String::from("Tere")];
/// let mut iter = IterMove::new(array);
///
/// let string: String = iter.next().unwrap();
/// assert_eq!(string, "hello");
///
/// let string: String = iter.next().unwrap();
/// assert_eq!(string, "Tere");
/// ```
///
/// ## Implementation details
///
/// Internally `IterMove` represented by `Range<usize>` and
/// `[MaybeUninit<T>; N]` (`MaybeUninit` is needed to take out elements from an
/// array without copying and `UB`).
///
/// The range represents "alive" part of the array, so all elements of
/// `inner[alive]` are initialized.
///
/// Diagram of `IterMove<[u32; 8]>` after consuming 3 elements with [`next`] and
/// 2 with [`next_back`]:
/// ```text
///                    _____.*------ `alive`
///                   /     \
/// inner: [ ~, ~, ~, 1, 2, 3, ~, ~ ]
///          \_____/  \_____/  \__/
///          |              |     `---- elements consumed with `next_back`
///          |              |           (in uninitialized state)
///          |              `---- valid elements in initialized state
///          `---- elements consumed with `next` (in uninitialized state)
/// ```
///
/// [`std::vec::IntoIter`]: https://doc.rust-lang.org/std/vec/struct.IntoIter.html
/// [`ArrayExt::iter_move`]: crate::ArrayExt::iter_move
/// [`next`]: core::iter::Iterator::next
/// [`next_back`]: core::iter::DoubleEndedIterator::next_back
pub struct IterMove<A: Array> {
    // Alive part of the inner array.
    // `inner[alive]` must be initialized.
    alive: Range<usize>,
    inner: A::Maybe,
}

impl<A> IterMove<A>
where
    A: Array,
{
    /// Crate new moving iterator from an array
    #[inline]
    pub fn new(array: A) -> Self {
        Self {
            alive: 0..A::SIZE,
            inner: array.into_uninit(),
        }
    }

    /// Returns the remaining items of this iterator as a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use arraylib::ArrayExt;
    /// let arr = ['a', 'b', 'c'];
    ///
    /// let mut iter_move = arr.iter_move();
    /// assert_eq!(iter_move.as_slice(), &['a', 'b', 'c']);
    ///
    /// let _ = iter_move.next().unwrap();
    /// assert_eq!(iter_move.as_slice(), &['b', 'c']);
    /// ```
    #[inline]
    pub fn as_slice(&self) -> &[A::Item] {
        unsafe {
            let slice: &[MaybeUninit<A::Item>] = self.inner.index(self.alive.clone());
            // # Safety
            //
            // All elements of inner[alive] are guaranteed to be initialized
            slice.assume_init()
        }
    }

    /// Returns the remaining items of this iterator as a mutable slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use arraylib::ArrayExt;
    /// let arr = ['a', 'b', 'c'];
    ///
    /// let mut iter_move = arr.iter_move();
    /// let _ = iter_move.next().unwrap();
    ///
    /// assert_eq!(iter_move.as_mut_slice(), &mut ['b', 'c']);
    /// iter_move.as_mut_slice()[0] = 'x';
    ///
    /// assert_eq!(iter_move.next().unwrap(), 'x');
    /// assert_eq!(iter_move.next().unwrap(), 'c');
    /// ```
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [A::Item] {
        unsafe {
            let slice: &mut [MaybeUninit<A::Item>] = self.inner.index_mut(self.alive.clone());
            // # Safety
            //
            // All elements of inner[alive] are guaranteed to be initialized
            slice.assume_init_mut()
        }
    }
}

impl<A> Iterator for IterMove<A>
where
    A: Array,
{
    type Item = A::Item;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            // return if there are no more elements
            let idx = self.alive.next()?;

            let result: A::Item = self.inner.replace(idx, MaybeUninit::uninit()).assume_init();

            Some(result)
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.alive.len();
        (exact, Some(exact))
    }

    #[inline]
    fn count(self) -> usize {
        self.alive.len()
    }
}

impl<A> DoubleEndedIterator for IterMove<A>
where
    A: Array,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        unsafe {
            // return if there are no more elements
            let idx = self.alive.next_back()?;

            let result: A::Item = self.inner.replace(idx, MaybeUninit::uninit()).assume_init();

            Some(result)
        }
    }
}

impl<A> ExactSizeIterator for IterMove<A>
where
    A: Array,
{
    #[inline]
    fn len(&self) -> usize {
        self.alive.len()
    }
}

impl<A> FusedIterator for IterMove<A> where A: Array {}

#[cfg(feature = "nightly")]
unsafe impl<A> core::iter::TrustedLen for IterMove<A> where A: Array {}

impl<A> Clone for IterMove<A>
where
    A: Array,
    A::Item: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        let inner = {
            // Create an uninitialized array of `MaybeUninit`. The `assume_init` is
            // safe because the type we are claiming to have initialized here is a
            // bunch of `MaybeUninit`s, which do not require initialization.
            let mut array: A::Maybe = A::uninit();

            for i in self.alive.clone() {
                let cloned = unsafe { (&*self.inner.index(i).as_ptr()).clone() };
                //                     ^^ ---- this deref is safe because we know that elements
                //                             of `inner[alive]` are initialized
                *array.index_mut(i) = MaybeUninit::new(cloned);
            }

            array
        };

        Self {
            alive: self.alive.clone(),
            inner,
        }
    }
}

impl<A> fmt::Debug for IterMove<A>
where
    A: Array,
    A::Item: fmt::Debug,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("IterMove").field(&self.as_slice()).finish()
    }
}

impl<A> Drop for IterMove<A>
where
    A: Array,
{
    #[inline]
    fn drop(&mut self) {
        for _ in self { /* drop all remaining elements */ }
    }
}

#[cfg(test)]
mod tests {
    use core::{convert::identity, iter};

    use crate::{iter::IterMove, Array};

    #[test]
    fn empty() {
        let arr: [String; 0] = [];
        let mut iter = IterMove::new(arr);

        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test() {
        let arr = <[usize; 5]>::from_fn(identity);
        let iter = IterMove::new(arr);

        assert!(iter.eq(vec![0, 1, 2, 3, 4]));
    }

    #[test]
    fn len() {
        let arr = <[usize; 5]>::from_fn(identity);
        let mut iter = IterMove::new(arr);

        assert_eq!(iter.len(), 5);

        iter.next();
        assert_eq!(iter.len(), 4);

        for _ in iter.by_ref() {}
        assert_eq!(iter.len(), 0);
    }

    #[test]
    fn clone() {
        let arr = <[usize; 5]>::from_fn(identity);
        let mut iter = IterMove::new(arr);

        assert!(iter.clone().eq(vec![0, 1, 2, 3, 4]));

        iter.next();
        iter.next_back();
        assert!(iter.clone().eq(vec![1, 2, 3]));

        for _ in iter.by_ref() {}
        assert!(iter.clone().eq(iter::empty()));
    }

    #[test]
    fn as_slice() {
        let arr = <[usize; 5]>::from_fn(identity);
        let mut iter = IterMove::new(arr);

        assert_eq!(iter.as_slice(), &[0, 1, 2, 3, 4]);
        assert_eq!(iter.as_mut_slice(), &mut [0, 1, 2, 3, 4]);

        iter.next();
        assert_eq!(iter.as_slice(), &[1, 2, 3, 4]);
        assert_eq!(iter.as_mut_slice(), &mut [1, 2, 3, 4]);

        iter.next_back();
        assert_eq!(iter.as_slice(), &[1, 2, 3]);
        assert_eq!(iter.as_mut_slice(), &mut [1, 2, 3]);

        for _ in iter.by_ref() {}
        assert_eq!(iter.as_slice(), &[]);
        assert_eq!(iter.as_mut_slice(), &mut []);
    }

    #[test]
    fn back() {
        let arr = <[usize; 5]>::from_fn(identity);
        let iter = IterMove::new(arr).rev();

        assert!(iter.eq(vec![4, 3, 2, 1, 0]));
    }
}

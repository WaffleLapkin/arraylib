use core::fmt;

use crate::Array;

// TODO: check that panicking refcast/index optimizes in a good way

/// An iterator over refs to overlapping subarrays of type `A`.
///
/// This struct is created by the [`array_windows`] method on [slices].
/// See it's documentation for more.
///
/// [`array_windows`]: crate::Continuous::array_windows_
/// [slices]: https://doc.rust-lang.org/std/primitive.slice.html
pub struct ArrayWindows<'a, T, const N: usize> {
    slice: &'a [T],
}

impl<'a, T, const N: usize> ArrayWindows<'a, T, N> {
    pub(crate) fn new(slice: &'a [T]) -> Self {
        assert!(N > 0);
        Self { slice }
    }
}

impl<'a, T: 'a, const N: usize> Iterator for ArrayWindows<'a, T, N> {
    type Item = &'a [T; N];

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.slice.len() >= N {
            let r = Array::ref_cast(&self.slice[..N]);
            self.slice = &self.slice[1..];
            Some(r)
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }

    #[inline]
    fn last(self) -> Option<Self::Item> {
        if self.slice.len() > N {
            Some(Array::ref_cast(&self.slice[self.slice.len() - N..]))
        } else {
            None
        }
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        let (end, overflow) = N.overflowing_add(n);
        if end > self.slice.len() || overflow {
            self.slice = &[];
            None
        } else {
            let nth = Array::ref_cast(&self.slice[n..end]);
            self.slice = &self.slice[n + 1..];
            Some(nth)
        }
    }
}

impl<'a, T, const N: usize> DoubleEndedIterator for ArrayWindows<'a, T, N> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.slice.len() >= N {
            let r = Array::ref_cast(&self.slice[self.slice.len() - N..]);
            self.slice = &self.slice[..self.slice.len() - 1];
            Some(r)
        } else {
            None
        }
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        let (end, overflow) = self.slice.len().overflowing_sub(n);
        if end < N || overflow {
            self.slice = &[];
            None
        } else {
            let ret = Array::ref_cast(&self.slice[end - N..end]);
            self.slice = &self.slice[..end - 1];
            Some(ret)
        }
    }
}

impl<'a, T, const N: usize> ExactSizeIterator for ArrayWindows<'a, T, N> {
    #[inline]
    fn len(&self) -> usize {
        (self.slice.len() + 1).saturating_sub(N)
    }

    #[inline]
    #[cfg(feature = "nightly")]
    fn is_empty(&self) -> bool {
        self.slice.len() < N
    }
}

impl<'a, T, const N: usize> fmt::Debug for ArrayWindows<'a, T, N>
where
    T: fmt::Debug,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ArrayWindows")
            .field("slice", &self.slice)
            .field("window_len", &N)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use crate::Continuous;

    #[test]
    fn basic_usage() {
        let mut iter = [0, 1, 2, 3].array_windows_::<2>();

        assert_eq!(iter.next(), Some(&[0, 1]));
        assert_eq!(iter.next(), Some(&[1, 2]));
        assert_eq!(iter.next(), Some(&[2, 3]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn back() {
        let mut iter = [0, 1, 2, 3].array_windows_::<2>().rev();

        assert_eq!(iter.next(), Some(&[2, 3]));
        assert_eq!(iter.next(), Some(&[1, 2]));
        assert_eq!(iter.next(), Some(&[0, 1]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn destruct() {
        let res = [1, 2, 3]
            .array_windows_::<2>()
            .fold(0, |i, [a, b]| i + (a * b));

        assert_eq!(res, 8)
    }

    #[test]
    fn nth() {
        let mut iter = [0, 1, 2, 3, 4, 5].array_windows_::<2>();

        assert_eq!(iter.nth(3), Some(&[3, 4]));
        assert_eq!(iter.next(), Some(&[4, 5]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn nth_back() {
        let mut iter = [0, 1, 2, 3, 4, 5].array_windows_::<2>();

        assert_eq!(iter.nth_back(3), Some(&[1, 2]));
        assert_eq!(iter.next(), Some(&[0, 1]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn len() {
        let mut iter = [0, 1, 2, 3, 4, 5].array_windows_::<2>();
        assert_eq!(iter.len(), 5);
        iter.next();
        iter.next_back();
        assert_eq!(iter.len(), 3);
        iter.by_ref().for_each(drop);
        assert_eq!(iter.len(), 0);
    }
}

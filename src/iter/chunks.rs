use core::{fmt, marker::PhantomData};

use crate::Array;

/// Iterator over chunks of the fixed size.
/// Created by [`IteratorExt::array_chunks`][method] method,
///
/// [method]: crate::iter::IteratorExt::array_chunks
pub struct ArrayChunks<I, T, const N: usize> {
    iter: I,
    marker: PhantomData<[T; N]>,
}

impl<I, T, const N: usize> ArrayChunks<I, T, N> {
    pub(crate) fn new(iter: I) -> Self {
        assert!(N > 0, "Size of chunks must be greater that zero");

        Self {
            iter,
            marker: PhantomData,
        }
    }
}

impl<I, T, const N: usize> Iterator for ArrayChunks<I, T, N>
where
    I: Iterator<Item = T>,
{
    type Item = [T; N];

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        Array::from_iter(self.iter.by_ref())
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (down, upper) = self.iter.size_hint();
        (down / N, upper.map(|it| it / N))
    }
}

impl<I, T, const N: usize> ExactSizeIterator for ArrayChunks<I, T, N>
where
    I: ExactSizeIterator<Item = T>,
{
    #[inline]
    fn len(&self) -> usize {
        self.iter.len() / N
    }

    #[inline]
    #[cfg(feature = "nightly")]
    fn is_empty(&self) -> bool {
        self.iter.len() < N
    }
}

impl<I: fmt::Debug, T, const N: usize> fmt::Debug for ArrayChunks<I, T, N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ArrayChunks")
            .field("iter", &self.iter)
            .field("chunk_len", &N)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use crate::{iter::IteratorExt, Array};

    #[test]
    fn basic_usage() {
        let mut iter = [0, 1, 2, 3, 4].iter_move().array_chunks::<2>();

        assert_eq!(iter.next(), Some([0, 1]));
        assert_eq!(iter.next(), Some([2, 3]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn len() {
        macro_rules! assert_len {
            (size: $array_size:literal, chunk: $chunk_size:literal, expect: $expected:literal) => {
                let array = [0; $array_size].iter_move().array_chunks::<$chunk_size>();
                assert_eq!(array.len(), $expected);
            };
            (
                $(
                    size: $array_size:literal, chunk: $chunk_size:literal, expect: $expected:literal;
                )+
            ) => {
                $(
                    assert_len!(size: $array_size, chunk: $chunk_size, expect: $expected);
                )+
            };

        }

        assert_len! {
            size: 0, chunk: 1, expect: 0;
            size: 1, chunk: 1, expect: 1;
            size: 2, chunk: 1, expect: 2;
            size: 3, chunk: 1, expect: 3;
            size: 32, chunk: 1, expect: 32;

            size: 0, chunk: 2, expect: 0;
            size: 1, chunk: 2, expect: 0;
            size: 2, chunk: 2, expect: 1;
            size: 3, chunk: 2, expect: 1;
            size: 4, chunk: 2, expect: 2;
            size: 5, chunk: 2, expect: 2;
            size: 32, chunk: 2, expect: 16;

            size: 0, chunk: 3, expect: 0;
            size: 1, chunk: 3, expect: 0;
            size: 2, chunk: 3, expect: 0;
            size: 3, chunk: 3, expect: 1;
            size: 4, chunk: 3, expect: 1;
            size: 5, chunk: 3, expect: 1;
            size: 6, chunk: 3, expect: 2;
            size: 7, chunk: 3, expect: 2;
            size: 32, chunk: 3, expect: 10;
        }
    }
}

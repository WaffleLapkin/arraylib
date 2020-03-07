use core::{fmt, marker::PhantomData};

use crate::Array;

/// Iterator over chunks of the fixed size.
/// Created by [`IteratorExt::array_chunks`][method] method,
///
/// [method]: crate::iter::IteratorExt::array_chunks
pub struct ArrayChunks<I, A> {
    iter: I,
    marker: PhantomData<A>,
}

impl<I, A> ArrayChunks<I, A> {
    pub(crate) fn new(iter: I) -> Self {
        Self {
            iter,
            marker: PhantomData,
        }
    }
}

impl<I, A> Iterator for ArrayChunks<I, A>
where
    I: Iterator,
    A: Array<Item = I::Item>,
{
    type Item = A;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        A::from_iter(self.iter.by_ref())
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (down, upper) = self.iter.size_hint();
        (down / A::SIZE, upper.map(|it| it / A::SIZE))
    }
}

impl<I, A> DoubleEndedIterator for ArrayChunks<I, A>
where
    I: DoubleEndedIterator,
    A: Array<Item = I::Item>,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        A::from_iter(self.iter.by_ref().rev())
    }
}

impl<I, A> ExactSizeIterator for ArrayChunks<I, A>
where
    I: ExactSizeIterator,
    A: Array<Item = I::Item>,
{
    #[inline]
    fn len(&self) -> usize {
        self.iter.len() / A::SIZE
    }

    #[inline]
    #[cfg(feature = "nightly")]
    fn is_empty(&self) -> bool {
        self.iter.len() < A::SIZE
    }
}

impl<I: fmt::Debug, A: Array> fmt::Debug for ArrayChunks<I, A> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Chunks")
            .field("iter", &self.iter)
            .field("chunk_len", &A::SIZE)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use crate::{iter::IteratorExt, ArrayExt};

    #[test]
    fn basic_usage() {
        let mut iter = [0, 1, 2, 3, 4].iter_move().array_chunks::<[_; 2]>();

        assert_eq!(iter.next(), Some([0, 1]));
        assert_eq!(iter.next(), Some([2, 3]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn back() {
        let mut iter = [0, 1, 2, 3, 4].iter_move().array_chunks::<[_; 2]>().rev();

        assert_eq!(iter.next(), Some([4, 3]));
        assert_eq!(iter.next(), Some([2, 1]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn len() {
        macro_rules! assert_len {
            (size: $array_size:literal, chunk: $chunk_size:literal, expect: $expected:literal) => {
                let array = [0; $array_size].iter_move().array_chunks::<[_; $chunk_size]>();
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

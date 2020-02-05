use core::{
    cmp::Ordering,
    fmt::{Display, Error, Formatter},
};

/// Error that represents difference in expected sizes of an array.
#[derive(Debug, PartialEq, Eq)]
pub enum SizeError<T = ()> {
    /// Size is less than expected by `.0`
    Less(usize, T),
    /// Size is greater than expected by `.0`
    Greater(usize, T),
}

impl<T> SizeError<T> {
    pub(crate) fn expect(x: usize, expected: usize, data: T) -> Result<T, Self> {
        match x.cmp(&expected) {
            Ordering::Equal => Ok(data),
            Ordering::Less => Err(SizeError::Less(expected - x, data)),
            Ordering::Greater => Err(SizeError::Greater(x - expected, data)),
        }
    }

    pub(crate) fn expect_size<Item>(slice: &[Item], expected: usize, data: T) -> Result<T, Self> {
        Self::expect(slice.len(), expected, data)
    }
}

impl<T: Display> Display for SizeError<T> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            Self::Less(n, data) => write!(
                f,
                "Size is less than expected by {n}; data: {data}",
                n = n,
                data = data
            ),
            Self::Greater(n, data) => write!(
                f,
                "Size is less than expected by {n}; data: {data}",
                n = n,
                data = data
            ),
        }
    }
}

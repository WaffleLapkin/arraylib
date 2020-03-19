use core::fmt::{self, Display, Formatter};

/// Error that is caused by wrong sizes of slices/arrays
#[derive(Debug, PartialEq, Eq, Copy, Clone, Default)]
pub struct SizeError<T = ()>(pub T);

impl<T: Display> Display for SizeError<T> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        f.write_str("wrong size")
    }
}

use crate::{iter::IteratorExt, Array};

/// Trait for conversation between `&[T; N]` and `[&T; N]` (or `&mut [T; N]` and `[&mut T; N]`)
pub trait ArrayAsRef<'a>: Array
where
    <Self as Array>::Item: 'a,
{
    /// Result of the 'shared' conversation, in other words `[&T; N]`
    /// (where `T = Self::Item, N = Self::Size`)
    type AsRef: Array<Item = &'a <Self as Array>::Item>;

    /// Result of the 'unique' conversation, in other words `[&mut T; N]`
    /// (where `T = Self::Item, N = Self::Size`)
    type AsMut: Array<Item = &'a mut <Self as Array>::Item>;

    /// Convert `&self` to `[&T; N]` (where `T = Self::Item, N = Self::Size`)
    ///
    /// ## Examples
    /// ```
    /// use arraylib::ArrayAsRef;
    ///
    /// let arr = [0, 1, 2, 3];
    /// let ref_arr = arr.as_ref_array();
    /// assert_eq!(ref_arr, [&0, &1, &2, &3]);
    /// assert_eq!(arr, [0, 1, 2, 3]);
    /// ```
    /// ```
    /// use arraylib::{ArrayAsRef, ArrayExt};
    ///
    /// // Don't do like this, it's just an example
    /// fn index_of<A>(a: &A, x: A::Item) -> Option<usize>
    /// where
    ///     for<'a> A: ArrayAsRef<'a>,
    ///     A::Item: PartialEq,
    /// {
    ///     a.as_ref_array()
    ///         .iter_move()
    ///         .enumerate()
    ///         .find(|&(_, it)| it == &x)
    ///         .map(|(idx, _)| idx)
    /// }
    ///
    /// let arr = [-2, 1, -1, 2];
    /// assert_eq!(index_of(&arr, 1), Some(1));
    /// assert_eq!(index_of(&arr, 2), Some(3));
    /// assert_eq!(index_of(&arr, 0), None);
    /// ```
    ///
    /// **NOTE**: it's nighly recommended to use iterators when you need to
    /// perform more that one operation (e.g. map + as_ref) because iterators
    /// are lazy and `ArrayAsRef` isn't.
    ///
    /// See also: [`as_mut_array`](crate::ArrayAsRef::as_mut_array)
    fn as_ref_array(&'a self) -> Self::AsRef;

    /// Convert `&mut self` to `[&mut T; N]` (where `T = Self::Item, N = Self::Size`)
    ///
    /// ## Examples
    /// ```
    /// use arraylib::ArrayAsRef;
    ///
    /// let mut arr = [0, 1, 2, 3];
    /// let ref_arr = arr.as_mut_array();
    /// assert_eq!(ref_arr, [&mut 0, &mut 1, &mut 2, &mut 3]);
    /// assert_eq!(arr, [0, 1, 2, 3]);
    /// ```
    /// ```
    /// use arraylib::{ArrayAsRef, ArrayExt};
    ///
    /// // Don't do like this, it's just an example
    /// fn find_and_replace<A>(a: &mut A, find: &A::Item, replace: A::Item) -> A::Item
    /// where
    ///     for<'a> A: ArrayAsRef<'a>,
    ///     A::Item: PartialEq,
    /// {
    ///     let mut x = a.as_mut_array()
    ///         .iter_move()
    ///         .find(|it| it == &find);
    ///     match x {
    ///         Some(ref mut inner) => core::mem::replace(inner, replace),
    ///         None => replace,
    ///     }
    /// }
    ///
    /// let mut arr = [-2, 1, -1, 2];
    /// assert_eq!(find_and_replace(&mut arr, &1, 8), 1);
    /// assert_eq!(arr, [-2, 8, -1, 2]);
    /// ```
    ///
    /// **NOTE**: it's nighly recommended to use iterators when you need to
    /// perform more that one operation (e.g. map + as_ref) because iterators
    /// are lazy and `ArrayAsRef` isn't.
    ///
    /// See also: [`as_ref_array`](crate::ArrayAsRef::as_ref_array)
    fn as_mut_array(&'a mut self) -> Self::AsMut;
}

impl<'a, T: 'a> ArrayAsRef<'a> for [T; 0] {
    type AsRef = [&'a T; 0];

    type AsMut = [&'a mut T; 0];

    #[inline]
    fn as_ref_array(&'a self) -> Self::AsRef {
        []
    }

    #[inline]
    fn as_mut_array(&'a mut self) -> Self::AsMut {
        []
    }
}

macro_rules! as_ref_impl {
    ($e:tt) => {
        impl<'a, T: 'a> ArrayAsRef<'a> for [T; $e] {
            type AsRef = [&'a T; $e];

            type AsMut = [&'a mut T; $e];

            #[inline]
            fn as_ref_array(&'a self) -> Self::AsRef {
                self.as_slice().iter().collect_array::<Self::AsRef>()
            }

            #[inline]
            fn as_mut_array(&'a mut self) -> Self::AsMut {
                self.as_mut_slice()
                    .iter_mut()
                    .collect_array::<Self::AsMut>()
            }
        }
    };
}

array_impls!(as_ref_impl);

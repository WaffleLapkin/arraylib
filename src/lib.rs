//! This crate provides API for working with arrays, e.g.:
//!   1) Abstraction over arrays (you can use [`Array`] trait as bound on
//!      generics)
//!   2) Creation of arrays (see [`Array`] trait)
//!   3) Doing operations on arrays that produce arrays (see
//!      [`ArrayMap`] and [`ArrayAsRef`] traits)
//!   4) By-value iterating on array (see [`IterMove`])
//!   5) `Iterator` adapter that yield fixed sized chunks of inner iterator
//!      (see [`ArrayChunks`])
//!
//! [`Array`]: crate::Array
//! [`ArrayExt`]: crate::ArrayExt
//! [`IterMove`]: crate::iter::IterMove
//! [`ArrayChunks`]: crate::iter::ArrayChunks
//!
//! ## Example
//!
//! ```
//! use arraylib::{Array, ArrayExt};
//!
//! // Array creation
//! let arr = <[_; 11]>::unfold(1, |it| {
//!     let res = *it;
//!     *it *= -2;
//!     res
//! });
//!
//! // Mapping
//! let arr = arr.lift(|it| it * 2);
//! assert_eq!(arr, [2, -4, 8, -16, 32, -64, 128, -256, 512, -1024, 2048]);
//!
//! // By-value iterator
//! arr.iter_move().for_each(|i: i32| {})
//! ```
//!
//! ## Sizes Limitations
//!
//! Because of lack of [`const generics`] it's impossible to implement traits on
//! arrays of _all_ sizes (see [std note about that]), so this crate implements
//! traits only for these sizes:
//! - `[0; 32]`
//! - `8 * [5; 12]` (40, 48, ..., 96)
//! - `100 * [1; 10]` (100, 200, ..., 1000)
//! - `2 ** [7; 16]` (128, 256, ..., 65536)
//! - `[33; 128]` (If **array-impls-33-128** feature enabled)
//! - `[129; 256]` (If **array-impls-129-256** feature enabled)
//!
//! [`const generics`]: https://github.com/rust-lang/rust/issues/44580
//! [std note about that]: https://doc.rust-lang.org/std/primitive.array.html
//!
//! ## no_std
//!
//! This lib doesn't depend on `std`, so it can be used in crates with the
//! `#![no_std]` attribute.
//!
//! ## Features
//!
//! This crate provide next features:
//! - **alloc** — enables API that depend on `alloc` crate
//! - **nightly** — enable features that require nightly features:
//!   - `trusted_len` ([tracking issue][trusted_ti]) (Adds impl of `TrustedLen`
//!     for iterators)
//!   - `exact_size_is_empty` ([tracking issue][is_empty_ti]) (Implement
//!     `<{Chunks,IterMove} as ExactSizeIterator>::is_empty` more effective)
//! - **array-impls-33-128** — adds impl of the [`Array`] trait for arrays of
//!   sizes 33-128 (inclusive)
//! - **array-impls-129-256** — adds impl of the [`Array`] trait for arrays of
//!   sizes 129-256 (inclusive)
//!
//! [trusted_ti]: https://github.com/rust-lang/rust/issues/37572
//! [is_empty_ti]: https://github.com/rust-lang/rust/issues/35428
//!
//! ## Alternatives
//!
//! Crates those provide similar API (or part of it):
//!
//! - [`generic_array`](https://docs.rs/generic-array)
//! - [`array_init`](https://docs.rs/array-init/) (analogs to [`Array::from_fn`]
//!   and [`Array::from_iter`])
//! - [`array_ext`](https://docs.rs/array_ext)
//! - [`slice_as_array`](https://peterreid.github.io/slice_as_array/slice_as_array/index.html)
//!   (analogs to [`ArrayExt::from_slice`] and [`Array::from_iter`])
//! - [`arraytools`](https://docs.rs/arraytools)
//! - [`core::array::FixedSizeArray`](https://doc.rust-lang.org/beta/core/array/trait.FixedSizeArray.html)
//! - [`stackvec`](https://docs.rs/stackvec/)
//! - [`array_iterator`](https://docs.rs/array_iterator/)
//! - [`arraymap`](https://docs.rs/arraymap/)
//!
//! [`Array::from_fn`]: crate::Array::from_fn
//! [`Array::from_iter`]: crate::Array::from_iter
//!
//! ## Safety
//!
//! To achieve good performance and support so many array sizes, this
//! crate uses a alot of unsafe code (by commit `079871cc` there are 17 `unsafe
//! {}` blocks). All `unsafe`s were checked with care and have a "Safety"
//! comment.
//!
//! If you see that some `unsafe`s could be removed without performance loss (we
//! need benchmarks, oh) please fill an [issue].
//!
//! [issue]: https://github.com/WaffleLapkin/arraylib/issues/new
// We use std in tests to catch panic
#![cfg_attr(not(test), no_std)]
// Some sweaty nightly features
#![cfg_attr(feature = "nightly", feature(trusted_len, exact_size_is_empty))]
// I hate missing docs
#![deny(missing_docs)]
// And I like inline
#![warn(clippy::missing_inline_in_public_items)]
// we pass "--cfg docsrs" when building docs to add `This is supported on feature="..." only.`
//
// To properly build docs of this crate run
// ```console
// $ RUSTDOCFLAGS="--cfg docsrs" cargo doc --open --features "alloc nightly"
// ```
#![cfg_attr(all(docsrs, feature = "nightly"), feature(doc_cfg))]

#[cfg(feature = "alloc")]
extern crate alloc;

/// Utils that help implementing public API
#[macro_use]
pub(crate) mod util {
    /// Array initialization
    pub(crate) mod init;

    /// `T -> U` transmute (analog to `core::mem::transmute`)
    pub(crate) mod transmute;
}

pub use self::{
    array::Array,
    ext::{
        array_ext::ArrayExt,
        shorthand::ArrayShorthand,
        slice_ext::{MaybeUninitSlice, Slice},
    },
};

/// Iterator related things
pub mod iter {
    pub use self::{chunks::ArrayChunks, ext::IteratorExt, windows::ArrayWindows};

    mod chunks;
    mod ext;
    mod windows;
}

// === private but reexported ===
mod array;

/// Different extension traits
mod ext {
    /// Array ext
    pub(super) mod array_ext;
    /// Also array ext (but for `.as_slice().method()` -> `.method()` shortcuts)
    pub(super) mod shorthand;
    /// Slice ext
    pub(super) mod slice_ext;
}

/// Run tests from readme
#[cfg_attr(feature = "nightly", doc = include_str!("../README.md"))]
#[cfg(doctest)]
pub struct ReadmeDocTests;

/// Error that is caused by wrong sizes of slices/arrays
#[derive(Debug, PartialEq, Eq, Copy, Clone, Default)]
pub struct SizeError(());

impl core::fmt::Display for SizeError {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        f.write_str("wrong size")
    }
}

/// Conditional compilation depending on whether `arraylib` is built with
/// `alloc` feature.
///
/// This macro is needed if you want to implement `Array` on your type (change
/// your mind, you fool) which requires `into_boxed_slice` method, but only if
/// `alloc` feature is enabled.
///
/// When `arraylib` is built with `alloc` feature, this macro expands
/// transparently into just the input tokens.
///
/// ```
/// macro_rules! if_alloc {
///     ($($tt:tt)*) => {
///         $($tt)*
///     };
/// }
/// ```
///
/// When built without `alloc` feature, this macro expands to
/// nothing.
///
/// ```
/// macro_rules! if_alloc {
///     ($($tt:tt)*) => {};
/// }
/// ```
// idea is copy-pasted from serde (https://docs.serde.rs/serde/macro.serde_if_integer128.html)
#[cfg(feature = "alloc")]
#[macro_export]
macro_rules! if_alloc {
    ($($tt:tt)*) => {
        $($tt)*
    };
}

#[cfg(not(feature = "alloc"))]
#[doc(hidden)]
#[macro_export]
macro_rules! if_alloc {
    ($($tt:tt)*) => {};
}

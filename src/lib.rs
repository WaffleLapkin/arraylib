//! This crate provides API for
//! 1) Abstraction over arrays (you can use [`Array` trait][arr] as bound on generics)
//! 2) Doing operations on arrays that produce arrays (see [`ArrayExt`] trait)
//! 3) By-value iterating on array (see [`IterMove`])
//!
//! [arr]: crate::Array
//! [`ArrayExt`]: crate::ArrayExt
//! [`IterMove`]: crate::iter::IterMove
//!
//! ## Sizes Limitations
//!
//! Because of lack of [`const generics`] it's impossible to implement traits on arrays of _all_
//! sizes (see [std note about that]), so this crate implements traits only for these sizes:
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
//! If you have an array of another size, open an [issue] describing your usecase
//! or use some [alternative lib]
//!
//! [issue]: https://github.com/WaffleLapkin/arraylib/issues/new
//! [alternative lib]: #Alternatives
//!
//! ## no_std
//!
//! This lib doesn't depend on `std`, so it can be used in crates with the `#![no_std]` attribute.
//!
//! ## Features
//!
//! This crate provide next features:
//! - **alloc** — enables API that depend on `alloc` crate
//! - **nightly** — enable features that require nightly features:
//!   + `trusted_len` ([tracking issue][trusted_ti]) (Adds impl of `TrustedLen` for iterators)
//!   + `exact_size_is_empty` ([tracking issue][is_empty_ti]) (Implement `Chunks::is_empty` more effective)
//! - **array-impls-33-128** — adds impl of the [`Array`][arr] trait for arrays of sizes 33-128 (inclusive)
//! - **array-impls-129-256** — adds impl of the [`Array`][arr] trait for arrays of sizes 129-256 (inclusive)
//!
//! [trusted_ti]: https://github.com/rust-lang/rust/issues/37572
//! [is_empty_ti]: https://github.com/rust-lang/rust/issues/35428
//!
//! ## Alternatives
//!
//! Crates those provide similar API (or part of it):
//!
//! - [`generic_array`](https://docs.rs/generic-array)
//! - [`array_init`](https://docs.rs/array-init/)
//!   (analogs to [`Array::from_fn`] and [`Array::from_iter`])
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
//! This crate uses a lot of unsafe code blah blah blah
//!
// We use std in tests to catch panic
#![cfg_attr(not(test), no_std)]
// Some sweaty nightly features
#![cfg_attr(feature = "nightly", feature(trusted_len, exact_size_is_empty))]
// I hate missing docs
#![deny(missing_docs)]
// And I like inline
#![warn(clippy::missing_inline_in_public_items)]

#[cfg(feature = "alloc")]
extern crate alloc;

/// Utils that help implementing public API
#[macro_use]
pub(crate) mod util {
    #[macro_use]
    /// Helper macros these are used in this lib
    mod local_macros;

    /// Array initialization
    pub(crate) mod init;

    /// `T -> U` transmute (analog to `core::mem::transmute`)
    pub(crate) mod transmute;
}

pub use {
    array::Array,
    error::SizeError,
    ext::{
        array_ext::ArrayExt,
        shorthand::ArrayShorthand,
        slice_ext::{MaybeUninitSlice, Slice},
    },
    transform::{as_ref::ArrayAsRef, map::ArrayMap},
    wrap::ArrayWrapper,
};

/// Iterator related things
pub mod iter {
    pub use {chunks::ArrayChunks, ext::IteratorExt, iter_move::IterMove};

    mod chunks;
    mod ext;
    mod iter_move;
}

// === private but reexported ===
mod array;
mod error;
mod wrap;

/// Array transformers like map (`[T; N]` -> `[U; N]`)
///
/// Commonly just shortcuts for `.iter_move().*method*(...).collect_array()`
mod transform {
    /// `&(mut) [T; N]` -> `[&(mut) T; N]`
    pub(super) mod as_ref;
    /// `[T; N]` -> `[U; N]`
    pub(super) mod map;
}

/// Different extension traits
mod ext {
    /// Array ext
    pub(super) mod array_ext;
    /// Also array ext (but for `.as_slice().method()` -> `.method()` shortcuts)
    pub(super) mod shorthand;
    /// Slice ext
    pub(super) mod slice_ext;
}

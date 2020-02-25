use core::mem;

/// **Extremely unsafe** (even more unsafe that original!) version of
/// [`mem::transmute`] that doesn't even check sizes of `T` and `U`.
///
/// This function is a wrapper around [`mem::transmute_copy`] that takes ownership.
///
/// ## Safety
///
/// See docs of [`mem::transmute`] and [`mem::transmute_copy`]
///
/// [`mem::transmute`]: core::mem::transmute
/// [`mem::transmute_copy`]: core::mem::transmute_copy
pub(crate) unsafe fn extremely_unsafe_transmute<T, U>(value: T) -> U {
    debug_assert!(
        mem::size_of::<T>() == mem::size_of::<U>(),
        "Sizes of transmuted types **MUST** be equal. Code that done that transmutation caused UB."
    );

    // Ensure that `value` won't be dropped
    let value = mem::ManuallyDrop::new(value);
    // Interprets `T` as `U`
    mem::transmute_copy::<T, U>(&value)
}

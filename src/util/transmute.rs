use core::{mem, ptr};

/// **Extremely unsafe** (even more unsafe that original!) version of
/// [`mem::transmute`] that doesn't even check sizes of `T` and `U`.
///
/// [`mem::transmute`]: core::mem::transmute
pub(crate) unsafe fn extremely_unsafe_transmute<T, U>(e: T) -> U {
    debug_assert!(
        mem::size_of::<T>() == mem::size_of::<U>(),
        "Sizes of transmuted types **MUST** be equal. Code that done that transmutation caused UB."
    );

    let res: U = ptr::read((&e as *const T).cast::<U>());
    mem::forget(e);
    res
}

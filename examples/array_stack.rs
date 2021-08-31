//! An example of using `Continuous` to build an array-based collection.
//!
//! All operations (except creation and unsizing) are defined on
//! `ArrayStack<[T]>` to make the codegen impact smaller (hoping for faster
//! compilation and smaller binaries).
//!
//! All nightly features are used only to make all operations `const`. Without
//! `const` restrictions this example works on stable.
//!
//! The example should also work without `std`/`alloc`.
#![feature(const_mut_refs)]
#![feature(const_maybe_uninit_as_ptr)]
#![feature(const_ptr_read)]
#![feature(const_raw_ptr_deref)]
#![feature(const_slice_from_raw_parts)]
#![feature(label_break_value)]
#![allow(clippy::redundant_pattern_matching)]

use core::mem::MaybeUninit;

use arraylib::Continuous;

#[repr(C)]
pub struct ArrayStack<S: ?Sized + Continuous> {
    len: usize,
    inner: S::Uninit,
}

impl<T, const N: usize> ArrayStack<[T; N]> {
    const U: MaybeUninit<T> = MaybeUninit::uninit();

    pub const fn new() -> Self {
        Self {
            len: 0,
            inner: [Self::U; N],
        }
    }

    pub const fn unsize(&mut self) -> &mut ArrayStack<[T]> {
        use core::ptr::slice_from_raw_parts_mut;

        // For some reason `ArrayStack<[T]>` doesn't implement `Pointee`, so it's
        // impossible to use `core::ptr::from_raw_parts_mut` here.
        //
        // This function uses `slice_from_raw_parts_mut` to create a pointer with
        // desired metadata.
        let ptr = slice_from_raw_parts_mut(self as *mut Self as *mut T, N);

        // ## Safety
        //
        // `ArrayStack<[T; N]>` and `ArrayStack<[T]>` are guaranteed to have the same
        // layout. `ptr` contains a proper metadata (as long as slice metadata is the
        // same as a dst with a slice metadata) and is derived from a mutable reference.
        unsafe { &mut *(ptr as *mut ArrayStack<[T]>) }
    }
}
impl<T> ArrayStack<[T]> {
    pub const fn push(&mut self, item: T) -> Result<(), T> {
        if self.len == self.inner.len() {
            Err(item)
        } else {
            self.inner[self.len] = MaybeUninit::new(item);
            self.len += 1;
            Ok(())
        }
    }

    pub const fn pop(&mut self) -> Option<T> {
        match self.len {
            0 => None,

            // ## Safety
            //
            // `self.inner[..self.len]` is always initialized
            _ => unsafe {
                self.len -= 1;
                Some(self.inner[self.len].as_ptr().read())
            },
        }
    }

    pub const fn peek(&self) -> Option<&T> {
        match self.len {
            0 => None,

            // ## Safety
            //
            // `self.inner[..self.len]` is always initialized
            _ => unsafe { Some(&*self.inner[self.len - 1].as_ptr()) },
        }
    }
}

const TEST: i32 = 'a: {
    let mut stack = ArrayStack::<[i32; 2]>::new();

    if let Err(_) = stack.unsize().push(1) {
        break 'a -1;
    }

    let stack = stack.unsize();

    let p0 = match stack.peek() {
        None => break 'a -2,
        Some(&x) => x,
    };

    if let Err(_) = stack.push(2) {
        break 'a -3;
    }

    let p1 = match stack.peek() {
        None => break 'a -4,
        Some(&x) => x,
    };

    if let Ok(()) = stack.push(3) {
        break 'a -5;
    }

    match (stack.pop(), stack.pop()) {
        (Some(a), Some(b)) => p0 + p1 + a + b,
        _ => -6,
    }
};

fn main() {
    assert_eq!(TEST, 6);
}

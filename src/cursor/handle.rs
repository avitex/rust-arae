use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};

use alloc::rc::Rc;
use alloc::sync::Arc;

use super::{Cursor, CursorPtr};

/// An extension over a [`Cursor`] type which ensures the data pointed to is
/// available to dereference.
///
/// # Safety
/// Implementations must ensure the guard returned can dereference safely to the
/// memory pointed to by the cursor and that there are no current mutable
/// references alive.
///
/// # Panics
/// Implementations may decide to panic when a `Guard` cannot be constructed.
///
/// # Example
/// ```rust
/// use std::sync::Arc;
/// use arae::cursor::Handle;
///
/// let handle = Arc::new(1);
///
/// assert_eq!(*handle.lock_ref(), 1);
/// ```
pub unsafe trait Handle<'a, T>: Cursor<T> {
    /// Guard type that represents a valid immutable borrow of data.
    type Guard: Deref<Target = T>;

    /// Returns a new `Self::Guard` available for dereferencing.
    fn lock_ref(&self) -> Self::Guard;
}

/// An extension over a [`Cursor`] type which ensures the data pointed to is
/// available to dereference mutably.
///
/// # Safety
/// Implementations must ensure the guard returned can mutably dereference safely
/// to the memory pointed to by the cursor and that there are no other current
/// immutable or mutable references alive.
///
/// # Panics
/// Implementations may decide to panic when a `Guard` cannot be constructed.
///
/// # Example
/// ```rust
/// use std::rc::Rc;
/// use arae::cursor::{Handle, HandleMut};
///
/// let mut handle = Rc::new(1);
///
/// *handle.lock_mut() = 2;
///
/// assert_eq!(*handle.lock_ref(), 2);
/// ```
pub unsafe trait HandleMut<'a, T>: Handle<'a, T> {
    /// Guard type that represents a valid mutable borrow of data.
    type GuardMut: DerefMut<Target = T>;

    /// Returns a new `Self::GuardMut` available for dereferencing.
    fn lock_mut(&mut self) -> Self::GuardMut;
}

///////////////////////////////////////////////////////////////////////////////

impl<T> Cursor<T> for Arc<T> {
    fn as_ptr(&self) -> CursorPtr<T> {
        let ptr = &**self as *const T;
        // Safe because Arc guarantees its pointer is non-null
        unsafe { CursorPtr::new_unchecked(ptr as _) }
    }
}

unsafe impl<'a, T> Handle<'a, T> for Arc<T> {
    type Guard = CursorPtrGuard<'a, T>;

    fn lock_ref(&self) -> Self::Guard {
        unsafe { CursorPtrGuard::new(self.as_ptr()) }
    }
}

///////////////////////////////////////////////////////////////////////////////

impl<T> Cursor<T> for Rc<T> {
    fn as_ptr(&self) -> CursorPtr<T> {
        let ptr = &**self as *const T;
        // Safe because Rc guarantees its pointer is non-null
        unsafe { CursorPtr::new_unchecked(ptr as _) }
    }
}

unsafe impl<'a, T> Handle<'a, T> for Rc<T> {
    type Guard = CursorPtrGuard<'a, T>;

    fn lock_ref(&self) -> Self::Guard {
        unsafe { CursorPtrGuard::new(self.as_ptr()) }
    }
}

unsafe impl<'a, T> HandleMut<'a, T> for Rc<T> {
    type GuardMut = CursorPtrGuardMut<'a, T>;

    fn lock_mut(&mut self) -> Self::GuardMut {
        let mut_ref = Rc::get_mut(self).expect("other Rc references exist");
        unsafe {
            let ptr = CursorPtr::new_unchecked(mut_ref as _);
            CursorPtrGuardMut::new(ptr)
        }
    }
}

/// Wrapper around a [`CursorPtr`] with the guarantee that the data it
/// points to can be safely dereferenced.
#[derive(Debug)]
pub struct CursorPtrGuard<'a, T> {
    ptr: CursorPtr<T>,
    lifetime: PhantomData<&'a ()>,
}

impl<'a, T> CursorPtrGuard<'a, T> {
    unsafe fn new(ptr: CursorPtr<T>) -> Self {
        Self {
            ptr,
            lifetime: PhantomData,
        }
    }
}

impl<'a, T> Deref for CursorPtrGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // Safe as the constructor of this guard promises
        // us we can deref the cursor ptr safely.
        unsafe { &*self.ptr.ptr_mut() }
    }
}

/// A mutable variant of [`CursorPtrGuard`].
#[derive(Debug)]
pub struct CursorPtrGuardMut<'a, T> {
    ptr: CursorPtr<T>,
    lifetime: PhantomData<&'a ()>,
}

impl<'a, T> CursorPtrGuardMut<'a, T> {
    unsafe fn new(ptr: CursorPtr<T>) -> Self {
        Self {
            ptr,
            lifetime: PhantomData,
        }
    }
}

impl<'a, T> Deref for CursorPtrGuardMut<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // Safe as the constructor of this guard promises
        // us we can deref the cursor ptr safely.
        unsafe { &*self.ptr.ptr_mut() }
    }
}

impl<'a, T> DerefMut for CursorPtrGuardMut<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // Safe as the constructor of this guard promises
        // us we can deref the cursor ptr safely.
        unsafe { &mut *self.ptr.ptr_mut() }
    }
}

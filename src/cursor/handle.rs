use core::ops::{Deref, DerefMut};

use super::Cursor;

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
    type Guard: Deref<Target = T> + 'a;

    /// Returns a new `Self::Guard` available for dereferencing.
    fn lock_ref(&'a self) -> Self::Guard;
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
    type GuardMut: DerefMut<Target = T> + 'a;

    /// Returns a new `Self::GuardMut` available for dereferencing.
    fn lock_mut(&'a mut self) -> Self::GuardMut;
}

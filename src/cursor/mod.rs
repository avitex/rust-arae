//! Cursors for [`Cursed`](crate::Cursed) types.

mod atomic;
mod handle;
mod imp;
mod pointer;

#[cfg(feature = "atomic")]
pub use self::atomic::AtomicCursorPtr;
pub use self::handle::{Handle, HandleMut};
pub use self::pointer::CursorPtr;

use super::{Cursed, Mutable};

/// Implemented for types that represent a location within a [`Cursed`] structure.
///
/// A `Cursor` is created from and used with initialized its owning [`Cursed`]
/// structure, however if the structure is dropped, will point to invalid memory.
///
/// Safety is achieved via `Cursor` validating it's owned by the [`Cursed`] structure.
pub trait Cursor<T>: Clone {
    /// Get the underlying `Cursor` pointer.
    fn as_ptr(&self) -> CursorPtr<T>;
}

/// A [`Cursor`] that guarantees the data it dereferences to is valid while `self` is.
///
/// This guarantee provides the foundation for a referenced counted [`Cursor`],
/// and operations on a [`Cursor`] without the need to reference the owner.
///
/// # Safety
/// Implementations must guarantee referenced data is valid while `self` is alive,
/// and that data referenced cannot be mutated without further synchronization.
pub unsafe trait Detached<T>: Cursor<T> {}

/// Extended functionality for implementations of [`Cursor`].
pub trait CursorExt<T>: Cursor<T> + Sized {
    /// Returns a reference to the element the [`Detached`] [`Cursor`] is pointing to.
    fn as_ref(&self) -> &T
    where
        Self: Detached<T>,
    {
        // Safe due to the constraints on `Detached`.
        unsafe { &*self.as_ptr().ptr_mut() }
    }

    /// Returns a reference to the element the `Cursor` is pointing to with
    /// the given owner.
    ///
    /// # Example
    /// ```rust
    /// use arae::{CurVec, CursorExt, Bounded};
    ///
    /// let mut vec: CurVec<_> = vec![0].into();
    ///
    /// let cursor = vec.hptr();
    ///
    /// assert_eq!(*cursor.as_ref_with(&vec), 0);
    /// ```
    ///
    /// # Panics
    /// Panics if `cursed` does not own self.
    #[inline]
    fn as_ref_with<'a, C: 'a>(&self, cursed: &'a C) -> &'a T
    where
        C: Cursed<T, Cursor = Self>,
    {
        assert!(cursed.is_owner(self));
        unsafe { &*self.as_ptr().ptr_mut() }
    }

    /// Returns a mutable reference to the element the `Cursor` is pointing to with
    /// the given owner.
    ///
    /// # Example
    /// ```rust
    /// use arae::{CurVec, CursorExt, Bounded};
    ///
    /// let mut vec: CurVec<_> = vec![0].into();
    ///
    /// let cursor = vec.hptr();
    ///
    /// *cursor.as_mut_with(&mut vec) = 1;
    ///
    /// assert_eq!(*cursor.as_ref_with(&vec), 1);
    /// ```
    ///
    /// # Panics
    /// Panics if `cursed` does not own self.
    #[inline]
    fn as_mut_with<'a, C: 'a>(&self, cursed: &'a mut C) -> &'a mut T
    where
        C: Mutable<T, Cursor = Self>,
    {
        assert!(cursed.is_owner(self));
        unsafe { &mut *self.as_ptr().ptr_mut() }
    }
}

impl<T, U> CursorExt<U> for T where T: Cursor<U> {}

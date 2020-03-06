use core::cmp;
use core::marker::PhantomData;
use core::ptr::NonNull;

use crate::Ring;

#[cfg(feature = "atomic")]
use core::sync::atomic::{AtomicPtr, Ordering};

/// An opaque structure that represents a location within a `Ring`.
///
/// `Cursor`s can only be created from and used within a initialized `Ring`,
/// but if a `Ring` is dropped it will point to invalid memory.
///
/// Safety is achieved via the `Ring` validating it owns the `Cursor`.
pub struct Cursor<T> {
    ptr: NonNull<T>,
}

impl<T> Cursor<T> {
    /// Constructs new cursor given a valid pointer.
    #[inline]
    pub(crate) fn new(ptr: NonNull<T>) -> Self {
        Self { ptr }
    }

    /// Constructs new cursor given a unchecked pointer.
    #[inline]
    pub(crate) unsafe fn new_unchecked(ptr: *mut T) -> Self {
        Self::new(NonNull::new_unchecked(ptr))
    }

    #[inline]
    pub(crate) fn ptr(self) -> NonNull<T> {
        self.ptr
    }

    #[cfg(feature = "atomic")]
    #[inline]
    pub fn into_atomic(self) -> AtomicCursor<T> {
        AtomicCursor::<T>::new(self)
    }
}

impl<T> Clone for Cursor<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self::new(self.ptr())
    }
}
impl<T> Copy for Cursor<T> {}

impl<T> PartialEq for Cursor<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr
    }
}

impl<T> Eq for Cursor<T> {}

impl<T> PartialOrd for Cursor<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.ptr.partial_cmp(&other.ptr)
    }
}

impl<T> Ord for Cursor<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.ptr.cmp(&other.ptr)
    }
}

#[cfg(feature = "atomic")]
pub struct AtomicCursor<T> {
    ptr: AtomicPtr<T>,
    marker: PhantomData<T>,
}

#[cfg(feature = "atomic")]
impl<T> AtomicCursor<T> {
    /// Constructs new atomic cursor given a `Cursor`.
    #[inline]
    pub fn new(cursor: Cursor<T>) -> Self {
        let ptr = AtomicPtr::new(cursor.ptr().as_ptr());
        Self {
            ptr,
            marker: PhantomData,
        }
    }

    #[inline]
    pub fn load(&self, order: Ordering) -> Cursor<T> {
        let ptr = self.ptr.load(order);
        unsafe { Cursor::new_unchecked(ptr) }
    }

    #[inline]
    pub fn store(&self, cursor: Cursor<T>, order: Ordering) {
        self.ptr.store(cursor.ptr().as_ptr(), order);
    }

    #[inline]
    pub fn advance(&self, ring: &Ring<T>, order: Ordering) {
        let cursor = self.load(order);
        let cursor = ring.advance(cursor);
        self.store(cursor, order);
    }
}

#[cfg(feature = "atomic")]
impl<T> From<Cursor<T>> for AtomicCursor<T> {
    fn from(cursor: Cursor<T>) -> Self {
        cursor.into_atomic()
    }
}

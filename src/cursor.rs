use core::ptr::NonNull;
use core::{cmp, fmt};

#[cfg(feature = "atomic")]
use crate::atomic::AtomicCursor;

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

impl<T> fmt::Debug for Cursor<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Cursor({:?})", self.ptr)
    }
}

use core::cmp;
use core::marker::PhantomData;
use core::ptr::NonNull;

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
    pub(crate) fn new(ptr: NonNull<T>) -> Self {
        Self { ptr }
    }

    pub(crate) fn ptr(self) -> NonNull<T> {
        self.ptr
    }

    #[cfg(feature = "atomic")]
    pub fn into_atomic(self) -> AtomicCursor<T> {
        AtomicCursor::<T>::new(self)
    }
}

impl<T> Clone for Cursor<T> {
    fn clone(&self) -> Self {
        Self::new(self.ptr().clone())
    }
}
impl<T> Copy for Cursor<T> {}

impl<T> PartialEq for Cursor<T> {
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr
    }
}

impl<T> Eq for Cursor<T> {}

impl<T> PartialOrd for Cursor<T> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.ptr.partial_cmp(&other.ptr)
    }
}

impl<T> Ord for Cursor<T> {
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
    pub fn new(cursor: Cursor<T>) -> Self {
        unimplemented!()
    }

    pub fn load(&self, order: Ordering) -> Cursor<T> {
        unimplemented!()
    }
}

#[cfg(feature = "atomic")]
impl<T> From<Cursor<T>> for AtomicCursor<T> {
    fn from(cursor: Cursor<T>) -> Self {
        cursor.into_atomic()
    }
}

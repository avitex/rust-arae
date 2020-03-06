use core::fmt;
use core::marker::PhantomData;
use core::sync::atomic::{AtomicPtr, Ordering};

use crate::{Cursor, Ring};

/// An atomic version of `Cursor`.
pub struct AtomicCursor<T> {
    ptr: AtomicPtr<T>,
    marker: PhantomData<T>,
}

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

    /// Loads the `Cursor` value with the given atomic ordering.
    #[inline]
    pub fn load(&self, order: Ordering) -> Cursor<T> {
        let ptr = self.ptr.load(order);
        unsafe { Cursor::new_unchecked(ptr) }
    }

    /// Stores a `Cursor` value with the given atomic ordering.
    #[inline]
    pub fn store(&self, cursor: Cursor<T>, order: Ordering) {
        self.ptr.store(cursor.ptr().as_ptr(), order);
    }

    /// Atomically advance the cursor given it's owning ring.
    ///
    /// # Panics
    /// Panics if the ring does not own the cursor.
    #[inline]
    pub fn next(&self, ring: &Ring<T>, order: Ordering) {
        let cursor = self.load(order);
        let cursor = ring.next(cursor);
        self.store(cursor, order);
    }
}

impl<T> fmt::Debug for AtomicCursor<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AtomicCursor({:?})", self.ptr)
    }
}

impl<T> From<Cursor<T>> for AtomicCursor<T> {
    fn from(cursor: Cursor<T>) -> Self {
        cursor.into_atomic()
    }
}

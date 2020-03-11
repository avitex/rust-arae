use core::fmt;

use crate::atomic::{AtomicPtr, Ordering};
use crate::cursor::CursorPtr;
use crate::{Bounded, CursedExt, Sequence};

/// An atomic [`CursorPtr`].
pub struct AtomicCursorPtr<T> {
    ptr: AtomicPtr<T>,
}

impl<T> AtomicCursorPtr<T> {
    /// Constructs new atomic cursor given a [`CursorPtr`].
    #[inline]
    pub fn new(cursor: CursorPtr<T>) -> Self {
        let ptr = AtomicPtr::new(cursor.ptr().as_ptr());
        Self { ptr }
    }

    /// Loads a [`CursorPtr`] value.
    ///
    /// `load` takes an `Ordering` argument which describes the memory ordering
    /// of this operation. Possible values are `SeqCst`, `Acquire` and `Relaxed`.
    ///
    /// # Panics
    ///
    /// Panics if `order` is `Release` or `AcqRel`.
    #[inline]
    pub fn load(&self, order: Ordering) -> CursorPtr<T> {
        let ptr = self.ptr.load(order);
        unsafe { CursorPtr::new_unchecked(ptr) }
    }

    /// Stores a [`CursorPtr`] value.
    ///
    /// `store` takes an `Ordering` argument which describes the memory ordering
    /// of this operation. Possible values are `SeqCst`, `Release` and `Relaxed`.
    ///
    /// # Panics
    ///
    /// Panics if `order` is `Acquire` or `AcqRel`.
    #[inline]
    pub fn store(&self, cursor: CursorPtr<T>, order: Ordering) {
        self.ptr.store(cursor.ptr().as_ptr(), order);
    }

    /// Stores a [`CursorPtr`] value, returning the previous value.
    ///
    /// `swap` takes an `Ordering` argument which describes the memory ordering
    /// of this operation. All ordering modes are possible. Note that using
    /// `Acquire` makes the store part of this operation `Relaxed`, and
    /// using `Release` makes the load part `Relaxed`.
    #[inline]
    pub fn swap(&self, cursor: CursorPtr<T>, order: Ordering) -> CursorPtr<T> {
        let prev_ptr = self.ptr.swap(cursor.ptr().as_ptr(), order);
        unsafe { CursorPtr::new_unchecked(prev_ptr) }
    }

    /// Stores a [`CursorPtr`] value if the current value is the same as the current value.
    ///
    /// The return value is always the previous value. If it is equal to `current`, then the value
    /// was updated.
    ///
    /// `compare_and_swap` also takes an `Ordering` argument which describes the memory
    /// ordering of this operation. Notice that even when using `AcqRel`, the operation
    /// might fail and hence just perform an `Acquire` load, but not have `Release` semantics.
    /// Using `Acquire` makes the store part of this operation `Relaxed` if it
    /// happens, and using `Release` makes the load part `Relaxed`.
    #[inline]
    pub fn compare_and_swap(
        &self,
        current: CursorPtr<T>,
        new: CursorPtr<T>,
        order: Ordering,
    ) -> CursorPtr<T> {
        let prev_ptr = self
            .ptr
            .compare_and_swap(current.ptr().as_ptr(), new.ptr().as_ptr(), order);
        unsafe { CursorPtr::new_unchecked(prev_ptr) }
    }

    /// Stores a [`CursorPtr`] value if the current value is the same as the `current` value.
    ///
    /// The return value is a result indicating whether the new value was written and containing
    /// the previous value. On success this value is guaranteed to be equal to `current`.
    ///
    /// `compare_exchange` takes two `Ordering` arguments to describe the memory
    /// ordering of this operation. The first describes the required ordering if the
    /// operation succeeds while the second describes the required ordering when the
    /// operation fails. Using `Acquire` as success ordering makes the store part
    /// of this operation `Relaxed`, and using `Release` makes the successful load
    /// `Relaxed`. The failure ordering can only be `SeqCst`, `Acquire` or `Relaxed`
    /// and must be equivalent to or weaker than the success ordering.
    #[inline]
    pub fn compare_exchange(
        &self,
        current: CursorPtr<T>,
        new: CursorPtr<T>,
        success: Ordering,
        failure: Ordering,
    ) -> Result<CursorPtr<T>, CursorPtr<T>> {
        let result =
            self.ptr
                .compare_exchange(current.ptr().as_ptr(), new.ptr().as_ptr(), success, failure);
        unsafe {
            match result {
                Ok(success) => Ok(CursorPtr::new_unchecked(success)),
                Err(failure) => Err(CursorPtr::new_unchecked(failure)),
            }
        }
    }

    /// Stores a [`CursorPtr`] value if the current value is the same as the `current` value.
    ///
    /// Unlike `compare_exchange`, this function is allowed to spuriously fail even when the
    /// comparison succeeds, which can result in more efficient code on some platforms. The
    /// return value is a result indicating whether the new value was written and containing the
    /// previous value.
    ///
    /// `compare_exchange_weak` takes two `Ordering` arguments to describe the memory
    /// ordering of this operation. The first describes the required ordering if the
    /// operation succeeds while the second describes the required ordering when the
    /// operation fails. Using `Acquire` as success ordering makes the store part
    /// of this operation `Relaxed`, and using `Release` makes the successful load
    /// `Relaxed`. The failure ordering can only be `SeqCst`, `Acquire` or `Relaxed`
    /// and must be equivalent to or weaker than the success ordering.
    #[inline]
    pub fn compare_exchange_weak(
        &self,
        current: CursorPtr<T>,
        new: CursorPtr<T>,
        success: Ordering,
        failure: Ordering,
    ) -> Result<CursorPtr<T>, CursorPtr<T>> {
        let result =
            self.ptr
                .compare_exchange(current.ptr().as_ptr(), new.ptr().as_ptr(), success, failure);
        unsafe {
            match result {
                Ok(success) => Ok(CursorPtr::new_unchecked(success)),
                Err(failure) => Err(CursorPtr::new_unchecked(failure)),
            }
        }
    }

    /// Atomically advance the cursor given its owner.
    ///
    /// `next` takes an `Ordering` argument which describes the memory ordering
    /// of this operation. All ordering modes are possible. Note that using
    /// `Acquire` makes the store part of this operation `Relaxed`, and
    /// using `Release` makes the load part `Relaxed`.
    ///
    /// Returns `true` if the cursor was updated, `false` if the cursor is at the
    /// tail and cannot go forward any further.
    ///
    /// # Panics
    /// Panics if `cursed` does not own the cursor.
    #[inline]
    pub fn next<C>(&self, cursed: &C, order: Ordering) -> bool
    where
        C: Sequence<T, Cursor = CursorPtr<T>>,
    {
        let (load, store) = Self::load_store_order(order);
        let cursor = self.load(load);
        cursed
            .next(cursor)
            .map(|cursor| self.store(cursor, store))
            .is_some()
    }

    /// Atomically reverse the cursor given its owner.
    ///
    /// `prev` takes an `Ordering` argument which describes the memory ordering
    /// of this operation. All ordering modes are possible. Note that using
    /// `Acquire` makes the store part of this operation `Relaxed`, and
    /// using `Release` makes the load part `Relaxed`.
    ///
    /// Returns `true` if the cursor was updated, `false` if the cursor is at the
    /// head and cannot go back any further.
    ///
    /// # Panics
    /// Panics if `cursed` does not own the cursor.
    #[inline]
    pub fn prev<C>(&self, cursed: &C, order: Ordering) -> bool
    where
        C: Sequence<T, Cursor = CursorPtr<T>>,
    {
        let (load, store) = Self::load_store_order(order);
        let cursor = self.load(load);
        cursed
            .prev(cursor)
            .map(|cursor| self.store(cursor, store))
            .is_some()
    }

    /// Atomically advance the cursor given its owner.
    ///
    /// `next` takes an `Ordering` argument which describes the memory ordering
    /// of this operation. All ordering modes are possible. Note that using
    /// `Acquire` makes the store part of this operation `Relaxed`, and
    /// using `Release` makes the load part `Relaxed`.
    ///
    /// # Panics
    /// Panics if `cursed` does not own the cursor.
    #[inline]
    pub fn wrapping_next<C>(&self, cursed: &C, order: Ordering)
    where
        C: Bounded<T, Cursor = CursorPtr<T>>,
    {
        let (load, store) = Self::load_store_order(order);
        let cursor = self.load(load);
        let cursor = cursed.wrapping_next(cursor);
        self.store(cursor, store);
    }

    /// Atomically reverse the cursor given its owner.
    ///
    /// `prev` takes an `Ordering` argument which describes the memory ordering
    /// of this operation. All ordering modes are possible. Note that using
    /// `Acquire` makes the store part of this operation `Relaxed`, and
    /// using `Release` makes the load part `Relaxed`.
    ///
    /// # Panics
    /// Panics if the `cursed` does not own the cursor.
    #[inline]
    pub fn wrapping_prev<C>(&self, cursed: &C, order: Ordering)
    where
        C: Bounded<T, Cursor = CursorPtr<T>>,
    {
        let (load, store) = Self::load_store_order(order);
        let cursor = self.load(load);
        let cursor = cursed.wrapping_prev(cursor);
        self.store(cursor, store);
    }

    /// Converts the atomic cursor into the base variant.
    #[inline]
    pub fn into_cursor(self) -> CursorPtr<T> {
        unsafe { CursorPtr::new_unchecked(self.ptr.into_inner()) }
    }

    #[inline]
    fn load_store_order(order: Ordering) -> (Ordering, Ordering) {
        let load = match order {
            Ordering::AcqRel => Ordering::Acquire,
            Ordering::Release => Ordering::Relaxed,
            other => other,
        };
        let store = match order {
            Ordering::AcqRel => Ordering::Release,
            Ordering::Acquire => Ordering::Relaxed,
            other => other,
        };
        (load, store)
    }
}

impl<T: fmt::Debug> fmt::Debug for AtomicCursorPtr<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AtomicCursor({:?})", self.ptr)
    }
}

impl<T> From<AtomicCursorPtr<T>> for CursorPtr<T> {
    fn from(cursor: AtomicCursorPtr<T>) -> Self {
        cursor.into_cursor()
    }
}

impl<T> From<CursorPtr<T>> for AtomicCursorPtr<T> {
    fn from(cursor: CursorPtr<T>) -> Self {
        Self::new(cursor)
    }
}

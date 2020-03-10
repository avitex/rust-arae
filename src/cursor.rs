use core::ptr::NonNull;
use core::{cmp, fmt, mem};

#[cfg(feature = "atomic")]
pub use self::atomic::AtomicCursor;

use crate::Cursed;

/// An structure that represents a location within a [`Cursed`] structure.
///
/// A `Cursor` is created from and used with initialized its owning [`Cursed`]
/// structure, however if the structure is dropped, will point to invalid memory.
///
/// Safety is achieved via `Cursor` validating it's owned by the [`Cursed`] structure.
///
/// [`Cursed`]: trait.Cursed.html
pub struct Cursor<T> {
    ptr: NonNull<T>,
}

impl<T> Cursor<T> {
    /// Constructs a new `Cursor` given a non-null pointer.
    #[inline]
    pub fn new(ptr: NonNull<T>) -> Self {
        Self { ptr }
    }

    /// Returns a reference to the element the `Cursor` is pointing to.
    ///
    /// # Example
    /// ```rust
    /// use arae::{CurVec, Cursed, Bounded};
    ///
    /// let mut vec: CurVec<_> = vec![0].into();
    ///
    /// let cursor = vec.head();
    ///
    /// assert_eq!(*cursor.get(&vec), 0);
    /// ```
    ///
    /// # Panics
    /// Panics if `cursed` does not own self.
    #[inline]
    pub fn get<C>(self, cursed: &C) -> &T
    where
        C: Cursed<T>,
    {
        assert!(cursed.is_owner(self));
        unsafe { &*self.ptr.as_ptr() }
    }

    /// Returns a mutable reference to the element the `Cursor` is pointing to.
    ///
    /// # Example
    /// ```rust
    /// use arae::{CurVec, Bounded};
    ///
    /// let mut vec: CurVec<_> = vec![0].into();
    ///
    /// let cursor = vec.head();
    ///
    /// *cursor.get_mut(&mut vec) = 1;
    ///
    /// assert_eq!(*cursor.get(&vec), 1);
    /// ```
    ///
    /// # Panics
    /// Panics if `cursed` does not own self.
    #[inline]
    pub fn get_mut<C>(self, cursed: &mut C) -> &mut T
    where
        C: Cursed<T>,
    {
        assert!(cursed.is_owner(self));
        unsafe { &mut *self.ptr.as_ptr() }
    }

    /// Constructs a new `Cursor` given a unchecked pointer.
    ///
    /// # Safety
    /// Must not be null, see `NonNull::new_unchecked` safety notes.
    #[inline]
    pub unsafe fn new_unchecked(ptr: *mut T) -> Self {
        Self::new(NonNull::new_unchecked(ptr))
    }

    /// Returns the `Cursor`'s underlying pointer.
    #[inline]
    pub fn ptr(self) -> NonNull<T> {
        self.ptr
    }

    /// Converts the cursor into an atomic variant.
    #[cfg(feature = "atomic")]
    #[inline]
    pub fn into_atomic(self) -> AtomicCursor<T> {
        AtomicCursor::<T>::new(self)
    }

    #[inline]
    pub(crate) unsafe fn unchecked_add(self, offset: usize) -> Self {
        let offset_ptr = self.ptr.as_ptr().add(offset);
        Self::new_unchecked(offset_ptr)
    }

    #[inline]
    pub(crate) unsafe fn unchecked_sub(self, offset: usize) -> Self {
        let offset_ptr = self.ptr.as_ptr().sub(offset);
        Self::new_unchecked(offset_ptr)
    }

    #[inline]
    pub(crate) fn offset_from(self, other: Self) -> usize {
        // TODO: use `offset_from` when stabilized
        if self == other {
            0
        } else {
            let left = self.ptr.as_ptr() as usize;
            let right = other.ptr.as_ptr() as usize;
            (left - right) / mem::size_of::<T>()
        }
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

mod atomic {
    use core::fmt;
    use core::marker::PhantomData;

    use crate::atomic::{AtomicPtr, Ordering};
    use crate::{Bounded, Cursed, CursedExt, Cursor};

    /// An atomic wrapper around a [`Cursor`].
    ///
    /// [`Cursor`]: struct.Cursor.html
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

        /// Loads a `Cursor` value.
        ///
        /// `load` takes an `Ordering` argument which describes the memory ordering
        /// of this operation. Possible values are `SeqCst`, `Acquire` and `Relaxed`.
        ///
        /// # Panics
        ///
        /// Panics if `order` is `Release` or `AcqRel`.
        #[inline]
        pub fn load(&self, order: Ordering) -> Cursor<T> {
            let ptr = self.ptr.load(order);
            unsafe { Cursor::new_unchecked(ptr) }
        }

        /// Stores a `Cursor` value.
        ///
        /// `store` takes an `Ordering` argument which describes the memory ordering
        /// of this operation. Possible values are `SeqCst`, `Release` and `Relaxed`.
        ///
        /// # Panics
        ///
        /// Panics if `order` is `Acquire` or `AcqRel`.
        #[inline]
        pub fn store(&self, cursor: Cursor<T>, order: Ordering) {
            self.ptr.store(cursor.ptr().as_ptr(), order);
        }

        /// Stores a `Cursor` value, returning the previous value.
        ///
        /// `swap` takes an `Ordering` argument which describes the memory ordering
        /// of this operation. All ordering modes are possible. Note that using
        /// `Acquire` makes the store part of this operation `Relaxed`, and
        /// using `Release` makes the load part `Relaxed`.
        #[inline]
        pub fn swap(&self, cursor: Cursor<T>, order: Ordering) -> Cursor<T> {
            let prev_ptr = self.ptr.swap(cursor.ptr().as_ptr(), order);
            unsafe { Cursor::new_unchecked(prev_ptr) }
        }

        /// Stores a `Cursor` value if the current value is the same as the current value.
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
            current: Cursor<T>,
            new: Cursor<T>,
            order: Ordering,
        ) -> Cursor<T> {
            let prev_ptr =
                self.ptr
                    .compare_and_swap(current.ptr().as_ptr(), new.ptr().as_ptr(), order);
            unsafe { Cursor::new_unchecked(prev_ptr) }
        }

        /// Stores a `Cursor` value if the current value is the same as the `current` value.
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
            current: Cursor<T>,
            new: Cursor<T>,
            success: Ordering,
            failure: Ordering,
        ) -> Result<Cursor<T>, Cursor<T>> {
            let result = self.ptr.compare_exchange(
                current.ptr().as_ptr(),
                new.ptr().as_ptr(),
                success,
                failure,
            );
            unsafe {
                match result {
                    Ok(success) => Ok(Cursor::new_unchecked(success)),
                    Err(failure) => Err(Cursor::new_unchecked(failure)),
                }
            }
        }

        /// Stores a `Cursor` value if the current value is the same as the `current` value.
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
            current: Cursor<T>,
            new: Cursor<T>,
            success: Ordering,
            failure: Ordering,
        ) -> Result<Cursor<T>, Cursor<T>> {
            let result = self.ptr.compare_exchange(
                current.ptr().as_ptr(),
                new.ptr().as_ptr(),
                success,
                failure,
            );
            unsafe {
                match result {
                    Ok(success) => Ok(Cursor::new_unchecked(success)),
                    Err(failure) => Err(Cursor::new_unchecked(failure)),
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
            C: Cursed<T>,
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
            C: Cursed<T>,
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
            C: Bounded<T>,
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
            C: Bounded<T>,
        {
            let (load, store) = Self::load_store_order(order);
            let cursor = self.load(load);
            let cursor = cursed.wrapping_prev(cursor);
            self.store(cursor, store);
        }

        /// Converts the atomic cursor into the base variant.
        #[inline]
        pub fn into_cursor(self) -> Cursor<T> {
            unsafe { Cursor::new_unchecked(self.ptr.into_inner()) }
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

    impl<T: fmt::Debug> fmt::Debug for AtomicCursor<T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "AtomicCursor({:?})", self.ptr)
        }
    }

    impl<T> From<AtomicCursor<T>> for Cursor<T> {
        fn from(cursor: AtomicCursor<T>) -> Self {
            cursor.into_cursor()
        }
    }

    impl<T> From<Cursor<T>> for AtomicCursor<T> {
        fn from(cursor: Cursor<T>) -> Self {
            cursor.into_atomic()
        }
    }
}

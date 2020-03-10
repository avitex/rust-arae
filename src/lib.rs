#![no_std]
#![deny(
    warnings,
    missing_docs,
    missing_debug_implementations,
    rust_2018_idioms
)]

//! `arae` provides `Cursed`, a trait for types that provide the ability to access
//! their elements given a `Cursor`.
//!
//! ## Example
//! ```rust
//! use arae::{CurVec, CursedExt, Bounded};
//!
//! // Create a new `CurVec` of length 10 with the elements
//! // initialized via `Default::default`.
//! let mut vec = CurVec::new_with_default(10);
//!
//! // Create two cursors pointing the the head of the vec.
//! let write_cursor = vec.head();
//! let read_cursor = vec.head();
//!
//! *vec.get_mut(write_cursor) = 1;
//!
//! assert_eq!(*vec.get(read_cursor), 1);
//! ```

extern crate alloc;

mod cursor;
/// Iterators for [`Cursed`](trait.Cursed.html) types.
pub mod iter;
mod vec;

#[cfg(feature = "atomic")]
pub use self::cursor::AtomicCursor;
pub use self::cursor::Cursor;
pub use self::vec::CurVec;

use self::iter::{Iter, WrappingIter};

/// `Cursed` types provide the ability to access their elements via [`Cursor`]s.
///
/// [`Cursor`]: struct.Cursor.html
pub trait Cursed<T> {
    /// Returns `true` if the [`Cursor`] is owned by self, `false` if not.
    ///
    /// This check determines whether or not a [`Cursor`] is pointing to valid
    /// memory, owned by `self` at the time of calling. It does not guarantee
    /// the owner will be around after the call, so a lot of care must still
    /// be taken when dereferencing the [`Cursor`].
    ///
    /// [`Cursor`]: struct.Cursor.html
    fn is_owner(&self, cursor: Cursor<T>) -> bool;
}

/// `Sequence` types are [`Cursed`] types that provide the ability to move forwards
/// and backwards through their elements.
///
/// [`Cursed`]: trait.Cursed.html
/// [`Sequence`]: trait.Sequence.html
pub trait Sequence<T>: Cursed<T> {
    /// Given a [`Cursor`], return its next element step.
    ///
    /// `None` is returned if the cursor provided cannot advance any further.
    ///
    /// [`Cursor`]: struct.Cursor.html
    fn next(&self, cursor: Cursor<T>) -> Option<Cursor<T>>;

    /// Given a [`Cursor`], return its previous element step.
    ///
    /// `None` is returned if the cursor provided cannot reverse any further.
    ///
    /// [`Cursor`]: struct.Cursor.html
    fn prev(&self, cursor: Cursor<T>) -> Option<Cursor<T>>;

    /// Given a [`Cursor`], return the bounds of the remaining steps.
    ///
    /// Specifically, `remaining()` returns a tuple where the first element is
    /// the lower bound, and the second element is the upper bound, as a known
    /// lower and optional upper bound.
    ///
    /// # Implementation notes
    ///
    /// As with `Iterator::size_hint()`, `remaining()` is primarily intended to
    /// be used for optimizations such as reserving space for the elements of the
    /// iterator, but must not be trusted to e.g., omit bounds checks in unsafe code.
    /// An incorrect implementation of `remaining()` should not lead to memory
    /// safety violations.
    ///
    /// [`Cursor`]: struct.Cursor.html
    fn remaining(&self, cursor: Cursor<T>) -> (usize, Option<usize>);
}

/// `Bounded` types are [`Cursed`] [`Sequence`]s that know their `head` and `tail` locations.
///
/// [`Cursed`]: trait.Cursed.html
/// [`Sequence`]: trait.Sequence.html
#[allow(clippy::len_without_is_empty)]
pub trait Bounded<T>: Sequence<T> {
    /// Returns the number of items within the sequence.
    fn len(&self) -> usize;

    /// Returns a [`Cursor`] pointing to the head of the sequence.
    ///
    /// [`Cursor`]: struct.Cursor.html
    fn head(&self) -> Cursor<T>;

    /// Returns a [`Cursor`] pointing to the tail of the sequence.
    ///
    /// [`Cursor`]: struct.Cursor.html
    fn tail(&self) -> Cursor<T>;

    /// Returns `Some(`[`Cursor`]`)` at the given offset from the head of the sequence,
    /// `None` if the offset is out of bounds.
    ///
    /// [`Cursor`]: struct.Cursor.html
    fn at(&self, offset: usize) -> Option<Cursor<T>>;
}

/// `Contiguous` types are [`Bounded`] [`Sequence`]s that guarantee elements
/// reside next to each other in memory (ie. `[T]`).
///
/// This trait is `unsafe` as dependencies may implement unsafe behaviour with
/// this guarantee.
///
/// # Safety
/// Implementers must ensure all elements reside next to each other in memory.
///
/// [`Bounded`]: trait.Bounded.html
/// [`Sequence`]: trait.Sequence.html
pub unsafe trait Contiguous<T>: Bounded<T> {}

/// Extended functionality for implementations of [`Cursed`].
///
/// [`Cursed`]: trait.Cursed.html
pub trait CursedExt<T>: Cursed<T> + Sized {
    /// Returns a reference to the element at the given [`Cursor`].
    ///
    /// # Example
    /// ```rust
    /// use arae::{CurVec, CursedExt, Bounded};
    ///
    /// let mut vec: CurVec<_> = vec![0].into();
    ///
    /// assert_eq!(*vec.get(vec.head()), 0);
    /// ```
    ///
    /// # Panics
    /// Panics if `self` does not own the [`Cursor`].
    ///
    /// [`Cursor`]: struct.Cursor.html
    #[inline]
    fn get(&self, cursor: Cursor<T>) -> &T {
        cursor.get(self)
    }

    /// Returns a mutable reference to the element at the given [`Cursor`].
    ///
    /// # Example
    /// ```rust
    /// use arae::{CurVec, CursedExt, Bounded};
    ///
    /// let mut vec: CurVec<_> = vec![0].into();
    ///
    /// *vec.get_mut(vec.head()) = 1;
    ///
    /// assert_eq!(*vec.get(vec.head()), 1);
    /// ```
    ///
    /// # Panics
    /// Panics if `self` does not own the [`Cursor`].
    ///
    /// [`Cursor`]: struct.Cursor.html
    #[inline]
    fn get_mut(&mut self, cursor: Cursor<T>) -> &mut T {
        cursor.get_mut(self)
    }

    /// Returns `true` if the [`Cursor`] points at the first element, `false` if not.
    ///
    /// [`Cursor`]: struct.Cursor.html
    #[inline]
    fn is_head(&self, cursor: Cursor<T>) -> bool
    where
        Self: Bounded<T>,
    {
        cursor == self.head()
    }

    /// Returns `true` if the [`Cursor`] points at the last element, `false` if not.
    ///
    /// [`Cursor`]: struct.Cursor.html
    #[inline]
    fn is_tail(&self, cursor: Cursor<T>) -> bool
    where
        Self: Bounded<T>,
    {
        cursor == self.tail()
    }

    /// Returns the element offset at the given [`Cursor`].
    ///
    /// # Panics
    /// Panics if `self` does not own the [`Cursor`].
    ///
    /// [`Cursor`]: struct.Cursor.html
    fn offset(&self, cursor: Cursor<T>) -> usize
    where
        Self: Bounded<T>,
    {
        assert!(self.is_owner(cursor));
        cursor.offset_from(self.head())
    }

    /// Given a [`Cursor`], return its next element step.
    ///
    /// If the [`Cursor`] provided points to the end of the structure,
    /// the [`Cursor`] returned will wrap and point to the start.
    ///
    /// # Example
    /// ```rust
    /// use arae::{CurVec, CursedExt, Bounded};
    ///
    /// let vec: CurVec<_> = vec![1, 2, 3].into();
    ///
    /// let cursor = vec.wrapping_next(vec.tail());
    ///
    /// assert_eq!(*vec.get(cursor), 1);
    /// ```
    ///
    /// # Panics
    /// Panics if `self` does not own the [`Cursor`].
    ///
    /// [`Cursor`]: struct.Cursor.html
    #[inline]
    fn wrapping_next(&self, cursor: Cursor<T>) -> Cursor<T>
    where
        Self: Bounded<T>,
    {
        if cursor == self.tail() {
            self.head()
        } else {
            match self.next(cursor) {
                Some(next_cursor) => next_cursor,
                None => unreachable!(),
            }
        }
    }

    /// Given a [`Cursor`], return its previous element step.
    ///
    /// If the [`Cursor`] provided points to the `head` of the structure,
    /// the [`Cursor`] returned will wrap and point to the `tail`.
    ///
    /// # Example
    /// ```rust
    /// use arae::{CurVec, CursedExt, Bounded};
    ///
    /// let vec: CurVec<_> = vec![1, 2, 3].into();
    ///
    /// let cursor = vec.wrapping_prev(vec.head());
    ///
    /// assert_eq!(*vec.get(cursor), 3);
    /// ```
    ///
    /// # Panics
    /// Panics if `self` does not own the [`Cursor`].
    ///
    /// [`Cursor`]: struct.Cursor.html
    #[inline]
    fn wrapping_prev(&self, cursor: Cursor<T>) -> Cursor<T>
    where
        Self: Bounded<T>,
    {
        if cursor == self.head() {
            self.tail()
        } else {
            match self.prev(cursor) {
                Some(prev_cursor) => prev_cursor,
                None => unreachable!(),
            }
        }
    }

    /// Returns a `Iterator<Item = (&T, Cursor<T>)>` that starts at the `head`.
    ///
    /// # Example
    /// ```rust
    /// use arae::{CurVec, CursedExt};
    ///
    /// let vec: CurVec<_> = vec![1, 2].into();
    ///
    /// for (elem, cursor) in vec.iter() {
    ///     println!("elem {} at {:?}:", elem, cursor);
    /// }
    /// ```
    #[inline]
    fn iter(&self) -> Iter<'_, Self, T>
    where
        Self: Bounded<T>,
    {
        self.iter_at(self.head())
    }

    /// Returns a `Iterator<Item = (&T, Cursor<T>)>` that starts at the given [`Cursor`].
    ///
    /// # Example
    /// ```rust
    /// use arae::{CurVec, CursedExt, Bounded};
    ///
    /// let vec: CurVec<_> = vec![1, 2].into();
    ///
    /// for (elem, cursor) in vec.iter_at(vec.head()) {
    ///     println!("elem {} at {:?}:", elem, cursor);
    /// }
    /// ```
    ///
    /// [`Cursor`]: struct.Cursor.html
    fn iter_at(&self, cursor: Cursor<T>) -> Iter<'_, Self, T>
    where
        Self: Sequence<T>,
    {
        Iter::new(self, cursor)
    }

    /// Returns a wrapping `Iterator<Item = (&T, Cursor<T>)>` that starts at
    /// the `head`.
    ///
    /// This iterator is never ending and will wrap from the `tail` to the
    /// `head` and vice-versa when iterating in the opposite direction.
    ///
    /// # Example
    /// ```rust
    /// use arae::{CurVec, CursedExt};
    ///
    /// let vec: CurVec<_> = vec![1, 2].into();
    ///
    /// for (elem, cursor) in vec.wrapping_iter() {
    ///     println!("elem: {}", elem);
    ///     if vec.is_tail(cursor) {
    ///         break;
    ///     }
    /// }
    /// ```
    #[inline]
    fn wrapping_iter(&self) -> WrappingIter<'_, Self, T>
    where
        Self: Bounded<T>,
    {
        self.wrapping_iter_at(self.head())
    }

    /// Returns a wrapping `Iterator<Item = (&T, Cursor<T>)>` that starts at
    /// the given [`Cursor`].
    ///
    /// This iterator is never ending and will wrap from the `tail` to the
    /// `head` and vice-versa when iterating in the opposite direction.
    ///
    /// # Example
    /// ```rust
    /// use arae::{CurVec, CursedExt, Bounded};
    ///
    /// let vec: CurVec<_> = vec![1, 2].into();
    ///
    /// for (elem, cursor) in vec.wrapping_iter_at(vec.head()) {
    ///     println!("elem: {}", elem);
    ///     if vec.is_tail(cursor) {
    ///         break;
    ///     }
    /// }
    /// ```
    ///
    /// [`Cursor`]: struct.Cursor.html
    #[inline]
    fn wrapping_iter_at(&self, cursor: Cursor<T>) -> WrappingIter<'_, Self, T>
    where
        Self: Sequence<T>,
    {
        WrappingIter::new(self, cursor)
    }
}

impl<T, U> CursedExt<U> for T where T: Cursed<U> {}

#[cfg(feature = "atomic")]
mod atomic {
    #[cfg(feature = "loom")]
    pub use loom::sync::atomic::{AtomicPtr, Ordering};

    #[cfg(not(feature = "loom"))]
    pub use core::sync::atomic::{AtomicPtr, Ordering};
}

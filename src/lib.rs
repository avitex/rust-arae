// #![no_std]
// #![doc(html_root_url = "https://docs.rs/arae/0.2.0")]
// #![deny(
//     warnings,
//     missing_docs,
//     missing_debug_implementations,
//     intra_doc_link_resolution_failure,
//     rust_2018_idioms,
//     unreachable_pub
// )]

//! `arae` provides [`Cursed`], a trait for types that provide the ability to access
//! their elements given a [`Cursor`].
//!
//! # Example
//! ```rust
//! use arae::{CurVec, CursedExt, Bounded};
//!
//! // Create a new `CurVec` of length 10 with the elements
//! // initialized via `Default::default`.
//! let mut vec = CurVec::new_with_default(10);
//!
//! // Create two cursors pointing the the head of the vec.
//! let head_cursor = vec.head().unwrap();
//! let write_cursor = head_cursor;
//! let read_cursor = head_cursor;
//!
//! *vec.get_mut(write_cursor) = 1;
//!
//! assert_eq!(*vec.get(read_cursor), 1);
//! ```

extern crate alloc;

#[cfg(feature = "atomic")]
mod atomic;
#[cfg(all(feature = "atomic", feature = "untested"))]
pub mod chain;
pub mod cursor;
pub mod iter;
mod unit;
mod vec;

use core::borrow::Borrow;

#[cfg(all(feature = "atomic", feature = "untested"))]
pub use self::chain::Chain;
pub use self::cursor::{Cursor, CursorExt};
pub use self::unit::Unit;
pub use self::vec::CurVec;

use self::iter::{Iter, WrappingIter};

/// `Cursed` types provide the ability to access their elements via [`Cursor`]s.
///
/// # Safety
/// Implementations of this trait **must** guarantee the [`Cursor`] is pointing
/// to valid memory owned by `self` when returning `true` from [`Cursed::is_owner`],
/// and that the data referenced does not disappear while `self` is alive.
pub unsafe trait Cursed<T> {
    /// The [`Cursor`] type this [`Cursed`] type uses.
    type Cursor: Cursor<T>;

    /// Returns `true` if the [`Cursor`] is owned by `self`, `false` if not.
    ///
    /// This check determines whether or not a [`Cursor`] is pointing to valid
    /// memory, and is used when dereferencing the [`Cursor`].
    fn is_owner(&self, cursor: &Self::Cursor) -> bool;
}

/// `Sequence` types are [`Cursed`] types that provide the ability to move forwards
/// and backwards through their elements.
pub trait Sequence<T>: Cursed<T> {
    /// Given a [`Cursor`], return its next element step.
    ///
    /// `None` is returned if the cursor provided cannot advance any further.
    fn next(&self, cursor: Self::Cursor) -> Option<Self::Cursor>;

    /// Given a [`Cursor`], return its previous element step.
    ///
    /// `None` is returned if the cursor provided cannot reverse any further.
    fn prev(&self, cursor: Self::Cursor) -> Option<Self::Cursor>;

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
    /// # Panics
    /// Panics if `self` does not own the [`Cursor`].
    fn remaining(&self, cursor: &Self::Cursor) -> (usize, Option<usize>);
}

/// `Bounded` types are [`Cursed`] [`Sequence`]s that know their `head` and `tail` locations.
pub trait Bounded<T>: Sequence<T> {
    /// Returns the number of items within the sequence.
    fn len(&self) -> usize;

    /// Returns `true` if the sequence is empty, `false` if not.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a [`Cursor`] pointing to the head of the sequence.
    fn head(&self) -> Option<Self::Cursor>;

    /// Returns a [`Cursor`] pointing to the tail of the sequence.
    fn tail(&self) -> Option<Self::Cursor>;

    /// Returns `Some(`[`Cursor`]`)` at the given offset from the head of the sequence,
    /// `None` if the offset is out of bounds.
    fn at(&self, offset: usize) -> Option<Self::Cursor>;
}

/// `Contiguous` types are [`Bounded`] [`Sequence`]s that guarantee elements
/// reside next to each other in memory (ie. `[T]`).
///
/// This trait is `unsafe` as dependencies may implement unsafe behaviour with
/// this guarantee.
///
/// # Safety
/// Implementers must ensure all elements reside next to each other in memory.
pub unsafe trait Contiguous<T>: Bounded<T> {}

/// `Mutable` types are [`Cursed`] types that allow their elements to be
/// directly mutated, given a mutable reference to `self`.
///
/// # Safety
/// Implementers must ensure this trait is implemented only for types that can
/// be safely mutated.
pub unsafe trait Mutable<T>: Cursed<T> {}

/// Extended functionality for implementations of [`Cursed`].
pub trait CursedExt<T>: Cursed<T> + Sized {
    /// Returns a reference to the element at the given [`Cursor`].
    ///
    /// # Example
    /// ```rust
    /// use arae::{CurVec, CursedExt, Bounded};
    ///
    /// let mut vec: CurVec<_> = vec![0].into();
    ///
    /// assert_eq!(*vec.get(vec.hptr()), 0);
    /// ```
    ///
    /// # Panics
    /// Panics if `self` does not own the [`Cursor`].
    #[inline]
    fn get<U>(&self, cursor: U) -> &T
    where
        U: Borrow<Self::Cursor>,
    {
        cursor.borrow().as_ref_with(self)
    }

    /// Returns a mutable reference to the element at the given [`Cursor`].
    ///
    /// # Example
    /// ```rust
    /// use arae::{CurVec, CursedExt, Bounded};
    ///
    /// let mut vec: CurVec<_> = vec![0].into();
    ///
    /// *vec.get_mut(vec.hptr()) = 1;
    ///
    /// assert_eq!(*vec.get(vec.hptr()), 1);
    /// ```
    ///
    /// # Panics
    /// Panics if `self` does not own the [`Cursor`].
    #[inline]
    fn get_mut<U>(&mut self, cursor: U) -> &mut T
    where
        Self: Mutable<T>,
        U: Borrow<Self::Cursor>,
    {
        cursor.borrow().as_mut_with(self)
    }

    /// Returns `true` if the [`Cursor`] points at the first element, `false` if not.
    #[inline]
    fn is_head<U>(&self, cursor: U) -> bool
    where
        Self: Bounded<T>,
        U: Borrow<Self::Cursor>,
    {
        if let Some(head) = self.head() {
            cursor.borrow().as_ptr() == head.as_ptr()
        } else {
            false
        }
    }

    /// Returns `true` if the [`Cursor`] points at the last element, `false` if not.
    #[inline]
    fn is_tail<U>(&self, cursor: U) -> bool
    where
        Self: Bounded<T>,
        U: Borrow<Self::Cursor>,
    {
        if let Some(tail) = self.tail() {
            cursor.borrow().as_ptr() == tail.as_ptr()
        } else {
            false
        }
    }

    /// Returns the element offset at the given [`Cursor`].
    ///
    /// # Panics
    /// Panics if `self` does not own the [`Cursor`].
    fn offset<U>(&self, cursor: U) -> usize
    where
        Self: Contiguous<T>,
        U: Borrow<Self::Cursor>,
    {
        let head = self.head().expect("head cursor");
        let cursor = cursor.borrow();
        assert!(self.is_owner(cursor));
        cursor.as_ptr().offset_from(head.as_ptr())
    }

    /// Given a [`Cursor`], return its next element step.
    ///
    /// If the [`Cursor`] provided points to the `tail` of the structure,
    /// the [`Cursor`] returned will wrap and point to the `head`.
    ///
    /// # Example
    /// ```rust
    /// use arae::{CurVec, CursedExt, Bounded};
    ///
    /// let vec: CurVec<_> = vec![1, 2, 3].into();
    ///
    /// let cursor = vec.wrapping_next(vec.tptr());
    ///
    /// assert_eq!(*vec.get(cursor), 1);
    /// ```
    ///
    /// # Panics
    /// Panics if `self` does not own the [`Cursor`].
    #[inline]
    fn wrapping_next(&self, cursor: Self::Cursor) -> Self::Cursor
    where
        Self: Bounded<T>,
    {
        if self.is_tail(&cursor) {
            self.head().expect("head cursor")
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
    /// let cursor = vec.wrapping_prev(vec.hptr());
    ///
    /// assert_eq!(*vec.get(cursor), 3);
    /// ```
    ///
    /// # Panics
    /// Panics if `self` does not own the [`Cursor`].
    #[inline]
    fn wrapping_prev(&self, cursor: Self::Cursor) -> Self::Cursor
    where
        Self: Bounded<T>,
    {
        if self.is_head(&cursor) {
            self.tail().expect("tail cursor")
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
        Iter::new(self, self.head())
    }

    /// Returns a `Iterator<Item = (&T, Cursor<T>)>` that starts at the given [`Cursor`].
    ///
    /// # Example
    /// ```rust
    /// use arae::{CurVec, CursedExt, Bounded};
    ///
    /// let vec: CurVec<_> = vec![1, 2].into();
    ///
    /// for (elem, cursor) in vec.iter_at(vec.hptr()) {
    ///     println!("elem {} at {:?}:", elem, cursor);
    /// }
    /// ```
    #[inline]
    fn iter_at(&self, cursor: Self::Cursor) -> Iter<'_, Self, T>
    where
        Self: Sequence<T>,
    {
        Iter::new(self, Some(cursor))
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
        WrappingIter::new(self, self.head())
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
    /// for (elem, cursor) in vec.wrapping_iter_at(vec.head().unwrap()) {
    ///     println!("elem: {}", elem);
    ///     if vec.is_tail(cursor) {
    ///         break;
    ///     }
    /// }
    /// ```
    #[inline]
    fn wrapping_iter_at(&self, cursor: Self::Cursor) -> WrappingIter<'_, Self, T>
    where
        Self: Sequence<T>,
    {
        WrappingIter::new(self, Some(cursor))
    }
}

impl<T, U> CursedExt<U> for T where T: Cursed<U> {}

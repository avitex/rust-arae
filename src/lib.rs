#![no_std]
#![deny(
    warnings,
    missing_docs,
    missing_debug_implementations,
    rust_2018_idioms
)]

//! Provides the heap allocated cyclic `Ring` and associated `Cursor` structures.
//!
//! # Example
//! ```rust
//! use carousel::Ring;
//!
//! // Create a new `Ring` of length 10 with the elements
//! // initialized via `Default::default`.
//! let mut ring = Ring::new_with_default(10);
//!
//! // Create two cursors pointing the the head of the ring.
//! let write_cursor = ring.head();
//! let read_cursor = ring.head();
//!
//! *ring.get_mut(write_cursor) = 1;
//!
//! assert_eq!(*ring.get(read_cursor), 1);
//! ```

#[cfg(feature = "atomic")]
mod atomic;
mod cursor;
mod iter;

extern crate alloc;

use core::mem::{self, MaybeUninit};
use core::ptr::NonNull;
use core::{fmt, slice};

use alloc::boxed::Box;
use alloc::vec::Vec;

#[cfg(feature = "atomic")]
pub use self::atomic::AtomicCursor;
pub use self::cursor::Cursor;
pub use self::iter::Iter;

/// A `Ring` is a cyclic structure of values in contiguous memory.
///
/// Elements within a `Ring` are accessed via `Cursor`s.
pub struct Ring<T> {
    head: NonNull<T>,
    tail: NonNull<T>,
}

impl<T> Ring<T> {
    /// Construct a new `Ring` with a given length and an element
    /// initializer that cannot fail.
    pub fn new_with_init<F>(len: usize, mut init_fn: F) -> Self
    where
        F: FnMut() -> T,
    {
        match Self::try_new_with_init::<_, ()>(len, || Ok(init_fn())) {
            Ok(this) => this,
            Err(()) => unreachable!(),
        }
    }

    /// Construct a new `Ring` with a given length and an element
    /// initializer that may fail.
    pub fn try_new_with_init<F, E>(len: usize, mut init_fn: F) -> Result<Self, E>
    where
        F: FnMut() -> Result<T, E>,
    {
        // ensure we aren't trying to alloc nothing.
        // it is invalid for a ring to be empty.
        assert_ne!(len, 0);
        assert_ne!(mem::size_of::<T>(), 0);

        // allocate the memory for the ring.
        let mut vec: Vec<MaybeUninit<T>> = Vec::with_capacity(len);

        // set the vec len to the capacity,
        // we initialize the elements below.
        unsafe { vec.set_len(len) }

        // initialize the elements.
        for i in 0..len {
            match init_fn() {
                // set the elem if init_fn was successful in returning a value.
                Ok(elem_val) => vec[i] = MaybeUninit::new(elem_val),
                // if init_fn failed on the first attempt to initialize a value,
                // we just set the vec len to zero again, and let the vec scope
                // drop handle the dealloc.
                Err(err) if i == 0 => {
                    // nothing was initialized so set the len to zero.
                    unsafe { vec.set_len(0) };
                    // return the error.
                    return Err(err);
                }
                // if init_fn was unsuccessful we need to destroy the data we
                // just initialized as well as the vec and return the error.
                Err(err) => {
                    unsafe {
                        // we didn't succeed in initializing this element, but
                        // we did for `i - 1` elements, so set the vec len to that.
                        vec.set_len(i - 1);
                        // we want vec to handle deinitializing the data for us,
                        // so we transmute the vec now, removing `MaybeUninit`,
                        // which is safe in that above we set the correct len.
                        //
                        // as vec drops out of scope it will drop the data for us.
                        mem::transmute::<_, Vec<T>>(vec);
                    };
                    // return the error.
                    return Err(err);
                }
            }
        }

        // we initialized all the elements above successfully,
        // so transmute to the initialized type.
        let mut vec = unsafe { mem::transmute::<_, Vec<T>>(vec) };

        // get the raw vec parts.
        let ptr = vec.as_mut_ptr();

        // we are taking control of the data.
        mem::forget(vec);

        unsafe {
            // safe as vec will alloc and return a valid ptr.
            let ptr = NonNull::new_unchecked(ptr);

            // return the new ring.
            Ok(Self::from_raw_parts(ptr, len))
        }
    }
}

impl<T: Default> Ring<T> {
    /// Construct a new `Ring` with a given length with elements
    /// initialized via `Default::default()`.
    pub fn new_with_default(len: usize) -> Self {
        Self::new_with_init(len, T::default)
    }
}

#[allow(clippy::len_without_is_empty)]
impl<T> Ring<T> {
    /// Returns the length of the ring.
    #[inline]
    pub fn len(&self) -> usize {
        let byte_len = self.tail.as_ptr() as usize - self.head.as_ptr() as usize;
        (byte_len / mem::size_of::<T>()) + 1
    }

    /// Returns a cursor at the given offset from the head of the ring.
    ///
    /// # Panics
    /// Panics if `offset >= Ring::len()`.
    #[inline]
    pub fn at(&self, offset: usize) -> Cursor<T> {
        Cursor::new(self.head_offset_ptr(offset))
    }

    /// Returns a cursor pointing to the head of the ring.
    #[inline]
    pub fn head(&self) -> Cursor<T> {
        Cursor::new(self.head)
    }

    /// Returns a cursor pointing to the tail of the ring.
    #[inline]
    pub fn tail(&self) -> Cursor<T> {
        Cursor::new(self.tail)
    }

    /// Returns a reference to the element at the given cursor in the ring.
    ///
    /// # Example
    /// ```rust
    /// use carousel::Ring;
    ///
    /// let ring = Ring::<u8>::new_with_default(1);
    ///
    /// assert_eq!(*ring.get(ring.head()), 0);
    /// ```
    ///
    /// # Panics
    /// Panics if the ring does not own the cursor.
    #[inline]
    pub fn get(&self, cursor: Cursor<T>) -> &T {
        self.assert_in_bounds(cursor);
        unsafe { &*cursor.ptr().as_ptr() }
    }

    /// Returns a mutable reference to the element at the given cursor in the ring.
    ///
    /// # Example
    /// ```rust
    /// use carousel::Ring;
    ///
    /// let mut ring = Ring::<u8>::new_with_default(1);
    ///
    /// *ring.get_mut(ring.head()) = 1;
    ///
    /// assert_eq!(*ring.get(ring.head()), 1);
    /// ```
    ///
    /// # Panics
    /// Panics if the ring does not own the cursor.
    #[inline]
    pub fn get_mut(&mut self, cursor: Cursor<T>) -> &mut T {
        self.assert_in_bounds(cursor);
        unsafe { &mut *cursor.ptr().as_ptr() }
    }

    /// Given a cursor, return its next element step through the ring.
    ///
    /// If the cursor provided points to the tail, the cursor returned
    /// will wrap and point to the head of the ring.
    ///
    /// # Example
    /// ```rust
    /// use carousel::Ring;
    ///
    /// let ring: Ring<_> = vec![1, 2, 3].into();
    ///
    /// let cursor = ring.next(ring.tail());
    ///
    /// assert_eq!(*ring.get(cursor), 1);
    /// ```
    ///
    /// # Panics
    /// Panics if the ring does not own the cursor.
    #[inline]
    // NOTE: we assume the cursor given to us is valid and
    // check it after our advance operation (see sanity check).
    pub fn next(&self, cursor: Cursor<T>) -> Cursor<T> {
        // get the current cursor ptr.
        let cursor_ptr = cursor.ptr();

        // wrap the cursor ptr if currently at the ring tail.
        let next_cursor = if cursor_ptr == self.tail {
            Cursor::new(self.head)
        } else {
            unsafe {
                let ptr = cursor_ptr.as_ptr().add(1);
                Cursor::new_unchecked(ptr)
            }
        };

        // sanity check.
        self.assert_in_bounds(next_cursor);

        // return the advanced cursor.
        next_cursor
    }

    /// Given a cursor, return its previous element step through the ring.
    ///
    /// If the cursor provided points to the head, the cursor returned
    /// will wrap and point to the tail of the ring.
    ///
    /// # Example
    /// ```rust
    /// use carousel::Ring;
    ///
    /// let ring: Ring<_> = vec![1, 2, 3].into();
    ///
    /// let cursor = ring.prev(ring.head());
    ///
    /// assert_eq!(*ring.get(cursor), 3);
    /// ```
    ///
    /// # Panics
    /// Panics if the ring does not own the cursor.
    #[inline]
    // NOTE: we assume the cursor given to us is valid and
    // check it after our advance operation (see sanity check).
    pub fn prev(&self, cursor: Cursor<T>) -> Cursor<T> {
        // get the current cursor ptr.
        let cursor_ptr = cursor.ptr();

        // wrap the cursor ptr if currently at the ring head.
        let prev_cursor = if cursor_ptr == self.head {
            Cursor::new(self.tail)
        } else {
            unsafe {
                let ptr = cursor_ptr.as_ptr().sub(1);
                Cursor::new_unchecked(ptr)
            }
        };

        // sanity check.
        self.assert_in_bounds(prev_cursor);

        // return the reversed cursor.
        prev_cursor
    }

    /// Returns the element offset at the given cursor in the ring.
    ///
    /// # Panics
    /// Panics if the ring does not own the cursor.
    #[inline]
    pub fn offset(&self, cursor: Cursor<T>) -> usize {
        self.assert_in_bounds(cursor);
        // calculate the byte offset.
        // TODO: use `offset_from` when stable.
        let byte_offset = cursor.ptr().as_ptr() as usize - self.head.as_ptr() as usize;
        // calculate the element offset and return.
        byte_offset / mem::size_of::<T>()
    }

    /// Returns `true` if the cursor points to the first element in the ring,
    /// `false` if not.
    #[inline]
    pub fn is_head(&self, cursor: Cursor<T>) -> bool {
        cursor.ptr() == self.head
    }

    /// Returns `true` if the cursor points to the last element in the ring,
    /// `false` if not.
    #[inline]
    pub fn is_tail(&self, cursor: Cursor<T>) -> bool {
        cursor.ptr() == self.tail
    }

    /// Returns `true` if the cursor is owned by the ring, `false` if not.
    ///
    /// Ownership is determined by checking whether the cursor pointer is
    /// equal to, or between the head pointer and the tail pointer.
    #[inline]
    pub fn is_owner(&self, cursor: Cursor<T>) -> bool {
        (self.head..=self.tail).contains(&cursor.ptr())
    }

    /// Returns a never ending element iterator that starts at
    /// the head of the ring.
    ///
    /// # Example
    /// ```rust
    /// use carousel::Ring;
    ///
    /// let ring: Ring<_> = vec![1, 2].into();
    ///
    /// for (elem, cursor) in ring.iter() {
    ///     println!("elem: {}", elem);
    ///     if ring.is_tail(cursor) {
    ///         break;
    ///     }
    /// }
    /// ```
    #[inline]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter::new(self, self.head())
    }

    /// Returns a never ending element iterator that starts at
    /// a given offset of the ring.
    ///
    /// # Example
    /// ```rust
    /// use carousel::Ring;
    ///
    /// let ring: Ring<_> = vec![1, 2].into();
    ///
    /// for (elem, cursor) in ring.iter_at(1) {
    ///     println!("elem: {}", elem);
    ///     if ring.is_tail(cursor) {
    ///         break;
    ///     }
    /// }
    /// ```
    ///
    /// # Panics
    /// Panics if `offset > Ring::len()`.
    #[inline]
    pub fn iter_at(&self, offset: usize) -> Iter<'_, T> {
        Iter::new(self, self.at(offset))
    }

    ///////////////////////////////////////////////////////////////////////////
    // private

    /// Construct a new `Ring` from its raw parts.
    ///
    /// # Panics
    /// Panics if `len` is zero or greater than `isize::max_value()`.
    ///
    /// # Safety
    /// Has the same safety constraints and notes as [`slice::from_raw_parts`].
    ///
    /// [`slice::from_raw_parts`]: https://doc.rust-lang.org/std/slice/fn.from_raw_parts.html
    #[inline]
    unsafe fn from_raw_parts(head_ptr: NonNull<T>, len: usize) -> Self {
        assert_ne!(len, 0);
        assert!(len <= isize::max_value() as usize);
        let head = head_ptr;
        let tail = NonNull::new_unchecked(head.as_ptr().add(len - 1));
        Self { head, tail }
    }

    #[inline]
    fn assert_in_bounds(&self, cursor: Cursor<T>) {
        assert!(self.is_owner(cursor));
    }

    #[inline]
    fn head_offset_ptr(&self, offset: usize) -> NonNull<T> {
        assert!(offset < self.len());
        unsafe {
            let offset_ptr = self.head.as_ptr().add(offset);
            NonNull::new_unchecked(offset_ptr)
        }
    }

    #[inline]
    fn as_slice(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.head.as_ptr() as _, self.len()) }
    }

    #[inline]
    fn as_slice_mut(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.head.as_ptr(), self.len()) }
    }
}

impl<T: Clone> Clone for Ring<T> {
    fn clone(&self) -> Self {
        self.as_slice().to_vec().into()
    }
}

impl<T> Drop for Ring<T> {
    fn drop(&mut self) {
        unsafe { mem::drop(Box::from_raw(self.as_slice_mut())) }
    }
}

impl<L, R> PartialEq<Ring<R>> for Ring<L>
where
    L: PartialEq<R>,
{
    fn eq(&self, other: &Ring<R>) -> bool {
        if self.len() != other.len() {
            return false;
        }
        let zipped_elems = self.iter().zip(other.iter());
        for ((left_elem, cur), (right_elem, _)) in zipped_elems {
            if left_elem != right_elem {
                return false;
            }
            if self.is_head(cur) {
                break;
            }
        }
        true
    }
}

impl<T> From<Vec<T>> for Ring<T> {
    fn from(value: Vec<T>) -> Self {
        value.into_boxed_slice().into()
    }
}

impl<T> From<Box<[T]>> for Ring<T> {
    fn from(value: Box<[T]>) -> Self {
        // get the box slice ptr as non-null.
        let ptr = NonNull::new(value.as_ptr() as _).expect("non-null box ptr");
        // get the box slice len.
        let len = value.len();
        // we are taking control of the data,
        // prevent the data being dropped.
        mem::forget(value);
        // construct the ring from the raw parts.
        unsafe { Self::from_raw_parts(ptr, len) }
    }
}

impl<T> AsRef<[T]> for Ring<T> {
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T> AsMut<[T]> for Ring<T> {
    fn as_mut(&mut self) -> &mut [T] {
        self.as_slice_mut()
    }
}

impl<T: fmt::Debug> fmt::Debug for Ring<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Ring({:?})", self.as_slice())
    }
}

#[cfg(test)]
mod tests {
    use super::Ring;
    use alloc::vec;

    #[test]
    fn test_new_ring_with_default() {
        Ring::<u8>::new_with_default(1);
    }

    #[test]
    #[should_panic]
    fn test_new_ring_empty() {
        Ring::<u8>::new_with_default(0);
    }

    #[test]
    fn test_ring_get() {
        let ring: Ring<_> = vec![1, 2, 3].into();
        assert_eq!(ring.len(), 3);

        let cursor = ring.head();

        assert_eq!(*ring.get(cursor), 1);

        let cursor = ring.next(cursor);
        assert_eq!(*ring.get(cursor), 2);

        let cursor = ring.next(cursor);
        assert_eq!(*ring.get(cursor), 3);

        let cursor = ring.next(cursor);
        assert_eq!(*ring.get(cursor), 1);
    }

    #[test]
    fn test_ring_clone() {
        let ring: Ring<_> = vec![1, 2, 3].into();
        let ring_clone = ring.clone();
        assert_eq!(ring, ring_clone);
    }

    #[test]
    fn test_ring_get_mut() {
        let mut ring: Ring<_> = vec![1, 2, 3].into();
        *ring.get_mut(ring.head()) = 2;
        assert_eq!(ring, vec![2, 2, 3].into());
    }

    #[test]
    fn test_ring_iter_at_zero() {
        let ring: Ring<_> = vec![1, 2].into();
        let mut ring_iter = ring.iter_at(0);

        let (_, cursor) = ring_iter.next().unwrap();
        assert_eq!(*ring.get(cursor), 1);
        assert_eq!(ring.offset(cursor), 0);

        let (_, cursor) = ring_iter.next().unwrap();
        assert_eq!(*ring.get(cursor), 2);
        assert_eq!(ring.offset(cursor), 1);
        assert!(ring.is_tail(cursor));

        let (_, cursor) = ring_iter.next().unwrap();
        assert_eq!(ring.offset(cursor), 0);
    }

    #[test]
    fn test_ring_iter_at() {
        let ring: Ring<_> = vec![1, 2].into();
        let mut ring_iter = ring.iter_at(1);

        let (_, cursor) = ring_iter.next().unwrap();
        assert_eq!(*ring.get(cursor), 2);
        assert_eq!(ring.offset(cursor), 1);
        assert!(ring.is_tail(cursor));

        let (_, cursor) = ring_iter.next().unwrap();
        assert_eq!(*ring.get(cursor), 1);
        assert_eq!(ring.offset(cursor), 0);
    }

    #[test]
    #[should_panic]
    fn test_ring_iter_at_invalid() {
        let ring: Ring<_> = vec![1].into();
        ring.iter_at(1);
    }

    #[test]
    fn test_ring_iter_at_single_elem() {
        let ring: Ring<_> = vec![1].into();
        let mut ring_iter = ring.iter();

        let (_, cursor) = ring_iter.next().unwrap();
        assert_eq!(*ring.get(cursor), 1);
        assert!(ring.is_head(cursor));
        assert!(ring.is_tail(cursor));

        let (_, next_cursor) = ring_iter.next().unwrap();
        assert_eq!(cursor, next_cursor);
    }
}

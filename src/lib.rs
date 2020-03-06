#![no_std]
#![deny(
    warnings,
    missing_docs,
    missing_debug_implementations,
    rust_2018_idioms
)]

//! Provides the heap allocated circular `Ring` and associated `Cursor` structures.
//!
//! # Example
//! ```rust
//! use carousel::Ring;
//!
//! // Create a new `Ring` with the elements initialized via `Default::default`.
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
use core::slice;

use alloc::boxed::Box;
use alloc::vec::Vec;

#[cfg(feature = "atomic")]
pub use self::atomic::AtomicCursor;
pub use self::cursor::Cursor;
pub use self::iter::Iter;

/// A `Ring` is a circular structure of values in contiguous memory.
///
/// Elements within a `Ring` are accessed via `Cursor`s.
#[derive(Debug)]
pub struct Ring<T> {
    ptr: NonNull<T>,
    len: usize,
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
    /// Construct a new `Ring` from its raw parts.
    ///
    /// # Safety
    /// Has the same safety constraints and notes as [`slice::from_raw_parts`].
    ///
    /// [`slice::from_raw_parts`]: https://doc.rust-lang.org/std/slice/fn.from_raw_parts.html
    #[inline]
    pub unsafe fn from_raw_parts(ptr: NonNull<T>, len: usize) -> Self {
        debug_assert!(len <= isize::max_value() as usize);
        Self { ptr, len }
    }

    /// Returns the length of the ring.
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns a cursor at the given offset from the head of the ring.
    ///
    /// # Panics
    /// Panics if `offset > Ring::len()`.
    #[inline]
    pub fn at(&self, offset: usize) -> Cursor<T> {
        Cursor::new(self.elem_offset_ptr(offset))
    }

    /// Returns a cursor pointing to the head of the ring.
    #[inline]
    pub fn head(&self) -> Cursor<T> {
        Cursor::new(self.get_head_ptr())
    }

    /// Returns a cursor pointing to the tail of the ring.
    #[inline]
    pub fn tail(&self) -> Cursor<T> {
        Cursor::new(self.get_tail_ptr())
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
    /// let ring: Ring<_> = vec[1, 2, 3].into();
    ///
    /// let cursor = ring.advance(ring.head());
    ///
    /// assert_eq!(*ring.get(cursor), 2);
    /// ```
    ///
    /// # Panics
    /// Panics if the ring does not own the cursor.
    #[inline]
    // NOTE: we assume the cursor given to us is valid and
    // check it after our advance operation (see sanity check).
    pub fn advance(&self, cursor: Cursor<T>) -> Cursor<T> {
        // get the current cursor ptr.
        let cursor_ptr = cursor.ptr().as_ptr();

        // get the ring ptr bounds.
        let (head_ptr, tail_ptr) = self.get_ptr_bounds();

        // wrap the cursor ptr if currently at the ring tail.
        let next_ptr = if cursor_ptr == tail_ptr.as_ptr() {
            head_ptr
        } else {
            unsafe { NonNull::new_unchecked(cursor_ptr.add(1)) }
        };

        // construct the advanced cursor
        let next_cursor = Cursor::new(next_ptr);

        // sanity check.
        self.assert_in_bounds(next_cursor);

        // return the advanced cursor.
        next_cursor
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
        let byte_offset = cursor.ptr().as_ptr() as usize - self.ptr.as_ptr() as usize;
        // calculate the element offset and return.
        byte_offset / mem::size_of::<T>()
    }

    /// Returns `true` if the cursor points to the first element in the ring,
    /// `false` if not.
    ///
    /// # Panics
    /// Panics if the ring does not own the cursor.
    #[inline]
    pub fn is_head(&self, cursor: Cursor<T>) -> bool {
        self.offset(cursor) == 0
    }

    /// Returns `true` if the cursor points to the last element in the ring,
    /// `false` if not.
    ///
    /// # Panics
    /// Panics if the ring does not own the cursor.
    #[inline]
    pub fn is_tail(&self, cursor: Cursor<T>) -> bool {
        self.offset(cursor) == self.len - 1
    }

    /// Returns `true` if the cursor is owned by the ring, `false` if not.
    ///
    /// Ownership is determined by checking whether the cursor pointer is
    /// equal to, or between the head pointer and the tail pointer.
    #[inline]
    pub fn is_owner(&self, cursor: Cursor<T>) -> bool {
        let (head_ptr, tail_ptr) = self.get_ptr_bounds();
        cursor.ptr() >= head_ptr && cursor.ptr() <= tail_ptr
    }

    /// Returns a never ending element iterator that starts at
    /// the head of the ring.
    ///
    /// # Example
    /// ```rust
    /// use carousel::Ring;
    ///
    /// let ring = Ring::<u8>::new_with_default(1);
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
    /// let ring = Ring::<u8>::new_with_default(1);
    ///
    /// for (elem, cursor) in ring.iter_from(1) {
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
    pub fn iter_from(&self, offset: usize) -> Iter<'_, T> {
        Iter::new(self, self.at(offset))
    }

    #[inline]
    fn assert_in_bounds(&self, cursor: Cursor<T>) {
        assert!(self.is_owner(cursor));
    }

    #[inline]
    fn get_ptr_bounds(&self) -> (NonNull<T>, NonNull<T>) {
        (self.get_head_ptr(), self.get_tail_ptr())
    }

    #[inline]
    fn get_tail_ptr(&self) -> NonNull<T> {
        self.elem_offset_ptr(self.len)
    }

    #[inline]
    fn elem_offset_ptr(&self, offset: usize) -> NonNull<T> {
        assert!(offset <= self.len);
        // Vec/Box ensures nevers allocates more than isize::MAX bytes so
        // this cast is safe.
        let byte_offset = (offset * mem::size_of::<T>()) as isize;
        unsafe {
            let ptr = self.get_head_ptr().as_ptr().offset(byte_offset);
            NonNull::new_unchecked(ptr)
        }
    }

    #[inline]
    fn get_head_ptr(&self) -> NonNull<T> {
        self.ptr
    }

    #[inline]
    unsafe fn as_boxed_slice(&self) -> Box<[T]> {
        let head_ptr = self.ptr.as_ptr();
        let slice = slice::from_raw_parts_mut(head_ptr, self.len);
        Box::from_raw(slice)
    }
}

impl<T: Clone> Clone for Ring<T> {
    fn clone(&self) -> Self {
        unsafe {
            // first get the ring as a boxed slice.
            let boxed_slice = self.as_boxed_slice();

            // clone the box
            let mut boxed_slice_clone = boxed_slice.clone();

            // forget about our original boxed data.
            // we don't want this to run `drop` on us D:
            mem::forget(boxed_slice);

            // get the raw parts of the cloned data.
            let ptr = boxed_slice_clone.as_mut_ptr();
            let len = boxed_slice_clone.len();

            // now forget about the cloned box for the same
            // reason as above!
            mem::forget(boxed_slice_clone);

            // we just cloned valid data... this is tots fine.
            let ptr = NonNull::new_unchecked(ptr);

            // return the cloned ring!
            Self::from_raw_parts(ptr, len)
        }
    }
}

impl<T> Drop for Ring<T> {
    fn drop(&mut self) {
        let boxed_slice = unsafe { self.as_boxed_slice() };
        mem::drop(boxed_slice);
    }
}

impl<TL, TR> PartialEq<Ring<TR>> for Ring<TL>
where
    TL: PartialEq<TR>,
{
    fn eq(&self, other: &Ring<TR>) -> bool {
        if self.len() != other.len() {
            return false;
        }
        let zipped_elems = self.iter().zip(other.iter());
        for ((left_elem, cur), (right_elem, _)) in zipped_elems {
            if left_elem.ne(right_elem) {
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

#[cfg(test)]
mod tests {
    use super::Ring;
    use alloc::vec;

    #[test]
    fn test_new_ring() {
        Ring::<u8>::new_with_default(1);
    }

    #[test]
    #[should_panic]
    fn test_new_ring_empty() {
        Ring::<u8>::new_with_default(0);
    }

    #[test]
    fn test_ring_clone() {
        let ring = Ring::<u8>::new_with_init(1, || 66);
        let ring_clone = ring.clone();
        assert_eq!(ring, ring_clone);
    }

    #[test]
    fn test_ring_get_mut() {
        let mut ring = Ring::<u8>::new_with_default(1);

        *ring.get_mut(ring.head()) = 1;

        assert_eq!(*ring.get(ring.head()), 1);
    }

    #[test]
    fn test_ring_iter_from() {
        let ring: Ring<_> = vec![1, 2].into();
        let mut ring_iter = ring.iter_from(1);

        let (_, cursor) = ring_iter.next().unwrap();
        assert_eq!(ring.offset(cursor), 0);

        let (_, cursor) = ring_iter.next().unwrap();
        assert_eq!(ring.offset(cursor), 1);
        assert!(ring.is_tail(cursor));

        let (_, cursor) = ring_iter.next().unwrap();
        assert_eq!(ring.offset(cursor), 0);
    }

    #[test]
    fn test_ring_iter_from_single_elem() {
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

use core::mem::{self, MaybeUninit};
use core::ptr::NonNull;
use core::{fmt, slice};

use alloc::boxed::Box;
use alloc::vec::Vec;

use crate::{Bounded, Contiguous, Cursed, CursedExt, Cursor};

/// A `CurVec` is heap-allocated, non-resizable sequence of elements in
/// contiguous memory designed for efficent access via `Cursor`s.
///
/// You can access the elements of a `CurVec` the same way you would a `Vec` or
/// `Box<[T]>` however it's characteristics are different to what either provide.
///
/// A `CurVec`:
///
/// - **Cannot** be empty.
/// - **Cannot** contain elements of `mem::size_of() == 0`.
/// - **Cannot** be resized (and does not have any notion of capacity).
/// - Stores the starting element pointer (head) and end element pointer (tail)
///   unlike a `Vec` which stores the first element pointer and length.
///
/// ```rust
/// use arae::{CurVec, Cursed, CursedExt, Bounded};
///
/// // Create a new `CurVec` of length 10 with the elements
/// // initialized via `Default::default`.
/// let mut vec = CurVec::new_with_default(10);
///
/// // Create two cursors pointing the the head of the vec.
/// let write_cursor = vec.head();
/// let read_cursor = vec.head();
///
/// // Write the value `1` at the element pointed by `write_cursor`.
/// *vec.get_mut(write_cursor) = 1;
///
/// // Read the value at the element pointed by `read_cursor`.
/// assert_eq!(*vec.get(read_cursor), 1);
/// ```
pub struct CurVec<T> {
    head: NonNull<T>,
    tail: NonNull<T>,
}

#[allow(clippy::len_without_is_empty)]
impl<T> CurVec<T> {
    /// Construct a new `CurVec` with a given length and an element
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

    /// Construct a new `CurVec` with a given length and an element
    /// initializer that may fail.
    pub fn try_new_with_init<F, E>(len: usize, mut init_fn: F) -> Result<Self, E>
    where
        F: FnMut() -> Result<T, E>,
    {
        // Ensure we aren't trying to alloc nothing.
        // It is invalid for a `CurVec` to be empty.
        assert_ne!(len, 0);
        assert_ne!(mem::size_of::<T>(), 0);

        // Allocate the memory for the `CurVec`.
        let mut vec: Vec<MaybeUninit<T>> = Vec::with_capacity(len);

        // Set the vec len to the capacity.
        // Safe as we initialize the elements below.
        unsafe { vec.set_len(len) }

        // Initialize the elements.
        for i in 0..len {
            match init_fn() {
                // Set the elem if init_fn was successful in returning a value.
                Ok(elem_val) => vec[i] = MaybeUninit::new(elem_val),
                // If init_fn failed on the first attempt to initialize a value,
                // we just set the vec len to zero again, and let the vec scope
                // drop handle the dealloc.
                Err(err) if i == 0 => {
                    // Nothing was initialized so set the len to zero.
                    unsafe { vec.set_len(0) };
                    // Return the error.
                    return Err(err);
                }
                // If init_fn was unsuccessful we need to destroy the data we
                // just initialized as well as the vec and return the error.
                Err(err) => {
                    unsafe {
                        // We didn't succeed in initializing this element, but
                        // we did for `i - 1` elements, so set the vec len to that.
                        vec.set_len(i - 1);
                        // We want vec to handle deinitializing the data for us,
                        // so we transmute the vec now, removing `MaybeUninit`,
                        // which is safe in that above we set the correct len.
                        //
                        // As vec drops out of scope it will drop the data for us.
                        mem::transmute::<_, Vec<T>>(vec);
                    };
                    // Return the error.
                    return Err(err);
                }
            }
        }

        // We initialized all the elements above successfully,
        // so transmute to the initialized type.
        let mut vec = unsafe { mem::transmute::<_, Vec<T>>(vec) };

        // Get the raw vec parts.
        let ptr = vec.as_mut_ptr();

        // We are taking control of the data.
        mem::forget(vec);

        unsafe {
            // Safe as vec will alloc and return a valid ptr.
            let ptr = NonNull::new_unchecked(ptr);

            // Return the new `CurVec`.
            Ok(Self::from_raw_parts(ptr, len))
        }
    }

    /// Construct a new `CurVec` from its raw parts.
    ///
    /// # Panics
    /// Panics if `len` is zero or greater than `isize::max_value()`.
    ///
    /// # Safety
    /// Has the same safety constraints and notes as [`slice::from_raw_parts`].
    ///
    /// [`slice::from_raw_parts`]: https://doc.rust-lang.org/std/slice/fn.from_raw_parts.html
    #[inline]
    pub unsafe fn from_raw_parts(head_ptr: NonNull<T>, len: usize) -> Self {
        assert_ne!(len, 0);
        assert!(len <= isize::max_value() as usize);
        let head = head_ptr;
        let tail = NonNull::new_unchecked(head.as_ptr().add(len - 1));
        Self { head, tail }
    }

    /// Return a slice of the elements.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.head.as_ptr() as _, self.len()) }
    }

    /// Return a mutable slice of the elements.
    #[inline]
    pub fn as_slice_mut(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.head.as_ptr(), self.len()) }
    }

    /// Consume `self` into a boxed slice.
    #[inline]
    pub fn into_boxed_slice(mut self) -> Box<[T]> {
        let boxed = unsafe { Box::from_raw(self.as_slice_mut()) };
        mem::forget(self);
        boxed
    }
}

impl<T: Default> CurVec<T> {
    /// Construct a new `CurVec` with a given length with elements
    /// initialized via `Default::default()`.
    pub fn new_with_default(len: usize) -> Self {
        Self::new_with_init(len, T::default)
    }
}

impl<T> Cursed<T> for CurVec<T> {
    fn remaining(&self, cursor: Cursor<T>) -> (usize, Option<usize>) {
        let remaining = if cursor.ptr() == self.head {
            self.len()
        } else {
            self.len() - self.offset(cursor)
        };
        (remaining, Some(remaining))
    }

    #[inline]
    fn is_owner(&self, cursor: Cursor<T>) -> bool {
        (self.head..=self.tail).contains(&cursor.ptr())
    }

    #[inline]
    // NOTE: we assume the cursor given to us is valid and
    // check it after our advance operation (see sanity check).
    fn next(&self, cursor: Cursor<T>) -> Option<Cursor<T>> {
        if cursor.ptr() == self.tail {
            None
        } else {
            let next_cursor = unsafe { cursor.unchecked_add(1) };
            // Sanity check.
            assert!(self.is_owner(cursor));
            // Return the advanced cursor.
            Some(next_cursor)
        }
    }

    #[inline]
    // NOTE: we assume the cursor given to us is valid and
    // check it after our advance operation (see sanity check).
    fn prev(&self, cursor: Cursor<T>) -> Option<Cursor<T>> {
        if cursor.ptr() == self.head {
            None
        } else {
            let prev_cursor = unsafe { cursor.unchecked_sub(1) };
            // Sanity check.
            assert!(self.is_owner(cursor));
            // Return the reversed cursor.
            Some(prev_cursor)
        }
    }
}

impl<T> Bounded<T> for CurVec<T> {
    #[inline]
    fn len(&self) -> usize {
        self.tail().offset_from(self.head()) + 1
    }

    #[inline]
    fn head(&self) -> Cursor<T> {
        Cursor::new(self.head)
    }

    #[inline]
    fn tail(&self) -> Cursor<T> {
        Cursor::new(self.tail)
    }

    #[inline]
    fn at(&self, offset: usize) -> Option<Cursor<T>> {
        if offset < self.len() {
            Some(unsafe { self.head().unchecked_add(offset) })
        } else {
            None
        }
    }
}

unsafe impl<T> Contiguous<T> for CurVec<T> {}

impl<T: Clone> Clone for CurVec<T> {
    fn clone(&self) -> Self {
        self.as_slice().to_vec().into()
    }
}

impl<T> Drop for CurVec<T> {
    fn drop(&mut self) {
        unsafe { mem::drop(Box::from_raw(self.as_slice_mut())) }
    }
}

impl<L, R> PartialEq<CurVec<R>> for CurVec<L>
where
    L: PartialEq<R>,
{
    fn eq(&self, other: &CurVec<R>) -> bool {
        self.as_slice().eq(other.as_slice())
    }
}

impl<T> From<Vec<T>> for CurVec<T> {
    fn from(value: Vec<T>) -> Self {
        value.into_boxed_slice().into()
    }
}

impl<T> From<Box<[T]>> for CurVec<T> {
    fn from(value: Box<[T]>) -> Self {
        // get the box slice ptr as non-null.
        let ptr = NonNull::new(value.as_ptr() as _).expect("non-null box ptr");
        // get the box slice len.
        let len = value.len();
        // we are taking control of the data,
        // prevent the data being dropped.
        mem::forget(value);
        // construct the vec from the raw parts.
        unsafe { Self::from_raw_parts(ptr, len) }
    }
}

impl<T> AsRef<[T]> for CurVec<T> {
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T> AsMut<[T]> for CurVec<T> {
    fn as_mut(&mut self) -> &mut [T] {
        self.as_slice_mut()
    }
}

impl<T: fmt::Debug> fmt::Debug for CurVec<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CurVec({:?})", self.as_slice())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    #[test]
    fn test_new_with_default() {
        CurVec::<u8>::new_with_default(1);
    }

    #[test]
    #[should_panic]
    fn test_new_empty() {
        CurVec::<u8>::new_with_default(0);
    }

    #[test]
    fn test_get() {
        let vec: CurVec<_> = vec![1, 2, 3].into();
        assert_eq!(vec.len(), 3);

        let cursor = vec.head();

        assert_eq!(*vec.get(cursor), 1);

        let cursor = vec.next(cursor).unwrap();
        assert_eq!(*vec.get(cursor), 2);

        let cursor = vec.next(cursor).unwrap();
        assert_eq!(*vec.get(cursor), 3);

        assert_eq!(vec.next(cursor), None);
    }

    #[test]
    fn test_clone() {
        let vec: CurVec<_> = vec![1, 2, 3].into();
        let vec_clone = vec.clone();
        assert_eq!(vec, vec_clone);
    }

    #[test]
    fn test_get_mut() {
        let mut vec: CurVec<_> = vec![1, 2, 3].into();
        *vec.get_mut(vec.head()) = 2;
        assert_eq!(vec, vec![2, 2, 3].into());
    }

    #[test]
    fn test_iter_at_head() {
        let vec: CurVec<_> = vec![1, 2].into();
        let mut vec_iter = vec.iter();

        let (_, cursor) = vec_iter.next().unwrap();
        assert_eq!(*vec.get(cursor), 1);
        assert_eq!(vec.offset(cursor), 0);

        let (_, cursor) = vec_iter.next().unwrap();
        assert_eq!(*vec.get(cursor), 2);
        assert_eq!(vec.offset(cursor), 1);
        assert!(vec.is_tail(cursor));

        assert_eq!(vec_iter.next(), None);
    }

    #[test]
    fn test_iter_at() {
        let vec: CurVec<_> = vec![1, 2].into();
        let mut vec_iter = vec.iter_at(vec.at(1).unwrap());

        let (_, cursor) = vec_iter.next().unwrap();
        assert_eq!(*vec.get(cursor), 2);
        assert_eq!(vec.offset(cursor), 1);
        assert!(vec.is_tail(cursor));

        assert_eq!(vec_iter.next(), None);
    }

    #[test]
    fn test_wrapping_iter_at_head() {
        let vec: CurVec<_> = vec![1, 2].into();
        let mut vec_iter = vec.wrapping_iter();

        let (_, cursor) = vec_iter.next().unwrap();
        assert_eq!(*vec.get(cursor), 1);
        assert_eq!(vec.offset(cursor), 0);

        let (_, cursor) = vec_iter.next().unwrap();
        assert_eq!(*vec.get(cursor), 2);
        assert_eq!(vec.offset(cursor), 1);
        assert!(vec.is_tail(cursor));

        let (_, cursor) = vec_iter.next().unwrap();
        assert_eq!(vec.offset(cursor), 0);
    }

    #[test]
    fn test_wrapping_iter_iter_at() {
        let vec: CurVec<_> = vec![1, 2].into();
        let mut vec_iter = vec.wrapping_iter_at(vec.at(1).unwrap());

        let (_, cursor) = vec_iter.next().unwrap();
        assert_eq!(*vec.get(cursor), 2);
        assert_eq!(vec.offset(cursor), 1);
        assert!(vec.is_tail(cursor));

        let (_, cursor) = vec_iter.next().unwrap();
        assert_eq!(*vec.get(cursor), 1);
        assert_eq!(vec.offset(cursor), 0);
    }

    #[test]
    #[should_panic]
    fn test_iter_at_invalid() {
        let vec: CurVec<_> = vec![1].into();
        vec.iter_at(vec.at(1).unwrap());
    }

    #[test]
    fn test_vec_iter_at_single_elem() {
        let vec: CurVec<_> = vec![1].into();
        let mut vec_iter = vec.iter();

        let (_, cursor) = vec_iter.next().unwrap();
        assert_eq!(*vec.get(cursor), 1);
        assert!(vec.is_head(cursor));
        assert!(vec.is_tail(cursor));

        assert_eq!(vec_iter.next(), None);
    }
}

use core::ptr::NonNull;
use core::{cmp, fmt, mem};

use super::Cursor;

/// Wrapper around a raw pointer.
pub struct CursorPtr<T> {
    ptr: NonNull<T>,
}

impl<T> CursorPtr<T> {
    /// Constructs a new `CursorPtr` given a non-null pointer.
    #[inline]
    pub fn new(ptr: NonNull<T>) -> Self {
        Self { ptr }
    }

    /// Constructs a new `CursorPtr` given a `*mut T` pointer.
    ///
    /// # Panics
    /// Panics if the given pointer is nul..
    #[inline]
    pub fn new_checked(ptr: *mut T) -> Self {
        NonNull::new(ptr)
            .map(Self::new)
            .expect("given null ptr for cursor")
    }

    /// Constructs a new `CursorPtr` given a unchecked pointer.
    ///
    /// # Safety
    /// Must not be null, see `NonNull::new_unchecked` safety notes.
    #[inline]
    pub unsafe fn new_unchecked(ptr: *mut T) -> Self {
        Self::new(NonNull::new_unchecked(ptr))
    }

    /// Returns the `CursorPtr`'s underlying pointer.
    #[inline]
    pub fn ptr(self) -> NonNull<T> {
        self.ptr
    }

    /// Returns the `CursorPtr`'s underlying pointer as `*mut T`.
    #[inline]
    pub fn ptr_mut(self) -> *mut T {
        self.ptr.as_ptr()
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

impl<T> Clone for CursorPtr<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self::new(self.ptr())
    }
}
impl<T> Copy for CursorPtr<T> {}

impl<T> PartialEq for CursorPtr<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr
    }
}

impl<T> Eq for CursorPtr<T> {}

impl<T> PartialOrd for CursorPtr<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.ptr.partial_cmp(&other.ptr)
    }
}

impl<T> Ord for CursorPtr<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.ptr.cmp(&other.ptr)
    }
}

impl<T> fmt::Debug for CursorPtr<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CursorPtr({:?})", self.ptr)
    }
}

impl<T> From<NonNull<T>> for CursorPtr<T> {
    #[inline]
    fn from(ptr: NonNull<T>) -> Self {
        Self::new(ptr)
    }
}

impl<T> Cursor<T> for CursorPtr<T> {
    #[inline]
    fn as_ptr(&self) -> Self {
        *self
    }
}

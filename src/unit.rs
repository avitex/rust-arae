use super::cursor::CursorPtr;
use super::{Bounded, Contiguous, Cursed, Sequence};

/// A [`Cursed`] single value container.
#[derive(Debug)]
pub struct Unit<T>(pub T);

impl<T> Unit<T> {
    #[inline]
    fn value_ptr(&self) -> CursorPtr<T> {
        CursorPtr::new((&self.0).into())
    }
}

unsafe impl<T> Cursed<T> for Unit<T> {
    type Cursor = CursorPtr<T>;

    #[inline]
    fn is_owner(&self, cursor: &Self::Cursor) -> bool {
        *cursor == self.value_ptr()
    }
}

impl<T> Sequence<T> for Unit<T> {
    #[inline]
    fn next(&self, _cursor: Self::Cursor) -> Option<Self::Cursor> {
        None
    }

    #[inline]
    fn prev(&self, _cursor: Self::Cursor) -> Option<Self::Cursor> {
        None
    }

    #[inline]
    fn remaining(&self, cursor: &Self::Cursor) -> (usize, Option<usize>) {
        assert!(self.is_owner(cursor));
        (0, Some(0))
    }
}

impl<T> Bounded<T> for Unit<T> {
    fn len(&self) -> usize {
        1
    }

    fn head(&self) -> Option<Self::Cursor> {
        Some(self.value_ptr())
    }

    fn tail(&self) -> Option<Self::Cursor> {
        Some(self.value_ptr())
    }

    fn at(&self, offset: usize) -> Option<Self::Cursor> {
        if offset == 0 {
            Some(self.value_ptr())
        } else {
            None
        }
    }
}

unsafe impl<T> Contiguous<T> for Unit<T> {}

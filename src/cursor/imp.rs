use alloc::rc::Rc;
use alloc::sync::Arc;

use super::{Cursor, CursorPtr, Detached, Handle, HandleMut};

impl<T> Cursor<T> for Rc<T> {
    fn as_ptr(&self) -> CursorPtr<T> {
        let ptr = &**self as *const T;
        // Safe because Rc guarantees its pointer is non-null
        unsafe { CursorPtr::new_unchecked(ptr as _) }
    }
}

unsafe impl<T> Detached<T> for Rc<T> {}

unsafe impl<'a, T: 'a> Handle<'a, T> for Rc<T> {
    type Guard = &'a T;

    fn lock_ref(&'a self) -> Self::Guard {
        &*self
    }
}

unsafe impl<'a, T: 'a> HandleMut<'a, T> for Rc<T> {
    type GuardMut = &'a mut T;

    fn lock_mut(&'a mut self) -> Self::GuardMut {
        Rc::get_mut(self).expect("other Rc references exist")
    }
}

impl<T> Cursor<T> for Arc<T> {
    fn as_ptr(&self) -> CursorPtr<T> {
        let ptr = &**self as *const T;
        // Safe because Arc guarantees its pointer is non-null
        unsafe { CursorPtr::new_unchecked(ptr as _) }
    }
}

unsafe impl<T> Detached<T> for Arc<T> {}

unsafe impl<'a, T: 'a> Handle<'a, T> for Arc<T> {
    type Guard = &'a T;

    fn lock_ref(&'a self) -> Self::Guard {
        &*self
    }
}

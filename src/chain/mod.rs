use core::ptr::NonNull;
use core::sync::atomic::{AtomicPtr, Ordering};

use crate::CurVec;

pub struct Chain<T> {
    head: Link<T>,
    tail: Link<T>,
}

impl<T> Chain<T> {
    pub fn new() -> Self {
        Self {
            head: Link::new(),
            tail: Link::new(),
        }
    }
}

pub struct Node<T> {
    ring: CurVec<T>,
    prev: Link<T>,
    next: Link<T>,
}

struct Link<T> {
    ptr: AtomicPtr<Node<T>>,
}

impl<T> Link<T> {
    fn new() -> Self {
        Self {
            ptr: AtomicPtr::new(0 as _),
        }
    }

    fn get(&self, order: Ordering) -> Option<&Node<T>> {
        unsafe { self.ptr.load(order).as_ref() }
    }

    fn set(&self, ptr: NonNull<Node<T>>, order: Ordering) {
        self.ptr.store(ptr.as_ptr(), order);
    }

    fn take(&self, order: Ordering) -> Option<NonNull<Node<T>>> {
        NonNull::new(self.ptr.swap(0 as _, order))
    }
}

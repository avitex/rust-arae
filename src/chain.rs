use core::ptr::NonNull;
use core::sync::atomic::{AtomicPtr, Ordering};

use crate::{Cursed, Sequence, Cursor, Bounded};

/// A `Chain` is a thread safe [`Cursed`] linked list inspired structure
/// where each node contains a [`Cursed`] [`Sequence`].
///
/// [`Cursed`]: trait.Cursed.html
/// [`Sequence`]: trait.Sequence.html
pub struct Chain<C, T> {
    // The head of the chain sequence.
    head: Link<C, T>,
    // The tail of the chain sequence.
    tail: Link<C, T>,
}

impl<C, T> Chain<C, T> {
    pub fn new() -> Self {
        Self {
            head: Link::new(),
            tail: Link::new(),
        }
    }
}

impl<C, T> Cursed<T> for Chain<C, T>
where
    C: Bounded<T>,
{
    fn is_owner(&self, _cursor: Cursor<T>) -> bool {
        unimplemented!()
    }
}

impl<C, T> Sequence<T> for Chain<C, T>
where
    C: Bounded<T>,
{
    fn next(&self, _cursor: Cursor<T>) -> Option<Cursor<T>> {
        unimplemented!()
    }

    fn prev(&self, _cursor: Cursor<T>) -> Option<Cursor<T>> {
        unimplemented!()
    }

    fn remaining(&self, _cursor: Cursor<T>) -> (usize, Option<usize>) {
        unimplemented!()
    }
}

impl<C, T> Bounded<T> for Chain<C, T>
where
    C: Bounded<T>,
{
    fn len(&self) -> usize {
        unimplemented!()
    }

    fn head(&self) -> Cursor<T> {
        unimplemented!()
    }

    fn tail(&self) -> Cursor<T> {
        unimplemented!()
    }

    fn at(&self, _offset: usize) -> Option<Cursor<T>> {
        unimplemented!()
    }
}

///////////////////////////////////////////////////////////////////////////////
// Node

struct Node<C, T> {
    prev: Link<C, T>,
    next: Link<C, T>,
    data: T,
}

///////////////////////////////////////////////////////////////////////////////
// Link

struct Link<C, T> {
    ptr: AtomicPtr<Node<C, T>>,
}

impl<C, T> Link<C, T> {
    fn new() -> Self {
        Self {
            ptr: AtomicPtr::new(0 as _),
        }
    }

    fn get(&self, order: Ordering) -> Option<&Node<C, T>> {
        unsafe { self.ptr.load(order).as_ref() }
    }

    fn set(&self, ptr: NonNull<Node<C, T>>, order: Ordering) {
        self.ptr.store(ptr.as_ptr(), order);
    }

    fn take(&self, order: Ordering) -> Option<NonNull<Node<C, T>>> {
        NonNull::new(self.ptr.swap(0 as _, order))
    }
}

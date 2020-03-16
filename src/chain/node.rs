use alloc::boxed::Box;
use core::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};

#[derive(Debug)]
pub(crate) struct Node<C, T> {
    /// The cursed data.
    pub data: C,
    /// The previous node.
    pub prev: NodePtr<C, T>,
    /// The next node.
    pub next: NodePtr<C, T>,
    /// The number of references to this node.
    /// This is used as a reference count
    /// for dropping the data once it
    /// reaches zero.
    ///
    /// When a node pointer is dropped,
    /// it decreases this count for us.
    refs: AtomicUsize,
}

impl<C, T> Node<C, T> {
    pub fn new(data: C, prev: *mut Node<C, T>, next: *mut Node<C, T>, refs: usize) -> Self {
        Self {
            data,
            prev: NodePtr::new(prev),
            next: NodePtr::new(next),
            refs: AtomicUsize::new(refs),
        }
    }

    pub fn new_for_insertion(data: C) -> Box<Self> {
        Box::new(Self::new(data, 0 as _, 0 as _, 2))
    }

    pub fn as_raw_ptr(&self) -> *mut Self {
        (self as *const Self) as _
    }

    // pub fn ptr_eq(&self, other: &Self) -> bool {
    //     self.as_ptr() == other.as_ptr()
    // }

    /// Decreases the ref count by one.
    /// Returns `true` if was the last ref, `false` if there are still links to this node.
    fn rem_ref(&self) -> bool {
        self.refs.fetch_sub(1, Ordering::Relaxed) == 0
    }

    /// Increases the ref count by a given amount.
    fn add_refs(&self, refs: u8) {
        if self.refs.fetch_add(refs as usize, Ordering::Relaxed) > isize::max_value() as usize {
            panic!("ref count to node greater than isize::MAX!");
        }
    }

    pub fn init_next_prev(&mut self, prev: *mut Node<C, T>, next: *mut Node<C, T>) {
        self.prev.set(prev);
        self.next.set(next);
    }
}

///////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
pub(crate) struct NodePtr<C, T> {
    inner: AtomicPtr<Node<C, T>>,
}

impl<C, T> NodePtr<C, T> {
    #[inline]
    pub fn new(ptr: *mut Node<C, T>) -> Self {
        Self {
            inner: AtomicPtr::new(ptr),
        }
    }

    #[inline]
    pub fn set(&mut self, ptr: *mut Node<C, T>) {
        *self.inner.get_mut() = ptr;
    }

    #[inline]
    pub fn load(&self, order: Ordering) -> *mut Node<C, T> {
        self.inner.load(order)
    }

    #[inline]
    pub fn store(&self, ptr: *mut Node<C, T>, order: Ordering) {
        self.inner.store(ptr, order)
    }

    #[inline]
    pub fn compare_exchange(
        &self,
        current: *mut Node<C, T>,
        new: *mut Node<C, T>,
        success: Ordering,
        failure: Ordering,
    ) -> Result<*mut Node<C, T>, *mut Node<C, T>> {
        self.inner.compare_exchange(current, new, success, failure)
    }
}

impl<C, T> Clone for NodePtr<C, T> {
    fn clone(&self) -> Self {
        // TODO: add ref
        unimplemented!()
    }
}

impl<C, T> Drop for NodePtr<C, T> {
    fn drop(&mut self) {
        // TODO: rem ref
    }
}

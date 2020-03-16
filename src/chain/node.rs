use alloc::boxed::Box;

use core::marker::PhantomData;
use core::ptr::NonNull;
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
    pub fn new(data: C, prev: *mut Node<C, T>, next: *mut Node<C, T>, refs: usize) -> Box<Self> {
        let this = Self {
            data,
            prev: NodePtr::new(prev),
            next: NodePtr::new(next),
            refs: AtomicUsize::new(refs),
        };
        Box::new(this)
    }

    pub fn new_for_insertion(data: C) -> Box<Self> {
        Self::new(data, 0 as _, 0 as _, 2)
    }

    pub fn init_next_prev(&mut self, prev: *mut Node<C, T>, next: *mut Node<C, T>) {
        self.prev.set(prev);
        self.next.set(next);
    }

    // pub fn as_raw_ptr(&self) -> *mut Self {
    //     (self as *const Self) as _
    // }

    // pub fn ptr_eq(&self, other: &Self) -> bool {
    //     self.as_ptr() == other.as_ptr()
    // }

    unsafe fn remove_ref(this: NonNull<Self>) {
        if this.as_ref().remove_ref_leaky() {
            Box::from_raw(this.as_ptr());
        }
    }

    /// Decreases the ref count by one.
    /// Returns `true` if was the last ref, `false` if there are still links to this node.
    unsafe fn remove_ref_leaky(&self) -> bool {
        self.refs.fetch_sub(1, Ordering::Relaxed) == 0
    }

    /// Increases the ref count by a given amount.
    fn add_refs(&self, refs: u8) {
        if self.refs.fetch_add(refs as usize, Ordering::Relaxed) > isize::max_value() as usize {
            panic!("ref count to node greater than isize::MAX!");
        }
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
    pub fn load(&self) -> Option<NonNull<Node<C, T>>> {
        NonNull::new(self.inner.load(Ordering::Relaxed))
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

    #[inline]
    pub fn to_node_ref(&self) -> Option<NodeRef<C, T>> {
        NodeRef::from_node_ptr(self)
    }
}

impl<C, T> Clone for NodePtr<C, T> {
    fn clone(&self) -> Self {
        match NodeRef::from_node_ptr(self) {
            Some(node_ref) => node_ref.into_node_ptr(),
            None => NodePtr::new(0 as _),
        }
    }
}

impl<C, T> Drop for NodePtr<C, T> {
    fn drop(&mut self) {
        if let Some(ptr) = self.load() {
            unsafe {
                NodeRef::from_tracked(ptr);
            }
        }
    }
}

///////////////////////////////////////////////////////////////////////////////

pub(crate) struct NodeRef<C, T> {
    ptr: NonNull<Node<C, T>>,
}

impl<C, T> NodeRef<C, T> {
    pub unsafe fn attach_new(ptr: NonNull<Node<C, T>>) -> Self {
        ptr.as_ref().add_refs(1);
        Self::from_tracked(ptr)
    }

    pub fn from_node_ptr(ptr: &NodePtr<C, T>) -> Option<Self> {
        ptr.load().map(|ptr| unsafe { Self::attach_new(ptr) })
    }

    pub unsafe fn from_tracked(ptr: NonNull<Node<C, T>>) -> Self {
        Self { ptr }
    }

    pub fn to_next(&self) -> Option<Self> {
        Self::from_node_ptr(&self.as_ref().next)
    }

    pub fn to_prev(&self) -> Option<Self> {
        Self::from_node_ptr(&self.as_ref().prev)
    }

    pub fn as_ptr(&self) -> *mut Node<C, T> {
        self.ptr.as_ptr()
    }

    pub fn into_node_ptr(self) -> NodePtr<C, T> {
        NodePtr::new(self.ptr.as_ptr())
    }

    pub fn data(&self) -> &C {
        &self.as_ref().data
    }

    pub fn as_ref(&self) -> &Node<C, T> {
        unsafe { self.ptr.as_ref() }
    }
}

impl<C, T> Clone for NodeRef<C, T> {
    fn clone(&self) -> Self {
        unsafe { Self::attach_new(self.ptr) }
    }
}

impl<C, T> Drop for NodeRef<C, T> {
    fn drop(&mut self) {
        unsafe { Node::remove_ref(self.ptr) }
    }
}

///////////////////////////////////////////////////////////////////////////////

pub(crate) struct NodeIter<'a, C, T> {
    is_first: bool,
    node: Option<NodeRef<C, T>>,
    lifetime: PhantomData<&'a ()>,
}

impl<'a, C, T> NodeIter<'a, C, T> {
    pub fn new(node: Option<NodeRef<C, T>>) -> Self {
        Self {
            node,
            is_first: true,
            lifetime: PhantomData,
        }
    }
}

impl<'a, C: 'a, T: 'a> Iterator for NodeIter<'a, C, T> {
    type Item = NodeRef<C, T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.node.clone().map(|node| {
            if self.is_first {
                self.is_first = false;
            } else {
                self.node = node.to_next();
            }
            node
        })
    }
}

impl<'a, C: 'a, T: 'a> DoubleEndedIterator for NodeIter<'a, C, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.node.clone().map(|node| {
            if self.is_first {
                self.is_first = false;
            } else {
                self.node = node.to_prev();
            }
            node
        })
    }
}

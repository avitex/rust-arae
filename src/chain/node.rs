use alloc::boxed::Box;

use core::marker::PhantomData;
use core::ptr::NonNull;
use core::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};

#[derive(Debug)]
pub(crate) struct Node<C, T> {
    /// The cursed data.
    pub data: C,
    /// The previous node, if any.
    pub prev: AtomicNodePtr<C, T>,
    /// The next node, if any.
    pub next: AtomicNodePtr<C, T>,
    /// The number of references to this node.
    refs: AtomicUsize,
}

impl<C, T> Node<C, T> {
    /// Allocates a new node structure with the data it will own.
    #[inline]
    pub fn new(data: C) -> Self {
        Self {
            data,
            prev: AtomicNodePtr::null(),
            next: AtomicNodePtr::null(),
            refs: AtomicUsize::new(0),
        }
    }

    /// Initializes the node for chain insertion by setting the reference count to `2`.
    #[inline]
    pub fn init_insert(mut self) -> Self {
        *self.refs.get_mut() = 2;
        self
    }

    /// Initializes the node's `prev` and `next` node pointers.
    ///
    /// # Safety
    ///
    /// Caller must guarantee the node pointers are either null or reference
    /// valid nodes with the correct reference count (as so they don't drop).
    #[inline]
    pub unsafe fn set_prev_next(&mut self, prev: *mut Node<C, T>, next: *mut Node<C, T>) {
        self.prev.set(prev);
        self.next.set(next);
    }

    // TODO: remove?
    // /// Returns the current amount of references to this node.
    // pub fn refs(&self) -> usize {
    //     self.refs.load(Ordering::Relaxed)
    // }

    /// Increases the reference count by a given amount.
    ///
    /// This function is to be used by reference counting structures who
    /// promise to drop their reference once complete.
    ///
    /// # Panics
    ///
    /// Panics if the resulting reference count is greater than `isize::MAX`.
    pub fn add_refs(&self, refs: u8) {
        if self.refs.fetch_add(refs as usize, Ordering::Relaxed) > isize::max_value() as usize {
            panic!("ref count to node greater than isize::MAX!");
        }
    }

    /// Drops a node ref, returning the recovered boxed node if was the
    /// last reference.
    ///
    /// This function is to be used by reference counting structures.
    ///
    /// # Safety
    ///
    /// Caller must guarantee the pointer references a valid boxed node and will
    /// not be used again, unless the resulting boxed node is handled correctly.
    pub unsafe fn drop_ref(ptr: NonNull<Self>) -> Option<Box<Self>> {
        if ptr.as_ref().refs.fetch_sub(1, Ordering::Relaxed) == 0 {
            Some(Box::from_raw(ptr.as_ptr()))
        } else {
            None
        }
    }
}

///////////////////////////////////////////////////////////////////////////////

/// A counted reference to a [`Node`].
#[derive(Debug)]
pub(crate) struct NodeRef<C, T> {
    ptr: NonNull<Node<C, T>>,
}

impl<C, T> NodeRef<C, T> {
    /// Constructs a new reference to a given [`Node`].
    ///
    /// Increases the reference count on the [`Node`].
    ///
    /// # Safety
    ///
    /// Caller must guarantee the pointer references a valid node.
    pub unsafe fn attach_new(ptr: NonNull<Node<C, T>>) -> Self {
        ptr.as_ref().add_refs(1);
        Self::from_tracked(ptr)
    }

    /// Constructs a new reference to a given [`Node`].
    ///
    /// Unlike [`attach_new`] does not increase the reference count
    /// on the [`Node`].
    ///
    /// # Safety
    ///
    /// Caller must guarantee the pointer references a valid [`Node`],
    /// and that this structure takes ownership of a count as so the
    /// [`Node`] does not drop while this reference is alive.
    pub unsafe fn from_tracked(ptr: NonNull<Node<C, T>>) -> Self {
        Self { ptr }
    }

    /// Returns a new reference to the next [`Node`] pointed to by `self`
    /// if it exists, `None` if no [`Node`] is pointed to.
    pub fn next_node(&self) -> Option<Self> {
        self.as_ref().next.to_node_ref()
    }

    /// Returns a new reference to the previous [`Node`] pointed to by `self`
    /// if it exists, `None` if no [`Node`] is pointed to.
    pub fn prev_node(&self) -> Option<Self> {
        self.as_ref().prev.to_node_ref()
    }

    /// Return a reference to the data owned by the [`Node`] referenced.
    pub fn data(&self) -> &C {
        &self.as_ref().data
    }

    /// Returns a reference to the underlying [`Node`] referenced.
    pub fn as_ref(&self) -> &Node<C, T> {
        // Safe as we guarantee the node lives while `self` is alive.
        unsafe { self.ptr.as_ref() }
    }

    /// Returns the raw pointer to the [`Node`] referenced.
    pub fn as_ptr(&self) -> NonNull<Node<C, T>> {
        self.ptr
    }
}

impl<C, T> Clone for NodeRef<C, T> {
    fn clone(&self) -> Self {
        unsafe { Self::attach_new(self.ptr) }
    }
}

impl<C, T> Drop for NodeRef<C, T> {
    fn drop(&mut self) {
        unsafe {
            Node::drop_ref(self.ptr);
        }
    }
}

///////////////////////////////////////////////////////////////////////////////

/// An atomic, thread-safe [`Node`] pointer.
#[derive(Debug)]
pub(crate) struct AtomicNodePtr<C, T>(AtomicPtr<Node<C, T>>);

impl<C, T> AtomicNodePtr<C, T> {
    /// Constructs a new [`AtomicNodePtr`] pointing to nothing.
    #[inline]
    pub fn null() -> Self {
        Self(AtomicPtr::new(0 as _))
    }

    /// Construct a new [`AtomicNodePtr`] pointing to a given node.
    ///
    /// # Safety
    ///
    /// Caller must guarantee the pointer references a valid [`Node`],
    /// and that this structure takes ownership of a count as so the
    /// [`Node`] does not drop while this reference is alive.
    #[inline]
    pub unsafe fn from_tracked(ptr: NonNull<Node<C, T>>) -> Self {
        Self(AtomicPtr::new(ptr.as_ptr()))
    }

    /// Loads the pointer stored internally
    #[inline]
    pub fn load(&self) -> Option<NonNull<Node<C, T>>> {
        NonNull::new(self.0.load(Ordering::Relaxed))
    }

    /// Set the internal pointer value using mutable exclusivity.
    ///
    /// # Safety
    ///
    /// Caller must guarantee the pointer is null or references a valid [`Node`],
    /// and that this structure takes ownership of a count as so the
    /// [`Node`] does not drop while this reference is alive.
    #[inline]
    pub unsafe fn set(&mut self, ptr: *mut Node<C, T>) {
        *self.0.get_mut() = ptr;
    }

    /// Atomically store the internal pointer value.
    ///
    /// # Safety
    ///
    /// Caller must guarantee the pointer is null or references a valid [`Node`],
    /// and that this structure takes ownership of a count as so the
    /// [`Node`] does not drop while this reference is alive.
    #[inline]
    pub unsafe fn store(&self, ptr: *mut Node<C, T>, order: Ordering) {
        self.0.store(ptr, order)
    }

    /// Stores a value if the current value is the same as the `current` value.
    ///
    /// The return value is a result indicating whether the new value was written and containing
    /// the previous value. On success this value is guaranteed to be equal to `current`.
    ///
    /// `compare_exchange` takes two `Ordering` arguments to describe the memory
    /// ordering of this operation. The first describes the required ordering if the
    /// operation succeeds while the second describeremove?s the required ordering when the
    /// operation fails. Using `Acquire` as success ordering makes the store part
    /// of this operation `Relaxed`, and using `Release` makes the successful load
    /// `Relaxed`. The failure ordering can only be `SeqCst`, `Acquire` or `Relaxed`
    /// and must be equivalent to or weaker than the success ordering.
    #[inline]
    pub unsafe fn compare_exchange(
        &self,
        current: *mut Node<C, T>,
        new: *mut Node<C, T>,
        success: Ordering,
        failure: Ordering,
    ) -> Result<*mut Node<C, T>, *mut Node<C, T>> {
        self.0.compare_exchange(current, new, success, failure)
    }

    /// Returns `Some(`[`NodeRef`]`)` if the internal pointer is not null,
    /// `None` if it is.
    #[inline]
    pub fn to_node_ref(&self) -> Option<NodeRef<C, T>> {
        self.load().map(|ptr|
            // Safe as we guarantee the node lives while `self` is alive.
            unsafe { NodeRef::attach_new(ptr) })
    }
}

impl<C, T> From<NodeRef<C, T>> for AtomicNodePtr<C, T> {
    fn from(node_ref: NodeRef<C, T>) -> Self {
        unsafe { Self::from_tracked(node_ref.ptr) }
    }
}

impl<C, T> Clone for AtomicNodePtr<C, T> {
    fn clone(&self) -> Self {
        match self.to_node_ref() {
            Some(node_ref) => node_ref.into(),
            None => AtomicNodePtr::null(),
        }
    }
}

impl<C, T> Drop for AtomicNodePtr<C, T> {
    fn drop(&mut self) {
        if let Some(ptr) = self.load() {
            unsafe {
                NodeRef::from_tracked(ptr);
            }
        }
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
                self.node = node.next_node();
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
                self.node = node.prev_node();
            }
            node
        })
    }
}

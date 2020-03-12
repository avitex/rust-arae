use alloc::boxed::Box;
use core::ptr::NonNull;

use crate::atomic::{AtomicPtr, AtomicUsize, Ordering};
use crate::{Bounded, Cursed, Cursor, CursorPtr, Sequence};

enum Boundary {
    Head,
    Tail,
}

impl Boundary {
    fn is_head(self) -> bool {
        match self {
            Self::Head => true,
            Self::Tail => false,
        }
    }
}

/// A `Chain` is a thread safe [`Cursed`] linked list inspired structure
/// where each node contains a [`Cursed`] [`Sequence`].
///
/// [`Cursed`]: trait.Cursed.html
/// [`Sequence`]: trait.Sequence.html
pub struct Chain<C, T> {
    // The head of the chain sequence.
    head: NodePtr<C, T>,
    // The tail of the chain sequence.
    tail: NodePtr<C, T>,
}

impl<C, T> Chain<C, T>
where
    C: Bounded<T>,
{
    pub fn new(data: C) -> Self {
        let node = Node::<C, T>::new_solo(data).into_boxed_ptr();
        Self {
            head: NodePtr::new(node),
            tail: NodePtr::new(node),
        }
    }

    pub fn push_front(&self, data: C) {
        let node = Node::<C, T>::new_solo(data).into_boxed_ptr();
        // Spin while we attempt to add between the chain head and node it points to.
        unsafe { while !push_boundary_node(&self.head, Boundary::Head, node) {} }
    }

    pub fn push_back(&self, data: C) {
        let node = Node::<C, T>::new_solo(data).into_boxed_ptr();
        unsafe { while !push_boundary_node(&self.tail, Boundary::Tail, node) {} }
    }

    pub fn insert_at(&self, at: usize, data: C) {
        self.insert_at_link_fn(data, |head, tail| Link::at_elem_offset(at, head, tail));
    }

    pub fn insert_at_node(&self, at: usize, data: C) {
        self.insert_at_link_fn(data, |head, tail| Link::at_node_offset(at, head, tail));
    }

    pub fn insert_ordered(&self, data: C) {
        let at = data.head();
        self.insert_at_link_fn(data, |head, tail| Link::find_ordered(&at, head, tail));
    }

    fn insert_at_link_fn<F>(&self, data: C, f: F)
    where
        F: for<'a> Fn(&'a Node<C, T>, &'a Node<C, T>) -> Link<'a, C, T>,
    {
        let node = Node::<C, T>::new_solo(data).into_boxed_ptr();
        loop {
            let head = self
                .head
                .load_ref()
                .expect("boundary node ptr must not be null");
            let tail = self
                .tail
                .load_ref()
                .expect("boundary node ptr must not be null");
            let link = f(&head, &tail);
            if unsafe { link.inject(node) } {
                break;
            }
        }
    }
}

// impl<C, T> Cursed<T> for Chain<C, T>
// where
//     C: Bounded<T>,
// {
//     fn is_owner(&self, _cursor: Cursor<T>) -> bool {
//         unimplemented!()
//     }
// }

// impl<C, T> Sequence<T> for Chain<C, T>
// where
//     C: Bounded<T>,
// {
//     fn next(&self, _cursor: Cursor<T>) -> Option<Cursor<T>> {
//         unimplemented!()
//     }

//     fn prev(&self, _cursor: Cursor<T>) -> Option<Cursor<T>> {
//         unimplemented!()
//     }

//     fn remaining(&self, _cursor: Cursor<T>) -> (usize, Option<usize>) {
//         unimplemented!()
//     }
// }

// impl<C, T> Bounded<T> for Chain<C, T>
// where
//     C: Bounded<T>,
// {
//     fn len(&self) -> usize {
//         unimplemented!()
//     }

//     fn head(&self) -> Cursor<T> {
//         unimplemented!()
//     }

//     fn tail(&self) -> Cursor<T> {
//         unimplemented!()
//     }

//     fn at(&self, _offset: usize) -> Option<Cursor<T>> {
//         unimplemented!()
//     }
// }

///////////////////////////////////////////////////////////////////////////////
// Node

struct Node<C, T> {
    /// The cursed data.
    data: C,
    /// The previous node.
    prev: NodePtr<C, T>,
    /// The next node.
    next: NodePtr<C, T>,
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
    fn new(data: C, prev: NodePtr<C, T>, next: NodePtr<C, T>) -> Self {
        let refs = AtomicUsize::new(2);
        Self {
            data,
            prev,
            next,
            refs,
        }
    }

    fn new_solo(data: C) -> Self {
        Self::new(data, NodePtr::new_null(), NodePtr::new_null())
    }

    fn new_self_referential(data: C) -> NonNull<Self> {
        let this = Self::new_solo(data);
        let this_ptr = this.into_boxed_ptr();
        //
        this_ptr.as_mut().next.excusive_set(this_ptr.as_ptr());
        this_ptr.as_mut().next.excusive_set(this_ptr.as_ptr());
        //
        this_ptr
    }

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

    fn as_ptr(&self) -> *mut Self {
        (self as *const Self) as _
    }

    fn ptr_eq(&self, other: &Self) -> bool {
        self.as_ptr() == other.as_ptr()
    }

    unsafe fn as_ptr_non_null(&self) -> NonNull<Self> {
        NonNull::new_unchecked(self.as_ptr() as _)
    }

    fn into_boxed_ptr(self) -> NonNull<Self> {
        // TODO: Use Box::into_raw_non_null when stable.
        let ptr = Box::into_raw(Box::new(self));
        unsafe { NonNull::new_unchecked(ptr) }
    }

    fn init_boundary_tail(&mut self, prev: NonNull<Node<C, T>>) {
        self.prev.excusive_set(prev.as_ptr());
        self.next.excusive_set(0 as _);
    }

    fn init_boundary_head(&mut self, next: NonNull<Node<C, T>>) {
        self.prev.excusive_set(0 as _);
        self.next.excusive_set(next.as_ptr());
    }
}

///////////////////////////////////////////////////////////////////////////////

/// A Link represents an attachment between two nodes at a given time.
struct Link<'a, C, T> {
    left: &'a NodePtr<C, T>,
    left_current: *mut Node<C, T>,
    right: &'a NodePtr<C, T>,
    right_current: *mut Node<C, T>,
}

impl<'a, C, T> Link<'a, C, T>
where
    C: Bounded<T>,
{
    pub fn find_ordered(at: &C::Cursor, left: &'a Node<C, T>, right: &'a Node<C, T>) -> Self {
        let at = at.as_ptr();
        unimplemented!()
    }

    pub fn at_node_offset(at: usize, left: &'a Node<C, T>, right: &'a Node<C, T>) -> Self {
        unimplemented!()
    }

    pub fn at_elem_offset(at: usize, left: &'a Node<C, T>, right: &'a Node<C, T>) -> Self {
        unimplemented!()
    }

    // fn for_current(left: &'a NodePtr<C, T>, right: &'a NodePtr<C, T>) -> Self {
    //     let left_current = left
    //         .load_non_null()
    //         .expect("left ptr for link null")
    //         .as_ptr();
    //     let right_current = right
    //         .load_non_null()
    //         .expect("right ptr for link null")
    //         .as_ptr();
    //     Self {
    //         left,
    //         left_current,
    //         right,
    //         right_current,
    //     }
    // }

    unsafe fn inject(&self, node: NonNull<Node<C, T>>) -> bool {
        let node_ref = node.as_ref();
        if node_ptr_exchange(self.left, self.left_current, &node_ref.prev, node.as_ptr()) {
            if !node_ptr_exchange(
                self.right,
                self.right_current,
                &node_ref.next,
                node.as_ptr(),
            ) {
                panic!("waaaaaaaaaa")
            }
            true
        } else {
            false
        }
    }
}

///////////////////////////////////////////////////////////////////////////////
// NodePtr

struct NodePtr<C, T> {
    ptr: AtomicPtr<Node<C, T>>,
}

impl<C, T> NodePtr<C, T> {
    fn new(ptr: NonNull<Node<C, T>>) -> Self {
        Self {
            ptr: AtomicPtr::new(ptr.as_ptr()),
        }
    }

    fn new_null() -> Self {
        Self {
            ptr: AtomicPtr::new(0 as _),
        }
    }

    fn store(&self, ptr: *mut Node<C, T>) {
        self.ptr.store(ptr, Ordering::Relaxed);
    }

    fn excusive_set(&mut self, ptr: *mut Node<C, T>) {
        *self.ptr.get_mut() = ptr;
    }

    fn load(&self) -> *mut Node<C, T> {
        self.ptr.load(Ordering::Relaxed)
    }

    fn load_ref(&self) -> Option<&Node<C, T>> {
        self.load().as_ref()
    }

    fn load_non_null(&self) -> Option<NonNull<Node<C, T>>> {
        NonNull::new(self.load())
    }

    // unsafe fn load_non_null_unchecked(&self) -> NonNull<Node<C, T>> {
    //     let ptr = self.load();
    //     debug_assert_ne!(ptr, 0);
    //     unsafe { NonNull::new_unchecked(ptr) }
    // }

    // fn take(&self) -> Option<NonNull<Node<C, T>>> {
    //     NonNull::new(self.ptr.swap(0 as _, Ordering::SeqCst))
    // }
}

/// The caller must promise no other references to `new_node` exist.
unsafe fn push_boundary_node<C, T>(
    boundary: &NodePtr<C, T>,
    to: Boundary,
    new_node: NonNull<Node<C, T>>,
) -> bool {
    let current_boundary = boundary
        .load_ref()
        .expect("boundary node ptr cannot be null");
    let boundary_node_null_side = match to {
        Boundary::Head => {
            let new_node_mut = new_node.as_mut();
            new_node_mut.init_boundary_head(current_boundary.into());
            current_boundary.prev
        }
        Boundary::Tail => {
            let new_node_mut = unsafe { new_node.as_mut() };
            new_node_mut.init_boundary_tail(current_boundary.into());
            current_boundary.next
        }
    };
    let boundary_change_result = boundary.ptr.compare_exchange(
        current_boundary.as_ptr() as _,
        new_node.as_ptr(),
        Ordering::Acquire,
        Ordering::Relaxed,
    );
    if boundary_change_result.is_err() {
        return false;
    }
    boundary_node_null_side
        .ptr
        .store(new_node.as_ptr(), Ordering::Release);
    true
}

/// Atomically exchanges two node pointer values, with the given expected values.
///
/// This operation has the notion of a hot `NodePtr`, and a stable `NodePtr`.
///
/// - The hot `NodePtr` may or may not have changed from it's current value.
/// - The stable `NodePtr` is expected not to have changed.
///
/// The operation is deemed successful if the hot `NodePtr` is the expected value of `hot_current`,
/// and will return `true` on success and `false` on failure.
///
/// # Panics
///
/// This operation will panic if the stable pointer is not the expected value of `stable_current`.
///
fn node_ptr_exchange<C, T>(
    hot: &NodePtr<C, T>,
    hot_current: *mut Node<C, T>,
    stable: &NodePtr<C, T>,
    stable_current: *mut Node<C, T>,
) -> bool {
    // Attempt to exchange the hot pointer first.
    let left_swap_result = hot.ptr.compare_exchange(
        hot_current,
        stable_current,
        Ordering::SeqCst,
        Ordering::SeqCst,
    );

    // If we failed, just return early.
    if left_swap_result.is_err() {
        return false;
    }

    // Now attempt to exchange the stable pointer.
    let right_swap_result = stable.ptr.compare_exchange(
        stable_current,
        hot_current,
        Ordering::SeqCst,
        Ordering::SeqCst,
    );

    // This operation should always succeed.
    right_swap_result.expect("node pointer exchange failed");

    // We did it!
    true
}

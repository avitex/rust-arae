mod node;

use core::ptr::NonNull;

use crate::atomic::Ordering;
use crate::{Bounded, Cursor};

use self::node::{Node, NodePtr};

enum Boundary {
    Head,
    Tail,
}

/// A [`Cursed`] thread safe, linked list inspired structure
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
        let node = Node::<C, T>::new_for_insertion(data);
        Self {
            head: NodePtr::new(node),
            tail: NodePtr::new(node),
        }
    }

    pub fn push_front(&self, data: C) {
        let node = Node::<C, T>::new_for_insertion(data);
        // Spin while we attempt to add between the chain head and node it points to.
        unimplemented!()
        //unsafe { while !push_boundary_node(&self.head, Boundary::Head, node) {} }
    }

    pub fn push_back(&self, data: C) {
        let node = Node::<C, T>::new_for_insertion(data);
        unimplemented!()
        //unsafe { while !push_boundary_node(&self.tail, Boundary::Tail, node) {} }
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
        let node = Node::<C, T>::new_for_insertion(data);
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
            unimplemented!()
            // if unsafe { link.inject(node) } {
            //     break;
            // }
        }
    }
}

/// A Link represents an attachment between two nodes at a given time.
struct Link<'a, C, T> {
    left_next: &'a NodePtr<C, T>,
    right_prev: &'a NodePtr<C, T>,
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

    // pub fn from_node_node(left: &'a Node<C, T>, right: &'a Node<C, T>) -> Option<Self> {
    //     // Load the pointer from the left Node.next.
    //     let right_ref = match left.next.load(Ordering::Relaxed) {
    //         None => return None,
    //         Some(right_ref) => right_ref,
    //     };
    //     // Load the pointer from the left Node.prev.
    //     let left_ref = match right.prev.load(Ordering::Relaxed) {
    //         None => return None,
    //         Some(left_ref) => left_ref,
    //     };
    //     // Because we are injecting the new node directly between
    //     // left and right, both should point to each other.
    //     // If they don't we didn't get given a valid link.
    //     if left.ptr_eq(right_ref) && right.ptr_eq(right_ref) {
    //         Some(Self::from_node_node_unchecked(left, right))
    //     } else {
    //         None
    //     }
    // }

    pub fn from_node_node_unchecked(left: &'a Node<C, T>, right: &'a Node<C, T>) -> Self {
        Self { left_next: &left.next, right_prev: &right.prev }
    }

    unsafe fn inject(&self, mut node: NonNull<Node<C, T>>) -> bool {
        let node_ref = node.as_mut();
        node_ref.prev.excusive_set(self.);
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

    // unsafe fn inject(&self, node: NonNull<Node<C, T>>) -> bool {
    //     let node_ref = node.as_ref();
    //     if node_ptr_exchange(self.left, self.left_current, &node_ref.prev, node.as_ptr()) {
    //         if !node_ptr_exchange(
    //             self.right,
    //             self.right_current,
    //             &node_ref.next,
    //             node.as_ptr(),
    //         ) {
    //             panic!("waaaaaaaaaa")
    //         }
    //         true
    //     } else {
    //         false
    //     }
    // }
}

// /// The caller must promise no other references to `new_node` exist.
// unsafe fn push_boundary_node<C, T>(
//     boundary: &NodePtr<C, T>,
//     to: Boundary,
//     mut new_node: NonNull<Node<C, T>>,
// ) -> bool {
//     let current_boundary = boundary
//         .load_ref()
//         .expect("boundary node ptr cannot be null");
//     let boundary_node_null_side = match to {
//         Boundary::Head => {
//             let new_node_mut = new_node.as_mut();
//             new_node_mut.init_boundary_head(current_boundary.into());
//             &current_boundary.prev
//         }
//         Boundary::Tail => {
//             let new_node_mut = new_node.as_mut();
//             new_node_mut.init_boundary_tail(current_boundary.into());
//             &current_boundary.next
//         }
//     };
//     let boundary_change_result = boundary.ptr.compare_exchange(
//         current_boundary.as_ptr() as _,
//         new_node.as_ptr(),
//         Ordering::Acquire,
//         Ordering::Relaxed,
//     );
//     if boundary_change_result.is_err() {
//         return false;
//     }
//     boundary_node_null_side
//         .ptr
//         .store(new_node.as_ptr(), Ordering::Release);
//     true
// }

// /// Atomically exchanges two node pointer values, with the given expected values.
// ///
// /// This operation has the notion of a hot `NodePtr`, and a stable `NodePtr`.
// ///
// /// - The hot `NodePtr` may or may not have changed from it's current value.
// /// - The stable `NodePtr` is expected not to have changed.
// ///
// /// The operation is deemed successful if the hot `NodePtr` is the expected value of `hot_current`,
// /// and will return `true` on success and `false` on failure.
// ///
// /// # Panics
// ///
// /// This operation will panic if the stable pointer is not the expected value of `stable_current`.
// ///
// fn node_ptr_exchange<C, T>(
//     hot: &NodePtr<C, T>,
//     hot_current: *mut Node<C, T>,
//     stable: &NodePtr<C, T>,
//     stable_current: *mut Node<C, T>,
// ) -> bool {
//     // Attempt to exchange the hot pointer first.
//     let left_swap_result = hot.ptr.compare_exchange(
//         hot_current,
//         stable_current,
//         Ordering::SeqCst,
//         Ordering::SeqCst,
//     );

//     // If we failed, just return early.
//     if left_swap_result.is_err() {
//         return false;
//     }

//     // Now attempt to exchange the stable pointer.
//     let right_swap_result = stable.ptr.compare_exchange(
//         stable_current,
//         hot_current,
//         Ordering::SeqCst,
//         Ordering::SeqCst,
//     );

//     // This operation should always succeed.
//     right_swap_result.expect("node pointer exchange failed");

//     // We did it!
//     true
// }

// enum NodeInjectKind {
//     NodeTail,
//     HeadNode,
//     NodeNode,
// }

enum NodeInjectResult {
    Ok,
    NodesNotLinked,
    LeftBecameTail,
    RightBecameHead,
}

// /// Atomically attempt to inject a node between two pointers.
// /// 
// /// Atomic operations on node pointers always start from the left side of a node first.
// /// 
// /// # Safety
// /// 
// /// The caller must promise no other references to `node` exist.
// unsafe fn node_node_inject_operation<C, T>(
//     mut node: NonNull<Node<C, T>>,
//     left: &Node<C, T>,
//     right: &Node<C, T>
// ) -> NodeInjectResult {
    
//     // Now we start our operation.
//     left.next.ptr.compare_swap()

//     Link::
// }

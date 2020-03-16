mod node;

use crate::atomic::Ordering;
use crate::cursor::{Cursor, CursorPtr};
use crate::Bounded;

use self::node::{Node, NodePtr};

/// A [`Cursed`] thread safe, linked list inspired structure
/// where each node contains a [`Cursed`] [`Sequence`].
///
/// [`Cursed`]: trait.Cursed.html
/// [`Sequence`]: trait.Sequence.html
#[derive(Debug)]
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
    pub fn new() -> Self {
        Self {
            head: NodePtr::new(0 as _),
            tail: NodePtr::new(0 as _),
        }
    }

    pub fn push_front(&self, data: C) {
        Link::inject_fn(data, || {
            let head_node = self.head_node();
            let head_node_ptr = head_node.map(Node::as_raw_ptr).unwrap_or(0 as _);
            let head_node_prev = head_node.map(|n| &n.prev).unwrap_or(&self.tail);
            Link {
                left_node: 0 as _,
                left_next: &self.head,
                right_node: head_node_ptr,
                right_prev: head_node_prev,
            }
        })
    }

    pub fn push_back(&self, data: C) {
        Link::inject_fn(data, || {
            let tail_node = self.tail_node();
            let tail_node_ptr = tail_node.map(Node::as_raw_ptr).unwrap_or(0 as _);
            let tail_node_next = tail_node.map(|n| &n.next).unwrap_or(&self.head);
            Link {
                left_node: tail_node_ptr,
                left_next: tail_node_next,
                right_node: 0 as _,
                right_prev: &self.tail,
            }
        })
    }

    pub fn insert_at(&self, at: usize, data: C) {
        Link::inject_fn(data, || Link::at_elem_offset(at, &self.head, &self.tail));
    }

    pub fn insert_at_node(&self, at: usize, data: C) {
        Link::inject_fn(data, || Link::at_node_offset(at, &self.head, &self.tail));
    }

    pub fn insert_ordered(&self, data: C) {
        let at = data.head();
        Link::inject_fn(data, || Link::find_ordered(&at, &self.head, &self.tail));
    }

    fn head_node(&self) -> Option<&Node<C, T>> {
        unsafe { self.head.load(Ordering::Relaxed).as_ref() }
    }

    fn tail_node(&self) -> Option<&Node<C, T>> {
        unsafe { self.tail.load(Ordering::Relaxed).as_ref() }
    }
}

/// A Link represents an attachment between two node pointers at a given time.
struct Link<'a, C, T> {
    left_node: *mut Node<C, T>,
    /// The left to right node pointer.
    left_next: &'a NodePtr<C, T>,
    /// Pointer to the right node for this link.
    right_node: *mut Node<C, T>,
    /// The right to left node pointer.
    right_prev: &'a NodePtr<C, T>,
}

impl<'a, C: 'a, T: 'a> Link<'a, C, T>
where
    C: Bounded<T>,
{
    pub fn find_ordered(
        _at: &C::Cursor,
        _left: &'a NodePtr<C, T>,
        _right: &'a NodePtr<C, T>,
    ) -> Self {
        //let at = at.as_ptr();
        unimplemented!()
    }

    pub fn at_node_offset(_at: usize, _left: &'a NodePtr<C, T>, _right: &'a NodePtr<C, T>) -> Self {
        unimplemented!()
    }

    pub fn at_elem_offset(_at: usize, _left: &'a NodePtr<C, T>, _right: &'a NodePtr<C, T>) -> Self {
        unimplemented!()
    }

    fn inject_fn<F>(data: C, mut f: F)
    where
        F: FnMut() -> Self,
    {
        // Create our node for insertion.
        let mut node = Node::<C, T>::new_for_insertion(data);
        // Spin while we attempt to inject the node in the generated link.
        loop {
            match f().inject(node) {
                Ok(()) => return,
                Err(failed_node) => node = failed_node,
            }
        }
    }

    /// Atomically insert a prepared node into the chain.
    ///
    /// This operation requires the node was prepared for the given link.
    fn inject(&self, mut new_node: Box<Node<C, T>>) -> Result<(), Box<Node<C, T>>> {
        new_node.init_next_prev(self.left_node, self.right_node);
        let new_node = Box::into_raw(new_node);
        if self
            .left_next
            .compare_exchange(
                self.right_node,
                new_node,
                Ordering::Acquire,
                Ordering::Relaxed,
            )
            .is_err()
        {
            let new_node = unsafe { Box::from_raw(new_node) };
            return Err(new_node);
        }
        self.right_prev.store(new_node, Ordering::Release);
        Ok(())
    }
}

///////////////////////////////////////////////////////////////////////////////

pub struct ChainCursor<C, T>
where
    C: Bounded<T>,
{
    node: NodePtr<C, T>,
    node_cursor: C::Cursor,
}

impl<C, T> Cursor<T> for ChainCursor<C, T>
where
    C: Bounded<T>,
{
    fn as_ptr(&self) -> CursorPtr<T> {
        self.node_cursor.as_ptr()
    }
}

impl<C, T> Clone for ChainCursor<C, T>
where
    C: Bounded<T>,
{
    fn clone(&self) -> Self {
        Self {
            node: self.node.clone(),
            node_cursor: self.node_cursor.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Unit;

    #[test]
    fn push_front() {
        let chain = Chain::new();
        chain.push_front(Unit(1));
        chain.push_front(Unit(2));

        assert_eq!(chain.head_node().unwrap().data.0, 2);
    }
}

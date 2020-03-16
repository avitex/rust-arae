mod node;

use crate::atomic::Ordering;
use crate::cursor::{Cursor, CursorPtr};
use crate::Bounded;

use self::node::NodeIter;
use self::node::{Node, NodePtr, NodeRef};

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
        Link::inject_fn(data, || Link::new(&self, None, self.head.to_node_ref()))
    }

    pub fn push_back(&self, data: C) {
        Link::inject_fn(data, || Link::new(&self, self.tail.to_node_ref(), None))
    }

    // NodeIter::new(left.to_node_ref())
    //     .flat_map(|node| node.as_ref().data.iter())
    //     .nth(at)

    pub fn insert_at(&self, at: usize, data: C) {
        if at == 0 {
            self.push_front(data)
        } else {
            Link::inject_fn(data, || {
                let node = NodeIter::new(self.head.to_node_ref()).nth(at).unwrap();
                Link::with_right_of(&self, Some(node))
            });
        }
    }

    pub fn insert_ordered(&self, data: C) {
        let at = data.head();
        Link::inject_fn(data, || {
            let node = NodeIter::new(self.head.to_node_ref())
                .find(|node| at.as_ptr() >= node.data().head().as_ptr());
            Link::with_right_of(&self, node)
        });
    }
}

/// A Link represents an attachment between two node pointers at a given time.
struct Link<'a, C, T> {
    chain: &'a Chain<C, T>,
    left: Option<NodeRef<C, T>>,
    right: Option<NodeRef<C, T>>,
}

impl<'a, C: 'a, T: 'a> Link<'a, C, T>
where
    C: Bounded<T>,
{
    pub fn new(
        chain: &'a Chain<C, T>,
        left: Option<NodeRef<C, T>>,
        right: Option<NodeRef<C, T>>,
    ) -> Self {
        Self { chain, left, right }
    }

    // pub fn with_left_of(chain: &'a Chain<C, T>, right: Option<NodeRef<C, T>>) -> Self {
    //     let left = right.as_ref().and_then(|right| right.to_prev());
    //     Self::new(chain, left, right)
    // }

    pub fn with_right_of(chain: &'a Chain<C, T>, left: Option<NodeRef<C, T>>) -> Self {
        let right = left.as_ref().and_then(|left| left.to_next());
        Self::new(chain, left, right)
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
    fn inject(&self, mut new_node: Box<Node<C, T>>) -> Result<(), Box<Node<C, T>>> {
        let (left_ptr, left_next) = match self.left.as_ref() {
            Some(left) => (left.as_ptr(), &left.as_ref().next),
            None => (0 as _, &self.chain.head),
        };
        let (right_ptr, right_prev) = match self.right.as_ref() {
            Some(right) => (right.as_ptr(), &right.as_ref().prev),
            None => (0 as _, &self.chain.tail),
        };
        new_node.init_next_prev(left_ptr, right_ptr);
        let new_node = Box::into_raw(new_node);
        if left_next
            .compare_exchange(right_ptr, new_node, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            let new_node = unsafe { Box::from_raw(new_node) };
            return Err(new_node);
        }
        right_prev.store(new_node, Ordering::Release);
        Ok(())
    }
}

///////////////////////////////////////////////////////////////////////////////

/// A [`Cursor`] for a [`Chain`] structure.
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
        chain.push_back(Unit(3));

        assert_eq!(chain.head.to_node_ref().unwrap().data().0, 2);
        assert_eq!(chain.tail.to_node_ref().unwrap().data().0, 3);
    }
}

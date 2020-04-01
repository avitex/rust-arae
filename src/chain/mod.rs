mod node;

use crate::atomic::Ordering;
use crate::cursor::{Cursor, CursorPtr};
use crate::{Bounded, Cursed, Sequence};

use self::node::NodeIter;
use self::node::{AtomicNodePtr, Node, NodeRef};

/// A [`Cursed`] thread safe, linked list inspired structure
/// where each node contains a [`Cursed`] [`Sequence`].
///
/// [`Cursed`]: trait.Cursed.html
/// [`Sequence`]: trait.Sequence.html
#[derive(Debug, Clone)]
pub struct Chain<C, T> {
    // The head of the chain sequence.
    head: AtomicNodePtr<C, T>,
    // The tail of the chain sequence.
    tail: AtomicNodePtr<C, T>,
}

impl<C, T> Chain<C, T>
where
    C: Bounded<T>,
{
    pub fn new() -> Self {
        Self {
            head: AtomicNodePtr::null(),
            tail: AtomicNodePtr::null(),
        }
    }

    pub fn push_front(&self, data: C) {
        Link::inject_fn(data, || Link::new(&self, None, self.head.to_node_ref()))
    }

    pub fn push_back(&self, data: C) {
        Link::inject_fn(data, || Link::new(&self, self.tail.to_node_ref(), None))
    }

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
        // Empty nodes end up at the end of the chain
        if let Some(at) = data.head() {
            Link::inject_fn(data, || {
                let node = NodeIter::new(self.head.to_node_ref()).find(|node| {
                    node.data()
                        .head()
                        .map(|head| at.as_ptr() >= head.as_ptr())
                        .unwrap_or(true)
                });
                Link::with_right_of(&self, node)
            });
        } else {
            self.push_back(data)
        }
    }
}

unsafe impl<C, T> Cursed<T> for Chain<C, T>
where
    C: Bounded<T>,
{
    type Cursor = ChainCursor<C, T>;

    fn is_owner(&self, _cursor: &Self::Cursor) -> bool {
        // TODO
        unimplemented!()
    }
}

impl<C, T> Sequence<T> for Chain<C, T>
where
    C: Bounded<T>,
{
    fn next(&self, cursor: Self::Cursor) -> Option<Self::Cursor> {
        cursor.next()
    }

    fn prev(&self, cursor: Self::Cursor) -> Option<Self::Cursor> {
        cursor.prev()
    }

    fn remaining(&self, _cursor: &Self::Cursor) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl<C, T> Bounded<T> for Chain<C, T>
where
    C: Bounded<T>,
{
    fn len(&self) -> usize {
        unimplemented!()
    }

    fn is_empty(&self) -> bool {
        unimplemented!()
    }

    fn head(&self) -> Option<Self::Cursor> {
        ChainCursor::from_atomic_ptr(&self.head)
    }

    fn tail(&self) -> Option<Self::Cursor> {
        ChainCursor::from_atomic_ptr(&self.tail)
    }

    fn at(&self, _offset: usize) -> Option<Self::Cursor> {
        unimplemented!()
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
    //     let left = right.as_ref().and_then(|right| right.prev_node());
    //     Self::new(chain, left, right)
    // }

    pub fn with_right_of(chain: &'a Chain<C, T>, left: Option<NodeRef<C, T>>) -> Self {
        let right = left.as_ref().and_then(|left| left.next_node());
        Self::new(chain, left, right)
    }

    fn inject_fn<F>(data: C, mut f: F)
    where
        F: FnMut() -> Self,
    {
        // Create our node for insertion.
        let mut node = Box::new(Node::<C, T>::new(data).init_insert());
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
            Some(left) => (left.as_ptr().as_ptr(), &left.as_ref().next),
            None => (0 as _, &self.chain.head),
        };
        let (right_ptr, right_prev) = match self.right.as_ref() {
            Some(right) => (right.as_ptr().as_ptr(), &right.as_ref().prev),
            None => (0 as _, &self.chain.tail),
        };
        unsafe {
            new_node.set_prev_next(left_ptr, right_ptr);
            let new_node = Box::into_raw(new_node);
            if left_next
                .compare_exchange(right_ptr, new_node, Ordering::Acquire, Ordering::Relaxed)
                .is_err()
            {
                let new_node = Box::from_raw(new_node);
                return Err(new_node);
            }
            right_prev.store(new_node, Ordering::Release);
        }
        Ok(())
    }
}

///////////////////////////////////////////////////////////////////////////////

/// A [`Cursor`] for a [`Chain`] structure.
pub struct ChainCursor<C, T>
where
    C: Bounded<T>,
{
    node: NodeRef<C, T>,
    node_cursor: C::Cursor,
}

impl<C, T> ChainCursor<C, T>
where
    C: Bounded<T>,
{
    fn from_atomic_ptr(node: &AtomicNodePtr<C, T>) -> Option<Self> {
        node.to_node_ref().and_then(Self::from_node_ref)
    }

    fn from_node_ref(node: NodeRef<C, T>) -> Option<Self> {
        node.data()
            .head()
            .map(|node_cursor| Self { node, node_cursor })
    }

    fn next(self) -> Option<Self> {
        let node = self.node.as_ref();
        match node.data.next(self.node_cursor) {
            None => Self::from_atomic_ptr(&node.next),
            Some(node_cursor) => Some(Self {
                node_cursor,
                ..self
            }),
        }
    }

    fn prev(self) -> Option<Self> {
        let node = self.node.as_ref();
        match node.data.prev(self.node_cursor) {
            None => Self::from_atomic_ptr(&node.prev),
            Some(node_cursor) => Some(Self {
                node_cursor,
                ..self
            }),
        }
    }
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

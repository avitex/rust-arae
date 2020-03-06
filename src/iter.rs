use crate::{Cursor, Ring};

/// A `Ring` element `Iterator` that returns a reference to the
/// element and a `Cursor` that points to it.
#[derive(Debug)]
pub struct Iter<'a, T> {
    cur: Cursor<T>,
    ring: &'a Ring<T>,
}

impl<'a, T> Iter<'a, T> {
    pub(crate) fn new(ring: &'a Ring<T>, cur: Cursor<T>) -> Self {
        Self { cur, ring }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (&'a T, Cursor<T>);

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.ring.len(), None)
    }

    fn next(&mut self) -> Option<Self::Item> {
        let curr_cursor = self.cur;
        self.cur = self.ring.next(curr_cursor);
        let elem = self.ring.get(curr_cursor);
        Some((elem, curr_cursor))
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let curr_cursor = self.cur;
        self.cur = self.ring.prev(curr_cursor);
        let elem = self.ring.get(curr_cursor);
        Some((elem, curr_cursor))
    }
}

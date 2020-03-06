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

// TODO: impl DoubleEndedIterator
impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (&'a T, Cursor<T>);

    fn next(&mut self) -> Option<Self::Item> {
        let curr_cursor = self.cur;
        self.cur = self.ring.next(curr_cursor);
        let elem = self.ring.get(curr_cursor);
        Some((elem, curr_cursor))
    }
}

/// A `Ring` element `Iterator` that returns a mutable reference to the
/// element and a `Cursor` that points to it.
pub struct IterMut<'a, T> {
    cur: Cursor<T>,
    ring: &'a mut Ring<T>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = (&'a mut T, Cursor<T>);

    fn next(&mut self) -> Option<Self::Item> {
        let curr_cursor = self.cur;
        self.cur = self.ring.next(curr_cursor);
        let elem_mut = self.ring.get_mut(curr_cursor);
        // as ring is mutably borrowed with the lifetime 'a
        // for this iterator, we can safely return a single
        // mut reference bound to the lifetime 'a to data inside.
        let elem_mut = unsafe { &mut *(elem_mut as *mut T) };
        Some((elem_mut, curr_cursor))
    }
}

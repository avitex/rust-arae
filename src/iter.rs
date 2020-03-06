use crate::{Cursor, Ring};

/// A `Ring` element `Iterator` that returns a reference to the
/// element and a `Cursor` that points to it.
pub struct Iter<'a, T> {
    cur: Cursor<T>,
    ring: &'a Ring<T>,
}

// TODO: impl DoubleEndedIterator

impl<'a, T> Iter<'a, T> {
    pub(crate) fn new(ring: &'a Ring<T>, cur: Cursor<T>) -> Self {
        Self { cur, ring }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (&'a T, Cursor<T>);

    fn next(&mut self) -> Option<Self::Item> {
        self.cur = self.ring.advance(self.cur);
        let elem = self.ring.get(self.cur);
        Some((elem, self.cur))
    }
}

// /// A `Ring` element `Iterator` that returns a mutable reference to the
// /// element and a `Cursor` that points to it.
// pub struct IterMut<'a, T> {
//     cur: Cursor<T>,
//     ring: &'a mut Ring<T>,
// }

// impl<'a, T> Iterator for IterMut<'a, T> {
//     type Item = (&'a mut T, Cursor<T>);

//     fn next(&mut self) -> Option<Self::Item> {
//         self.cur = self.ring.advance(self.cur);
//         let elem = self.ring.get_mut(self.cur);
//         Some((elem, self.cur))
//     }
// }

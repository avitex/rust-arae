use crate::{Cursed, Bounded, CursedExt, Cursor};

/// A `Cursed` element `Iterator` that returns a reference to the
/// element and a `Cursor` that points to it.
#[derive(Debug)]
pub struct Iter<'a, C, T> {
    cursor: Option<Cursor<T>>,
    cursed: &'a C,
}

impl<'a, C, T> Iter<'a, C, T> {
    /// Construct a new `Iter`.
    pub fn new(cursed: &'a C, cursor: Cursor<T>) -> Self {
        let cursor = Some(cursor);
        Self { cursed, cursor }
    }
}

impl<'a, C, T: 'a> Iterator for Iter<'a, C, T>
where
    C: Cursed<T>,
{
    type Item = (&'a T, Cursor<T>);

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self.cursor {
            Some(cursor) => self.cursed.remaining(cursor),
            None => (0, Some(0)),
        }
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.cursor.map(|curr_cursor| {
            self.cursor = self.cursed.next(curr_cursor);
            let elem = self.cursed.get(curr_cursor);
            (elem, curr_cursor)
        })
    }
}

impl<'a, C, T: 'a> DoubleEndedIterator for Iter<'a, C, T>
where
    C: Cursed<T>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.cursor.map(|curr_cursor| {
            self.cursor = self.cursed.prev(curr_cursor);
            let elem = self.cursed.get(curr_cursor);
            (elem, curr_cursor)
        })
    }
}

///////////////////////////////////////////////////////////////////////////////
// WrappingIter

/// A never ending `Cursed` element `Iterator` that returns a reference to the
/// element and a `Cursor` that points to it.
#[derive(Debug)]
pub struct WrappingIter<'a, C, T> {
    cursor: Cursor<T>,
    cursed: &'a C,
}

impl<'a, C, T> WrappingIter<'a, C, T> {
    /// Construct a new `WrappingIter`.
    pub fn new(cursed: &'a C, cursor: Cursor<T>) -> Self {
        Self { cursed, cursor }
    }
}

impl<'a, C, T: 'a> Iterator for WrappingIter<'a, C, T>
where
    C: Bounded<T>,
{
    type Item = (&'a T, Cursor<T>);

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, None)
    }

    fn next(&mut self) -> Option<Self::Item> {
        let curr_cursor = self.cursor;
        self.cursor = self.cursed.wrapping_next(curr_cursor);
        let elem = self.cursed.get(curr_cursor);
        Some((elem, curr_cursor))
    }
}

impl<'a, C, T: 'a> DoubleEndedIterator for WrappingIter<'a, C, T>
where
    C: Bounded<T>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        let curr_cursor = self.cursor;
        self.cursor = self.cursed.wrapping_prev(curr_cursor);
        let elem = self.cursed.get(curr_cursor);
        Some((elem, curr_cursor))
    }
}

//! Iterators for [`Cursed`] types.

use crate::{Bounded, Cursed, CursedExt, Sequence};

/// A [`Sequence`] element `Iterator` that returns a reference to the
/// element and a [`Cursor`] that points to it.
///
/// [`Cursor`]: crate::cursor::Cursor
#[derive(Debug)]
pub struct Iter<'a, C, T>
where
    C: Cursed<T>,
{
    cursor: Option<C::Cursor>,
    cursed: &'a C,
}

impl<'a, C, T> Iter<'a, C, T>
where
    C: Cursed<T>,
{
    /// Construct a new `Iter`.
    pub fn new(cursed: &'a C, cursor: Option<C::Cursor>) -> Self {
        Self { cursed, cursor }
    }
}

impl<'a, C, T: 'a> Iterator for Iter<'a, C, T>
where
    C: Sequence<T>,
{
    type Item = (&'a T, C::Cursor);

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self.cursor.as_ref() {
            Some(cursor) => self.cursed.remaining(cursor),
            None => (0, Some(0)),
        }
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.cursor.take().map(|curr_cursor| {
            self.cursor = self.cursed.next(curr_cursor.clone());
            let elem = self.cursed.get(&curr_cursor);
            (elem, curr_cursor)
        })
    }
}

impl<'a, C, T: 'a> DoubleEndedIterator for Iter<'a, C, T>
where
    C: Sequence<T>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.cursor.take().map(|curr_cursor| {
            self.cursor = self.cursed.prev(curr_cursor.clone());
            let elem = self.cursed.get(&curr_cursor);
            (elem, curr_cursor)
        })
    }
}

///////////////////////////////////////////////////////////////////////////////
// WrappingIter

/// A cyclic [`Bounded`] element `Iterator` that returns a reference to the
/// element and a [`Cursor`] that points to it.
///
/// [`Cursor`]: crate::cursor::Cursor
#[derive(Debug)]
pub struct WrappingIter<'a, C, T>
where
    C: Cursed<T>,
{
    cursor: Option<C::Cursor>,
    cursed: &'a C,
}

impl<'a, C, T> WrappingIter<'a, C, T>
where
    C: Cursed<T>,
{
    /// Construct a new `WrappingIter`.
    pub fn new(cursed: &'a C, cursor: Option<C::Cursor>) -> Self {
        Self { cursed, cursor }
    }
}

impl<'a, C, T: 'a> Iterator for WrappingIter<'a, C, T>
where
    C: Bounded<T>,
{
    type Item = (&'a T, C::Cursor);

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, None)
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.cursor.map(|cursor| {
            let curr_cursor = cursor.clone();
            self.cursor = Some(self.cursed.wrapping_next(curr_cursor.clone()));
            let elem = self.cursed.get(&curr_cursor);
            (elem, curr_cursor)
        })
    }
}

impl<'a, C, T: 'a> DoubleEndedIterator for WrappingIter<'a, C, T>
where
    C: Bounded<T>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.cursor.map(|cursor| {
            let curr_cursor = cursor.clone();
            self.cursor = Some(self.cursed.wrapping_prev(curr_cursor.clone()));
            let elem = self.cursed.get(&curr_cursor);
            (elem, curr_cursor)
        })
    }
}

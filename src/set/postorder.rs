use std::iter::FusedIterator;

pub struct PostorderIter<'a, T> {
    inner: crate::map::PostorderIter<'a, T, ()>
}

impl<'a, T: Ord> PostorderIter<'a, T> {
    pub(super) fn new(map: &'a crate::map::BSTMap<T, ()>) -> Self {
        Self {
            inner: map.iter_postorder(),
        }
    }
}

impl<'a, T> Iterator for PostorderIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(value, ())| value)
    }
}

impl<'a, T> FusedIterator for PostorderIter<'a, T> {}

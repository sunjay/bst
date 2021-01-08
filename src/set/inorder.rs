use std::iter::FusedIterator;

pub struct InorderIter<'a, T> {
    inner: crate::map::InorderIter<'a, T, ()>
}

impl<'a, T: Ord> InorderIter<'a, T> {
    pub(super) fn new(map: &'a crate::map::BSTMap<T, ()>) -> Self {
        Self {
            inner: map.iter_inorder(),
        }
    }
}

impl<'a, T> Iterator for InorderIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(value, ())| value)
    }
}

impl<'a, T> FusedIterator for InorderIter<'a, T> {}

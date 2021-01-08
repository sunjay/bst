use std::iter::FusedIterator;

pub struct PreorderIter<'a, T> {
    inner: crate::map::PreorderIter<'a, T, ()>
}

impl<'a, T: Ord> PreorderIter<'a, T> {
    pub(super) fn new(map: &'a crate::map::BSTMap<T, ()>) -> Self {
        Self {
            inner: map.iter_preorder(),
        }
    }
}

impl<'a, T> Iterator for PreorderIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(value, ())| value)
    }
}

impl<'a, T> FusedIterator for PreorderIter<'a, T> {}

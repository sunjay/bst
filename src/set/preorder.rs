use std::iter::FusedIterator;

pub struct IterPreorder<'a, T> {
    inner: crate::map::IterPreorder<'a, T, ()>
}

impl<'a, T: Ord> IterPreorder<'a, T> {
    pub(super) fn new(map: &'a crate::map::BSTMap<T, ()>) -> Self {
        Self {
            inner: map.iter_preorder(),
        }
    }
}

impl<'a, T> Iterator for IterPreorder<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(value, ())| value)
    }
}

impl<'a, T> FusedIterator for IterPreorder<'a, T> {}

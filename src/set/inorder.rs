use std::iter::FusedIterator;

pub struct IterInorder<'a, T> {
    inner: crate::map::IterInorder<'a, T, ()>
}

impl<'a, T: Ord> IterInorder<'a, T> {
    pub(super) fn new(map: &'a crate::map::BSTMap<T, ()>) -> Self {
        Self {
            inner: map.iter_inorder(),
        }
    }
}

impl<'a, T> Iterator for IterInorder<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(value, ())| value)
    }
}

impl<'a, T> FusedIterator for IterInorder<'a, T> {}

use std::iter::FusedIterator;

pub struct IterPostorder<'a, T> {
    inner: crate::map::IterPostorder<'a, T, ()>
}

impl<'a, T: Ord> IterPostorder<'a, T> {
    pub(super) fn new(map: &'a crate::map::SimpleBSTMap<T, ()>) -> Self {
        Self {
            inner: map.iter_postorder(),
        }
    }
}

impl<'a, T> Iterator for IterPostorder<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(value, ())| value)
    }
}

impl<'a, T> FusedIterator for IterPostorder<'a, T> {}

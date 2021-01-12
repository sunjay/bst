use std::iter::FusedIterator;

use super::Node;

pub struct IterPreorder<'a, K, V> {
    stack: Vec<&'a Node<K, V>>,
}

impl<'a, K, V> IterPreorder<'a, K, V> {
    pub(super) fn new(root: Option<&'a Node<K, V>>) -> Self {
        Self {
            stack: root.into_iter().collect(),
        }
    }
}

// See: https://www.geeksforgeeks.org/iterative-preorder-traversal/
impl<'a, K, V> Iterator for IterPreorder<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.stack.pop()?;
        self.stack.extend(node.right());
        self.stack.extend(node.left());
        Some((node.key(), node.value()))
    }
}

impl<'a, K, V> FusedIterator for IterPreorder<'a, K, V> {}

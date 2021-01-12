use std::iter::FusedIterator;

use super::Node;

pub struct IterInorder<'a, K, V> {
    stack: Vec<&'a Node<K, V>>,
}

// See: https://www.geeksforgeeks.org/inorder-tree-traversal-without-recursion/
impl<'a, K, V> IterInorder<'a, K, V> {
    pub(super) fn new(root: Option<&'a Node<K, V>>) -> Self {
        let mut stack = Vec::new();
        let mut current = root;
        while let Some(current_node) = current {
            stack.push(current_node);
            current = current_node.left();
        }

        Self {stack}
    }
}

// See: https://www.geeksforgeeks.org/inorder-tree-traversal-without-recursion/
impl<'a, K, V> Iterator for IterInorder<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.stack.pop()?;

        let mut current = node.right();
        while let Some(current_node) = current {
            self.stack.push(current_node);
            current = current_node.left();
        }

        Some((node.key(), node.value()))
    }
}

impl<'a, K, V> FusedIterator for IterInorder<'a, K, V> {}

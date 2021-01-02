use std::iter::FusedIterator;

use super::{InnerNode, index::NodeIndex};

pub struct InorderIter<'a, K, V> {
    nodes: &'a [InnerNode<K, V>],
    stack: Vec<usize>,
}

// See: https://www.geeksforgeeks.org/inorder-tree-traversal-without-recursion/
impl<'a, K, V> InorderIter<'a, K, V> {
    pub(super) fn new(nodes: &'a [InnerNode<K, V>], root: NodeIndex) -> Self {
        let mut stack = Vec::new();
        let mut current = root.into_index();
        while let Some(index) = current {
            stack.push(index);
            // Safety: Nodes contain indexes to other valid nodes in `nodes`
            let current_node = unsafe { nodes.get_unchecked(index) };
            current = current_node.left.into_index();
        }

        Self {nodes, stack}
    }
}

// See: https://www.geeksforgeeks.org/inorder-tree-traversal-without-recursion/
impl<'a, K, V> Iterator for InorderIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let top_index = self.stack.pop()?;
        // Safety: any indexes added to the stack are valid in `self.nodes`
        let node = unsafe { self.nodes.get_unchecked(top_index) };

        let mut current = node.right.into_index();
        while let Some(index) = current {
            self.stack.push(index);
            // Safety: Nodes contain indexes to other valid nodes in `nodes`
            let current_node = unsafe { self.nodes.get_unchecked(index) };
            current = current_node.left.into_index();
        }

        Some((&node.key, &node.value))
    }
}

impl<'a, K, V> ExactSizeIterator for InorderIter<'a, K, V> {
    fn len(&self) -> usize {
        self.nodes.len()
    }
}

impl<'a, K, V> FusedIterator for InorderIter<'a, K, V> {}

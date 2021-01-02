use std::iter::FusedIterator;

use super::{InnerNode, index::NodeIndex};

pub struct PreorderIter<'a, K, V> {
    nodes: &'a [InnerNode<K, V>],
    stack: Vec<usize>,
}

impl<'a, K, V> PreorderIter<'a, K, V> {
    pub(super) fn new(nodes: &'a [InnerNode<K, V>], root: NodeIndex) -> Self {
        Self {
            nodes,
            stack: root.into_index().into_iter().collect(),
        }
    }
}

// See: https://www.geeksforgeeks.org/iterative-preorder-traversal/
impl<'a, K, V> Iterator for PreorderIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let top_index = self.stack.pop()?;
        // Safety: any indexes added to the stack are valid in `self.nodes`
        let node = unsafe { self.nodes.get_unchecked(top_index) };
        self.stack.extend(node.right.into_index());
        self.stack.extend(node.left.into_index());
        Some((&node.key, &node.value))
    }
}

impl<'a, K, V> FusedIterator for PreorderIter<'a, K, V> {}

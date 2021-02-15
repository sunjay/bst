use std::iter::FusedIterator;

use crate::slab::{Ptr, UnsafeSlab};

use super::InnerNode;

pub struct IterPreorder<'a, K, V> {
    nodes: &'a UnsafeSlab<InnerNode<K, V>>,
    stack: Vec<Ptr>,
}

impl<'a, K, V> IterPreorder<'a, K, V> {
    pub(super) fn new(nodes: &'a UnsafeSlab<InnerNode<K, V>>, root: Option<Ptr>) -> Self {
        Self {
            nodes,
            stack: root.into_iter().collect(),
        }
    }
}

// See: https://www.geeksforgeeks.org/iterative-preorder-traversal/
impl<'a, K, V> Iterator for IterPreorder<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let top_ptr = self.stack.pop()?;
        // Safety: any pointers added to the stack are valid in `self.nodes`
        let node = unsafe { self.nodes.get_unchecked(top_ptr) };
        self.stack.extend(node.right);
        self.stack.extend(node.left);
        Some((&node.key, &node.value))
    }
}

impl<'a, K, V> FusedIterator for IterPreorder<'a, K, V> {}

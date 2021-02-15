use std::iter::FusedIterator;

use crate::slab::{Ptr, UnsafeSlab};

use super::InnerNode;

pub struct IterInorder<'a, K, V> {
    nodes: &'a UnsafeSlab<InnerNode<K, V>>,
    stack: Vec<Ptr>,
}

// See: https://www.geeksforgeeks.org/inorder-tree-traversal-without-recursion/
impl<'a, K, V> IterInorder<'a, K, V> {
    pub(super) fn new(nodes: &'a UnsafeSlab<InnerNode<K, V>>, root: Option<Ptr>) -> Self {
        let mut stack = Vec::new();
        let mut current = root;
        while let Some(ptr) = current {
            stack.push(ptr);
            // Safety: Nodes contain pointers to other valid nodes in `nodes`
            let current_node = unsafe { nodes.get_unchecked(ptr) };
            current = current_node.left;
        }

        Self {nodes, stack}
    }
}

// See: https://www.geeksforgeeks.org/inorder-tree-traversal-without-recursion/
impl<'a, K, V> Iterator for IterInorder<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let top_ptr = self.stack.pop()?;
        // Safety: any pointers added to the stack are valid in `self.nodes`
        let node = unsafe { self.nodes.get_unchecked(top_ptr) };

        let mut current = node.right;
        while let Some(ptr) = current {
            self.stack.push(ptr);
            // Safety: Nodes contain pointers to other valid nodes in `nodes`
            let current_node = unsafe { self.nodes.get_unchecked(ptr) };
            current = current_node.left;
        }

        Some((&node.key, &node.value))
    }
}

impl<'a, K, V> FusedIterator for IterInorder<'a, K, V> {}

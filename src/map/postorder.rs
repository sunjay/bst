use std::iter::FusedIterator;

use crate::slab::UnsafeSlab;

use super::{InnerNode, index::NodeIndex};

pub struct IterPostorder<'a, K, V> {
    nodes: &'a UnsafeSlab<InnerNode<K, V>>,
    stack: Vec<usize>,
}

// See: https://www.geeksforgeeks.org/iterative-postorder-traversal-using-stack/
impl<'a, K, V> IterPostorder<'a, K, V> {
    pub(super) fn new(nodes: &'a UnsafeSlab<InnerNode<K, V>>, root: NodeIndex) -> Self {
        let mut stack = Vec::new();
        let mut current = root.into_index();
        while let Some(index) = current {
            // Safety: Nodes contain indexes to other valid nodes in `nodes`
            let current_node = unsafe { nodes.get_unchecked(index) };

            stack.extend(current_node.right.into_index());
            stack.push(index);

            current = current_node.left.into_index();
        }

        Self {nodes, stack}
    }
}

// See: https://www.geeksforgeeks.org/iterative-postorder-traversal-using-stack/
impl<'a, K, V> Iterator for IterPostorder<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(mut current_index) = self.stack.pop() {
            // Safety: any indexes added to the stack are valid in `self.nodes`
            let mut node = unsafe { self.nodes.get_unchecked(current_index) };

            // If the top of the stack is the current node's right child
            match node.right.into_index() {
                Some(right) if self.stack.last().copied() == Some(right) => {
                    // Remove right from stack
                    self.stack.pop();

                    // Push the current index back onto the stack
                    self.stack.push(current_index);

                    current_index = right;
                    // Safety: any indexes added to the stack are valid in `self.nodes`
                    node = unsafe { self.nodes.get_unchecked(current_index) };
                },

                _ => return Some((&node.key, &node.value)),
            }

            loop {
                self.stack.extend(node.right.into_index());
                self.stack.push(current_index);

                match node.left.into_index() {
                    Some(index) => {
                        current_index = index;
                        // Safety: any indexes added to the stack are valid in `self.nodes`
                        node = unsafe { self.nodes.get_unchecked(current_index) };
                    },

                    None => break,
                }
            }
        }

        None
    }
}

impl<'a, K, V> FusedIterator for IterPostorder<'a, K, V> {}

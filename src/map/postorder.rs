use std::iter::FusedIterator;

use crate::slab::{Ptr, UnsafeSlab};

use super::InnerNode;

pub struct IterPostorder<'a, K, V> {
    nodes: &'a UnsafeSlab<InnerNode<K, V>>,
    stack: Vec<Ptr>,
}

// See: https://www.geeksforgeeks.org/iterative-postorder-traversal-using-stack/
impl<'a, K, V> IterPostorder<'a, K, V> {
    pub(super) fn new(nodes: &'a UnsafeSlab<InnerNode<K, V>>, root: Option<Ptr>) -> Self {
        let mut stack = Vec::new();
        let mut current = root;
        while let Some(ptr) = current {
            // Safety: Nodes contain pointers to other valid nodes in `nodes`
            let current_node = unsafe { nodes.get_unchecked(ptr) };

            stack.extend(current_node.right);
            stack.push(ptr);

            current = current_node.left;
        }

        Self {nodes, stack}
    }
}

// See: https://www.geeksforgeeks.org/iterative-postorder-traversal-using-stack/
impl<'a, K, V> Iterator for IterPostorder<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(mut current_ptr) = self.stack.pop() {
            // Safety: any pointers added to the stack are valid in `self.nodes`
            let mut node = unsafe { self.nodes.get_unchecked(current_ptr) };

            // If the top of the stack is the current node's right child
            match node.right {
                Some(right) if self.stack.last().copied() == Some(right) => {
                    // Remove right from stack
                    self.stack.pop();

                    // Push the current pointer back onto the stack
                    self.stack.push(current_ptr);

                    current_ptr = right;
                    // Safety: any pointers added to the stack are valid in `self.nodes`
                    node = unsafe { self.nodes.get_unchecked(current_ptr) };
                },

                _ => return Some((&node.key, &node.value)),
            }

            loop {
                self.stack.extend(node.right);
                self.stack.push(current_ptr);

                match node.left {
                    Some(ptr) => {
                        current_ptr = ptr;
                        // Safety: any pointers added to the stack are valid in `self.nodes`
                        node = unsafe { self.nodes.get_unchecked(current_ptr) };
                    },

                    None => break,
                }
            }
        }

        None
    }
}

impl<'a, K, V> FusedIterator for IterPostorder<'a, K, V> {}

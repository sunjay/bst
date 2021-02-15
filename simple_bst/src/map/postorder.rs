use std::ptr;
use std::iter::FusedIterator;

use super::Node;

pub struct IterPostorder<'a, K, V> {
    stack: Vec<&'a Node<K, V>>,
}

// See: https://www.geeksforgeeks.org/iterative-postorder-traversal-using-stack/
impl<'a, K, V> IterPostorder<'a, K, V> {
    pub(super) fn new(root: Option<&'a Node<K, V>>) -> Self {
        let mut stack = Vec::new();
        let mut current = root;
        while let Some(current_node) = current {
            stack.extend(current_node.right());
            stack.push(current_node);

            current = current_node.left();
        }

        Self {stack}
    }
}

/// Compares two nodes for equality using pointer equality only
fn node_eq<K, V>(left: Option<&&Node<K, V>>, right: &Node<K, V>) -> bool {
    left.map(|&left| ptr::eq(left, right))
        // default to not equal
        .unwrap_or(false)
}

// See: https://www.geeksforgeeks.org/iterative-postorder-traversal-using-stack/
impl<'a, K, V> Iterator for IterPostorder<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(mut node) = self.stack.pop() {
            // If the top of the stack is the current node's right child
            match node.right() {
                Some(right) if node_eq(self.stack.last(), right) => {
                    // Remove right from stack
                    self.stack.pop();

                    // Push the current node back onto the stack
                    self.stack.push(node);

                    node = right;
                },

                _ => return Some((node.key(), node.value())),
            }

            loop {
                self.stack.extend(node.right());
                self.stack.push(node);

                match node.left() {
                    Some(left) => {
                        node = left;
                    },

                    None => break,
                }
            }
        }

        None
    }
}

impl<'a, K, V> FusedIterator for IterPostorder<'a, K, V> {}

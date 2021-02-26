use std::iter::FusedIterator;
use std::marker::PhantomData;

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

pub struct IterMutPreorder<'a, K, V> {
    nodes: *mut UnsafeSlab<InnerNode<K, V>>,
    stack: Vec<Ptr>,
    _marker: PhantomData<&'a mut UnsafeSlab<InnerNode<K, V>>>,
}

impl<'a, K, V> IterMutPreorder<'a, K, V> {
    pub(super) fn new(nodes: &'a mut UnsafeSlab<InnerNode<K, V>>, root: Option<Ptr>) -> Self {
        Self {
            nodes,
            stack: root.into_iter().collect(),
            _marker: PhantomData,
        }
    }
}

// See: https://www.geeksforgeeks.org/iterative-preorder-traversal/
impl<'a, K, V> Iterator for IterMutPreorder<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        let top_ptr = self.stack.pop()?;

        // Safety: `nodes` was created from a valid &mut reference, so it is safe to dereference
        //   here. Since trees don't have cycles, we only access unique elements of `nodes`. We will
        //   never yield two mutable references to the same memory.
        let nodes = unsafe { &mut *self.nodes };

        // Safety: any pointers added to the stack are valid in `self.nodes`
        let node = unsafe { nodes.get_unchecked_mut(top_ptr) };
        self.stack.extend(node.right);
        self.stack.extend(node.left);

        Some((&node.key, &mut node.value))
    }
}

impl<'a, K, V> FusedIterator for IterMutPreorder<'a, K, V> {}

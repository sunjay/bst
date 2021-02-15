use std::ptr;
use std::mem;
use std::fmt;

use crate::slab::{Ptr, UnsafeSlab};

use super::InnerNode;

/// A single node of the binary search tree
pub struct Node<'a, K, V> {
    nodes: &'a UnsafeSlab<InnerNode<K, V>>,
    /// A pointer into `nodes` for the node represented by this struct
    ///
    /// Guaranteed to be a valid pointer
    ptr: Ptr,
}

impl<'a, K, V> fmt::Debug for Node<'a, K, V>
    where K: fmt::Debug,
          V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Node")
            .field("key", self.key())
            .field("value", self.value())
            .field("left", &self.left())
            .field("right", &self.right())
            .finish()
    }
}

impl<'a, K, V> Clone for Node<'a, K, V> {
    fn clone(&self) -> Self {
        Self {..*self}
    }
}

impl<'a, K: PartialEq, V: PartialEq> PartialEq for Node<'a, K, V> {
    fn eq(&self, other: &Self) -> bool {
        // No need to check `left()` or `right()` since trees do not have cycles in them, you cannot
        // have two different nodes with the same `left()` and `right()` nodes. That is, if the keys
        // are different, the `self.left() == other.left()` and `self.right() == other.right()` will
        // be false.

        // If the pointers are the same, the values are guaranteed to be equal (similar to `Arc`
        // using `ptr_eq` to optimize its `PartialEq` impl)
        let ptr_eq = ptr::eq(self.nodes, other.nodes) && self.ptr == other.ptr;
        ptr_eq || (self.key().eq(other.key()) && self.value().eq(other.value()))
    }
}

impl<'a, K: Eq, V: Eq> Eq for Node<'a, K, V> {}

impl<'a, K, V> Node<'a, K, V> {
    /// Creates a new `Node`
    ///
    /// # Safety
    ///
    /// Must guarantee that `ptr` represents a valid pointer into `nodes`.
    pub(super) unsafe fn new(nodes: &'a UnsafeSlab<InnerNode<K, V>>, ptr: Ptr) -> Self {
        Self {nodes, ptr}
    }

    /// Returns the key of this node
    pub fn key(&self) -> &'a K {
        &self.node().key
    }

    /// Returns the value of this node
    pub fn value(&self) -> &'a V {
        &self.node().value
    }

    /// Returns true if this node has a left subtree
    pub fn has_left(&self) -> bool {
        self.node().left.is_some()
    }

    /// Returns true if this node has a right subtree
    pub fn has_right(&self) -> bool {
        self.node().right.is_some()
    }

    /// Returns the left child node (subtree) of this node, if any
    pub fn left(&self) -> Option<Self> {
        // Safety: Nodes only contain pointers to other nodes within `self.nodes`
        self.node().left.map(|ptr| unsafe { Self::new(self.nodes, ptr) })
    }

    /// Returns the right child node (subtree) of this node, if any
    pub fn right(&self) -> Option<Self> {
        // Safety: Nodes only contain pointers to other nodes within `self.nodes`
        self.node().right.map(|ptr| unsafe { Self::new(self.nodes, ptr) })
    }

    fn node(&self) -> &'a InnerNode<K, V> {
        // Safety: `self.ptr` is guaranteed to be a valid pointer
        unsafe { self.nodes.get_unchecked(self.ptr) }
    }
}

/// A single mutable node of the binary search tree
///
/// Note that only the value is mutable, not the key since modifying the key
/// could result in invalidating the ordering properties.
pub struct NodeMut<'a, K, V> {
    nodes: &'a mut UnsafeSlab<InnerNode<K, V>>,
    /// A pointer into `nodes` for the node represented by this struct
    ///
    /// Guaranteed to be a valid pointer
    ptr: Ptr,
}

impl<'a, K, V> fmt::Debug for NodeMut<'a, K, V>
    where K: fmt::Debug,
          V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("NodeMut")
            .field("key", self.key())
            .field("value", self.value())
            .field("left", &"...")
            .field("right", &"...")
            .finish()
    }
}

impl<'a, K: PartialEq, V: PartialEq> PartialEq for NodeMut<'a, K, V> {
    fn eq(&self, other: &Self) -> bool {
        // No need to check `left()` or `right()` since trees do not have cycles in them, you cannot
        // have two different nodes with the same `left()` and `right()` nodes. That is, if the keys
        // are different, the `self.left() == other.left()` and `self.right() == other.right()` will
        // be false.

        // If the pointers are the same, the values are guaranteed to be equal (similar to `Arc`
        // using `ptr_eq` to optimize its `PartialEq` impl)
        let ptr_eq = ptr::eq(self.nodes, other.nodes) && self.ptr == other.ptr;
        ptr_eq || (self.key().eq(other.key()) && self.value().eq(other.value()))
    }
}

impl<'a, K: Eq, V: Eq> Eq for NodeMut<'a, K, V> {}

impl<'a, K, V> NodeMut<'a, K, V> {
    /// Creates a new `NodeMut`
    ///
    /// # Safety
    ///
    /// Must guarantee that `ptr` represents a valid pointer into `nodes`.
    pub(super) unsafe fn new(nodes: &'a mut UnsafeSlab<InnerNode<K, V>>, ptr: Ptr) -> Self {
        Self {nodes, ptr}
    }

    /// Returns the key of this node
    pub fn key(&'a self) -> &'a K {
        &self.node().key
    }

    /// Returns the value of this node
    pub fn value(&'a self) -> &'a V {
        &self.node().value
    }

    /// Returns the value of this node
    pub fn value_mut(&'a mut self) -> &'a mut V {
        &mut self.node_mut().value
    }

    /// Returns the value of this node, consuming the node in the process
    pub fn into_value_mut(self) -> &'a mut V {
        let node = unsafe { self.nodes.get_unchecked_mut(self.ptr) };
        &mut node.value
    }

    /// Returns true if this node has a left subtree
    pub fn has_left(&self) -> bool {
        self.node().left.is_some()
    }

    /// Returns true if this node has a right subtree
    pub fn has_right(&self) -> bool {
        self.node().right.is_some()
    }

    /// Returns the left child node (subtree) of this node, if any
    pub fn left(self) -> Option<Self> {
        // Safety: Nodes only contain pointers to other nodes within `self.nodes`
        self.node().left.map(move |ptr| unsafe { Self::new(self.nodes, ptr) })
    }

    /// Returns the right child node (subtree) of this node, if any
    pub fn right(self) -> Option<Self> {
        // Safety: Nodes only contain pointers to other nodes within `self.nodes`
        self.node().right.map(move |ptr| unsafe { Self::new(self.nodes, ptr) })
    }

    /// Private API for updating the left subtree of this node
    pub(crate) fn set_left(&'a mut self, ptr: Ptr) {
        self.node_mut().left = Some(ptr);
    }

    /// Private API for updating the right subtree of this node
    pub(crate) fn set_right(&'a mut self, ptr: Ptr) {
        self.node_mut().right = Some(ptr);
    }

    /// Private API for pushing a new node and assigning the left subtree
    /// of this node
    pub(crate) fn push_left(&'a mut self, key: K, value: V) -> Ptr {
        let ptr = self.nodes.push(InnerNode::new(key, value));
        self.set_left(ptr);
        ptr
    }

    /// Private API for pushing a new node and assigning the right subtree
    /// of this node
    pub(crate) fn push_right(&'a mut self, key: K, value: V) -> Ptr {
        let ptr = self.nodes.push(InnerNode::new(key, value));
        self.set_right(ptr);
        ptr
    }

    /// Private API for replacing the value of this node and returning the
    /// previous value
    pub(crate) fn replace_value(&'a mut self, value: V) -> V {
        mem::replace(self.value_mut(), value)
    }

    fn node(&'a self) -> &'a InnerNode<K, V> {
        // Safety: `self.ptr` is guaranteed to be a valid pointer
        unsafe { self.nodes.get_unchecked(self.ptr) }
    }

    fn node_mut(&'a mut self) -> &'a mut InnerNode<K, V> {
        // Safety: `self.ptr` is guaranteed to be a valid pointer
        unsafe { self.nodes.get_unchecked_mut(self.ptr) }
    }
}

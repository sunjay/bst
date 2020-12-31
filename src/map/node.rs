use std::mem;
use std::fmt;

use super::{InnerNode, index::NodeIndex, push_node};

/// A single node of the binary search tree
#[derive(Clone, PartialEq, Eq)]
pub struct BSTNode<'a, K, V> {
    nodes: &'a [InnerNode<K, V>],
    /// An index into `nodes` for the node represented by this struct
    ///
    /// Guaranteed to be a valid index
    index: usize,
}

impl<'a, K, V> fmt::Debug for BSTNode<'a, K, V>
    where K: Ord + fmt::Debug,
          V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BSTNode")
            .field("key", self.key())
            .field("value", self.value())
            .field("left", &self.left())
            .field("right", &self.right())
            .finish()
    }
}

impl<'a, K: Ord, V> BSTNode<'a, K, V> {
    /// Creates a new `BSTNode`
    ///
    /// # Safety
    ///
    /// Must guarantee that `index` represents a valid index into `nodes`.
    pub(super) unsafe fn new(nodes: &'a [InnerNode<K, V>], index: NodeIndex) -> Option<Self> {
        index.into_index().map(|index| Self {nodes, index})
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
        !self.node().left.is_none()
    }

    /// Returns true if this node has a right subtree
    pub fn has_right(&self) -> bool {
        !self.node().right.is_none()
    }

    /// Returns the left child node (subtree) of this node, if any
    pub fn left(&self) -> Option<Self> {
        // Safety: Nodes only contain indexes to other nodes within `self.nodes`
        unsafe { Self::new(self.nodes, self.node().left) }
    }

    /// Returns the right child node (subtree) of this node, if any
    pub fn right(&self) -> Option<Self> {
        // Safety: Nodes only contain indexes to other nodes within `self.nodes`
        unsafe { Self::new(self.nodes, self.node().right) }
    }

    fn node(&self) -> &'a InnerNode<K, V> {
        // Safety: `self.index` is guaranteed to be a valid index
        unsafe { self.nodes.get_unchecked(self.index) }
    }
}

/// A single mutable node of the binary search tree
///
/// Note that only the value is mutable, not the key since modifying the key
/// could result in invalidating the ordering properties.
#[derive(PartialEq, Eq)]
pub struct BSTNodeMut<'a, K, V> {
    nodes: &'a mut Vec<InnerNode<K, V>>,
    /// An index into `nodes` for the node represented by this struct
    ///
    /// Guaranteed to be a valid index
    index: usize,
}

impl<'a, K, V> fmt::Debug for BSTNodeMut<'a, K, V>
    where K: Ord + fmt::Debug,
          V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BSTNode")
            .field("key", self.key())
            .field("value", self.value())
            .field("left", &"...")
            .field("right", &"...")
            .finish()
    }
}

impl<'a, K: Ord, V> BSTNodeMut<'a, K, V> {
    /// Creates a new `BSTNodeMut`
    ///
    /// # Safety
    ///
    /// Must guarantee that `index` represents a valid index into `nodes`.
    pub(super) unsafe fn new(nodes: &'a mut Vec<InnerNode<K, V>>, index: NodeIndex) -> Option<Self> {
        index.into_index().map(move |index| Self {nodes, index})
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
        let node = unsafe { self.nodes.get_unchecked_mut(self.index) };
        &mut node.value
    }

    /// Returns true if this node has a left subtree
    pub fn has_left(&self) -> bool {
        !self.node().left.is_none()
    }

    /// Returns true if this node has a right subtree
    pub fn has_right(&self) -> bool {
        !self.node().right.is_none()
    }

    /// Returns the left child node (subtree) of this node, if any
    pub fn left(self) -> Option<Self> {
        // Safety: Nodes only contain indexes to other nodes within `self.nodes`
        unsafe { Self::new(self.nodes, self.node().left) }
    }

    /// Returns the right child node (subtree) of this node, if any
    pub fn right(self) -> Option<Self> {
        // Safety: Nodes only contain indexes to other nodes within `self.nodes`
        unsafe { Self::new(self.nodes, self.node().right) }
    }

    /// Private API for updating the left subtree of this node
    pub(crate) fn set_left(&'a mut self, index: NodeIndex) {
        self.node_mut().left = index;
    }

    /// Private API for updating the right subtree of this node
    pub(crate) fn set_right(&'a mut self, index: NodeIndex) {
        self.node_mut().right = index;
    }

    /// Private API for pushing a new node and assigning the left subtree
    /// of this node
    pub(crate) fn push_left(&'a mut self, key: K, value: V) -> NodeIndex {
        let index = push_node(self.nodes, key, value);
        self.set_left(index);
        index
    }

    /// Private API for pushing a new node and assigning the right subtree
    /// of this node
    pub(crate) fn push_right(&'a mut self, key: K, value: V) -> NodeIndex {
        let index = push_node(self.nodes, key, value);
        self.set_right(index);
        index
    }

    /// Private API for replacing the value of this node and returning the
    /// previous value
    pub(crate) fn replace_value(&'a mut self, value: V) -> V {
        mem::replace(self.value_mut(), value)
    }

    fn node(&'a self) -> &'a InnerNode<K, V> {
        // Safety: `self.index` is guaranteed to be a valid index
        unsafe { self.nodes.get_unchecked(self.index) }
    }

    fn node_mut(&'a mut self) -> &'a mut InnerNode<K, V> {
        // Safety: `self.index` is guaranteed to be a valid index
        unsafe { self.nodes.get_unchecked_mut(self.index) }
    }
}

use std::fmt;

/// A single node of the binary search tree
#[derive(Clone, PartialEq, Eq)]
pub struct Node<'a, T> {
    inner: crate::map::Node<'a, T, ()>,
}

impl<'a, T> fmt::Debug for Node<'a, T>
    where T: Ord + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Node")
            .field("value", self.value())
            .field("left", &self.left())
            .field("right", &self.right())
            .finish()
    }
}

impl<'a, T: Ord> Node<'a, T> {
    /// Creates a new `Node`
    pub(super) fn new(inner: crate::map::Node<'a, T, ()>) -> Self {
        Self {inner}
    }

    /// Returns the value of this node
    pub fn value(&self) -> &'a T {
        self.inner.key()
    }

    /// Returns true if this node has a left subtree
    pub fn has_left(&self) -> bool {
        self.inner.has_left()
    }

    /// Returns true if this node has a right subtree
    pub fn has_right(&self) -> bool {
        self.inner.has_right()
    }

    /// Returns the left child node (subtree) of this node, if any
    pub fn left(&self) -> Option<Self> {
        self.inner.left().map(Self::new)
    }

    /// Returns the right child node (subtree) of this node, if any
    pub fn right(&self) -> Option<Self> {
        self.inner.right().map(Self::new)
    }
}

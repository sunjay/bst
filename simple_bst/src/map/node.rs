use std::mem;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node<K, V> {
    key: K,
    value: V,
    left: Option<Box<Node<K, V>>>,
    right: Option<Box<Node<K, V>>>,
}

impl<K, V> Node<K, V> {
    pub(crate) fn new(key: K, value: V) -> Self {
        Self {
            key,
            value,
            left: None,
            right: None,
        }
    }

    pub(crate) fn into_inner(self) -> (K, V) {
        (self.key, self.value)
    }

    pub fn key(&self) -> &K {
        &self.key
    }

    pub fn value(&self) -> &V {
        &self.value
    }

    pub fn value_mut(&mut self) -> &mut V {
        &mut self.value
    }

    pub fn has_left(&self) -> bool {
        self.left.is_some()
    }

    pub fn has_right(&self) -> bool {
        self.right.is_some()
    }

    pub fn left(&self) -> Option<&Self> {
        self.left.as_deref()
    }

    pub fn right(&self) -> Option<&Self> {
        self.right.as_deref()
    }

    pub fn left_mut(&mut self) -> Option<&mut Self> {
        self.left.as_deref_mut()
    }

    pub fn right_mut(&mut self) -> Option<&mut Self> {
        self.right.as_deref_mut()
    }

    pub(crate) fn take_left(&mut self) -> Option<Self> {
        self.left.take().map(|node| *node)
    }

    pub(crate) fn take_right(&mut self) -> Option<Self> {
        self.right.take().map(|node| *node)
    }

    /// New node MUST maintain BST property
    pub(crate) fn set_left(&mut self, new_node: Self) {
        debug_assert!(self.left.is_none());
        self.left = Some(Box::new(new_node));
    }

    /// New node MUST maintain BST property
    pub(crate) fn set_right(&mut self, new_node: Self) {
        debug_assert!(self.right.is_none());
        self.right = Some(Box::new(new_node));
    }

    /// New node MUST maintain BST property
    pub(crate) fn replace_left(&mut self, new_node: Self) -> Option<Box<Self>> {
        mem::replace(&mut self.left, Some(Box::new(new_node)))
    }

    /// New node MUST maintain BST property
    pub(crate) fn replace_right(&mut self, new_node: Self) -> Option<Box<Self>> {
        mem::replace(&mut self.right, Some(Box::new(new_node)))
    }

    pub(crate) fn remove_left(&mut self) -> Option<Self> {
        self.left.take().map(|node| *node)
    }

    pub(crate) fn remove_right(&mut self) -> Option<Self> {
        self.right.take().map(|node| *node)
    }
}

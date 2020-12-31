mod index;
mod node;
mod preorder;
mod inorder;
mod postorder;

pub use node::*;
pub use preorder::*;
pub use inorder::*;
pub use postorder::*;

use std::cmp::Ordering;

use index::NodeIndex;

#[derive(Debug, Clone, PartialEq, Eq)]
struct InnerNode<K, V> {
    key: K,
    value: V,
    left: NodeIndex,
    right: NodeIndex,
}

impl<K, V> InnerNode<K, V> {
    fn new(key: K, value: V) -> Self {
        Self {
            key,
            value,
            left: NodeIndex::default(),
            right: NodeIndex::default(),
        }
    }
}

/// A binary search tree (BST)
///
/// BST properties: For each node with key `k`:
/// - The value of the key of each node in the left subtree is less than `k`
/// - The value of the key of each node in the right subtree is greater than
///   or equal to `k`
///
/// The tree is not guaranteed to be structured or balanced in any particular
/// way. The implementation may structure the tree however is needed to fulfill
/// the BST properties.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BSTMap<K, V> {
    nodes: Vec<InnerNode<K, V>>,
    root: NodeIndex,
}

impl<K, V> Default for BSTMap<K, V> {
    fn default() -> Self {
        Self {
            nodes: Default::default(),
            root: Default::default(),
        }
    }
}

impl<K: Ord, V> BSTMap<K, V> {
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the number of nodes in the tree
    ///
    /// Time complexity: `O(1)`
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Returns true if the tree is empty
    ///
    /// Time complexity: `O(1)`
    pub fn is_empty(&self) -> bool {
        debug_assert!(self.nodes.is_empty() == self.root.is_none());
        self.nodes.is_empty()
    }

    /// Returns a reference to the value corresponding to the given key, or
    /// `None` if no such key exists in the binary search tree
    ///
    /// Time complexity: `O(log n)`
    pub fn get(&self, key: &K) -> Option<&V> {
        let mut current = self.root();
        while let Some(node) = current {
            match node.key().cmp(key) {
                Ordering::Less => current = node.left(),
                Ordering::Greater => current = node.right(),
                Ordering::Equal => return Some(node.value()),
            }
        }

        None
    }

    /// Returns a mutable reference to the value corresponding to the given
    /// key, or `None` if no such key exists in the binary search tree
    ///
    /// Time complexity: `O(log n)`
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let mut current = self.root_mut();
        while let Some(node) = current.take() {
            match node.key().cmp(key) {
                Ordering::Less => current = node.left(),
                Ordering::Greater => current = node.right(),
                Ordering::Equal => return Some(node.into_value_mut()),
            }
        }

        None
    }

    /// Inserts a new value into the binary search tree
    ///
    /// Returns the previous value if the key was already present in an
    /// existing node or `None` if a new node was inserted.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let mut current = self.root_mut();
        while let Some(mut node) = current.take() {
            match node.key().cmp(&key) {
                Ordering::Less => {
                    // Key not found, insert where we stopped
                    if node.has_left() {
                        let index = node.push_left(key, value);
                        if self.root.is_none() {
                            self.root = index;
                        }
                        break;
                    }
                    current = node.left();
                },

                Ordering::Greater => {
                    // Key not found, insert where we stopped
                    if node.has_right() {
                        node.push_right(key, value);
                        break;
                    }
                    current = node.right();
                },

                Ordering::Equal => {
                    let prev_value = node.replace_value(value);
                    return Some(prev_value);
                },
            }
        }

        // A new node was inserted
        None
    }

    /// Performs a pre-order traversal of the tree
    pub fn iter_preorder(&self) -> PreorderIter<K, V> {
        PreorderIter::new(&self.nodes, self.root)
    }

    /// Performs an in-order traversal of the tree
    pub fn iter_inorder(&self) -> InorderIter<K, V> {
        InorderIter::new(&self.nodes, self.root)
    }

    /// Performs a post-order traversal of the tree
    pub fn iter_postorder(&self) -> PostorderIter<K, V> {
        PostorderIter::new(&self.nodes, self.root)
    }

    /// Performs a pre-order traversal of the tree
    pub fn iter_mut_preorder(&mut self) -> impl Iterator<Item=(&K, &mut V)> {
        std::iter::from_fn(|| todo!())
    }

    /// Performs an in-order traversal of the tree
    pub fn iter_mut_inorder(&mut self) -> impl Iterator<Item=(&K, &mut V)> {
        std::iter::from_fn(|| todo!())
    }

    /// Performs a post-order traversal of the tree
    pub fn iter_mut_postorder(&mut self) -> impl Iterator<Item=(&K, &mut V)> {
        std::iter::from_fn(|| todo!())
    }

    /// Returns the root node of the tree, or `None` if the tree is empty
    ///
    /// Note that the root can be **any** node inserted into the tree. This may
    /// change depending on the self-balancing characteristics of the
    /// implementation. For a guaranteed ordering, use the various iteration
    /// methods.
    ///
    /// This is a low-level API meant to be used for implementing traversals.
    /// The inner structure of the tree can be anything that satisfies the
    /// BST properties.
    pub fn root(&self) -> Option<BSTNode<K, V>> {
        // Safety: `self.root` is a valid index into `self.nodes`
        unsafe { BSTNode::new(&self.nodes, self.root) }
    }

    /// Returns the root node of the tree, or `None` if the tree is empty
    ///
    /// Note that the root can be **any** node inserted into the tree. This may
    /// change depending on the self-balancing characteristics of the
    /// implementation. For a guaranteed ordering, use the various iteration
    /// methods.
    ///
    /// This is a low-level API meant to be used for implementing traversals.
    /// The inner structure of the tree can be anything that satisfies the
    /// BST properties.
    pub fn root_mut(&mut self) -> Option<BSTNodeMut<K, V>> {
        // Safety: `self.root` is a valid index into `self.nodes`
        unsafe { BSTNodeMut::new(&mut self.nodes, self.root) }
    }
}

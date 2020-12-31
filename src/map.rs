use std::mem;
use std::cmp::Ordering;

#[macro_export(local_inner_macros)]
macro_rules! bstmap {
    // trailing comma case
    ($($key:expr => $value:expr,)+) => (bstmap!($($key => $value),+));

    ( $($key:expr => $value:expr),* ) => {
        {
            let mut _map = $crate::BSTMap::new();
            $(
                let _ = _map.insert($key, $value);
            )*
            _map
        }
    };
}

/// The index/ID of a node
///
/// This type is essentially `Option<usize>`. The value usize::MAX is
/// reserved to represent `None`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct NodeIndex(usize);

impl Default for NodeIndex {
    fn default() -> Self {
        // Default to no node
        NodeIndex(usize::MAX)
    }
}

impl NodeIndex {
    fn new(value: usize) -> Option<Self> {
        if value == usize::MAX {
            None
        } else {
            Some(NodeIndex(value))
        }
    }

    fn into_index(self) -> Option<usize> {
        let NodeIndex(index) = self;
        if index == usize::MAX {
            None
        } else {
            Some(index)
        }
    }

    fn is_none(self) -> bool {
        self.0 == usize::MAX
    }
}

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

/// A single node of the binary search tree
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BSTNode<'a, K, V> {
    nodes: &'a [InnerNode<K, V>],
    /// An index into `nodes` for the node represented by this struct
    ///
    /// Guaranteed to be a valid index
    index: usize,
}

impl<'a, K: Ord, V> BSTNode<'a, K, V> {
    /// Creates a new `BSTNode`
    ///
    /// # Safety
    ///
    /// Must guarantee that `index` represents a valid index into `nodes`.
    unsafe fn new(nodes: &'a [InnerNode<K, V>], index: NodeIndex) -> Option<Self> {
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
#[derive(Debug, PartialEq, Eq)]
pub struct BSTNodeMut<'a, K, V> {
    nodes: &'a mut Vec<InnerNode<K, V>>,
    /// An index into `nodes` for the node represented by this struct
    ///
    /// Guaranteed to be a valid index
    index: usize,
}

impl<'a, K: Ord, V> BSTNodeMut<'a, K, V> {
    /// Creates a new `BSTNodeMut`
    ///
    /// # Safety
    ///
    /// Must guarantee that `index` represents a valid index into `nodes`.
    unsafe fn new(nodes: &'a mut Vec<InnerNode<K, V>>, index: NodeIndex) -> Option<Self> {
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

fn push_node<K, V>(nodes: &mut Vec<InnerNode<K, V>>, key: K, value: V) -> NodeIndex {
    let index = nodes.len();
    nodes.push(InnerNode::new(key, value));
    NodeIndex::new(index).expect("cannot have more than usize::MAX - 1 nodes")
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

#[derive(Debug)]
pub struct PreorderIter<'a, K, V> {
    nodes: &'a [InnerNode<K, V>],
    stack: Vec<usize>,
}

// See: https://www.geeksforgeeks.org/iterative-preorder-traversal/
impl<'a, K, V> PreorderIter<'a, K, V> {
    fn new(nodes: &'a [InnerNode<K, V>], root: NodeIndex) -> Self {
        Self {
            nodes,
            stack: root.into_index().into_iter().collect(),
        }
    }
}

// See: https://www.geeksforgeeks.org/iterative-preorder-traversal/
impl<'a, K, V> Iterator for PreorderIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let top_index = self.stack.pop()?;
        // Safety: any indexes added to the stack are valid in `self.nodes`
        let node = unsafe { self.nodes.get_unchecked(top_index) };
        self.stack.extend(node.right.into_index());
        self.stack.extend(node.left.into_index());
        Some((&node.key, &node.value))
    }
}

#[derive(Debug)]
pub struct InorderIter<'a, K, V> {
    nodes: &'a [InnerNode<K, V>],
    stack: Vec<usize>,
}

// See: https://www.geeksforgeeks.org/inorder-tree-traversal-without-recursion/
impl<'a, K, V> InorderIter<'a, K, V> {
    fn new(nodes: &'a [InnerNode<K, V>], root: NodeIndex) -> Self {
        let mut stack = Vec::new();
        let mut current = root.into_index();
        while let Some(index) = current {
            stack.push(index);
            // Safety: Nodes contain indexes to other valid nodes in `nodes`
            let current_node = unsafe { nodes.get_unchecked(index) };
            current = current_node.left.into_index();
        }

        Self {nodes, stack}
    }
}

// See: https://www.geeksforgeeks.org/inorder-tree-traversal-without-recursion/
impl<'a, K, V> Iterator for InorderIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let top_index = self.stack.pop()?;
        // Safety: any indexes added to the stack are valid in `self.nodes`
        let node = unsafe { self.nodes.get_unchecked(top_index) };

        let mut current = node.right.into_index();
        while let Some(index) = current {
            self.stack.push(index);
            // Safety: Nodes contain indexes to other valid nodes in `nodes`
            let current_node = unsafe { self.nodes.get_unchecked(index) };
            current = current_node.left.into_index();
        }

        Some((&node.key, &node.value))
    }
}

#[derive(Debug)]
pub struct PostorderIter<'a, K, V> {
    nodes: &'a [InnerNode<K, V>],
    stack: Vec<usize>,
}

// See: top_index
impl<'a, K, V> PostorderIter<'a, K, V> {
    fn new(nodes: &'a [InnerNode<K, V>], root: NodeIndex) -> Self {
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
impl<'a, K, V> Iterator for PostorderIter<'a, K, V> {
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

mod node;
mod preorder;
mod inorder;
mod postorder;

pub use node::*;
pub use preorder::*;
pub use inorder::*;
pub use postorder::*;

use std::fmt;
use std::cmp::Ordering;
use std::borrow::Borrow;
use std::iter::FromIterator;

#[cfg(test)]
use static_assertions::const_assert_eq;

use crate::slab::{UnsafeSlab, Ptr};

#[derive(Clone)]
struct InnerNode<K, V> {
    key: K,
    value: V,
    left: Ptr,
    right: Ptr,
}

// We've designed `InnerNode` to use as little space as possible to help with cache
#[cfg(test)]
const_assert_eq!(std::mem::size_of::<InnerNode<(), ()>>(), 16);

impl<K, V> InnerNode<K, V> {
    fn new(key: K, value: V) -> Self {
        Self {
            key,
            value,
            left: Ptr::default(),
            right: Ptr::default(),
        }
    }
}

fn push_node<K, V>(nodes: &mut UnsafeSlab<InnerNode<K, V>>, key: K, value: V) -> Ptr {
    let index = nodes.push(InnerNode::new(key, value));
    Ptr::new(index).expect("cannot have more than usize::MAX - 1 nodes")
}

/// A binary search tree (BST)
///
/// BST properties: For each node with key `k`:
/// - The value of the key of each node in the left subtree is less than `k`
/// - The value of the key of each node in the right subtree is greater than `k`
///
/// Duplicate keys are not allowed. Inserting a key that already exists in the map updates the
/// previous value.
///
/// The tree is not guaranteed to be structured or balanced in any particular way. The
/// implementation may structure the tree however is needed to fulfill the BST properties.
pub struct BSTMap<K, V> {
    nodes: UnsafeSlab<InnerNode<K, V>>,
    root: Ptr,
}

impl<K, V> Default for BSTMap<K, V> {
    fn default() -> Self {
        Self {
            nodes: UnsafeSlab::new(),
            root: Default::default(),
        }
    }
}

impl<K, V> fmt::Debug for BSTMap<K, V>
    where K: Ord + fmt::Debug,
          V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BSTMap")
            .field("root", &self.root())
            .finish()
    }
}

//TODO: This can be specialized to a single memcpy if K: Copy and V: Copy
impl<K: Clone, V: Clone> Clone for BSTMap<K, V> {
    fn clone(&self) -> Self {
        use std::mem::{self, MaybeUninit};

        let mut nodes = self.nodes.clone_uninit();

        // For a balanced tree, this will use O(log n) space.
        let mut stack = Vec::new();
        stack.extend(self.root.into_index());

        // Walk tree and initialize nodes
        while let Some(index) = stack.pop() {
            // Safety: any indexes added to the stack are valid in `self.nodes`
            let node = unsafe { self.nodes.get_unchecked(index) };
            stack.extend(node.right.into_index());
            stack.extend(node.left.into_index());

            let new_entry = MaybeUninit::new(node.clone());
            // Safety: initializing the same index in the new set of nodes as was used in the old
            // set of nodes, so it should be valid. Furthermore, `MaybeUninit` does not need to be
            // initialized, so `&mut MaybeUninit` does not cause UB, even though the memory has not
            // been initialized yet.
            unsafe { *nodes.get_unchecked_mut(index) = new_entry; }
        }

        Self {
            // Safety: All entries that previously contained a value have now been initialized
            nodes: unsafe { mem::transmute(nodes) },
            root: self.root,
        }
    }
}

impl<K: Ord + PartialEq, V: PartialEq> PartialEq for BSTMap<K, V> {
    fn eq(&self, other: &Self) -> bool {
        // We can't just compare the binary trees structurally, since they may be structured
        // differently while still having all the same elements (e.g. if insertion order is
        // different). Instead, we use in-order traversal since we know that that is guaranteed to
        // produce the elements in sorted order. If their sorted orders are equal, the maps are
        // equal.

        if self.len() != other.len() {
            return false;
        }

        self.iter_inorder().zip(other.iter_inorder()).all(|((k1, v1), (k2, v2))| {
            k1.eq(k2) && v1.eq(v2)
        })
    }
}

impl<K: Ord + Eq, V: Eq> Eq for BSTMap<K, V> {}

impl<K: Ord, V> BSTMap<K, V> {
    /// Creates an empty `BSTMap`
    ///
    /// The map is initially created with a capacity of 0, so it will not allocate until it is first
    /// inserted into.
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTMap;
    /// let mut map: BSTMap<&str, i32> = BSTMap::new();
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates an empty map with the specified capacity.
    ///
    /// The map will be able to hold at least `capacity` elements without reallocating. If
    /// `capacity` is 0, the map will not allocate.
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTMap;
    /// let mut map: BSTMap<&str, i32> = BSTMap::with_capacity(10);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            nodes: UnsafeSlab::with_capacity(capacity),
            ..Self::default()
        }
    }

    /// Returns the number of entries in the map (i.e. the number of nodes in the binary search
    /// tree)
    ///
    /// Time complexity: `O(1)`
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTMap;
    ///
    /// let mut map = BSTMap::new();
    /// assert_eq!(map.len(), 0);
    /// map.insert(1, "a");
    /// assert_eq!(map.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Returns the number of elements the map can hold without reallocating.
    ///
    /// This number is a lower bound; the map might be able to hold more, but is guaranteed to be
    /// able to hold at least this many.
    ///
    /// Time complexity: `O(1)`
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTMap;
    /// let mut map: BSTMap<&str, i32> = BSTMap::with_capacity(100);
    /// assert!(map.capacity() >= 100);
    /// ```
    pub fn capacity(&self) -> usize {
        self.nodes.capacity()
    }

    /// Returns true if the map is empty
    ///
    /// Time complexity: `O(1)`
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTMap;
    ///
    /// let mut map = BSTMap::new();
    /// assert!(map.is_empty());
    /// map.insert(1, "a");
    /// assert!(!map.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        debug_assert!(self.nodes.is_empty() == self.root.is_null());
        self.nodes.is_empty()
    }

    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering on the borrowed
    /// form must match the ordering on the key type.
    ///
    /// Time complexity: `O(log n)`
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTMap;
    ///
    /// let mut map = BSTMap::new();
    /// map.insert(1, "a");
    /// assert!(map.contains_key(&1));
    /// assert!(!map.contains_key(&2));
    /// ```
    pub fn contains_key<Q>(&self, key: &Q) -> bool
        where K: Borrow<Q>,
              Q: Ord + ?Sized,
    {
        let mut current = self.root();
        while let Some(node) = current {
            match key.cmp(node.key().borrow()) {
                Ordering::Less => current = node.left(),
                Ordering::Greater => current = node.right(),
                Ordering::Equal => return true,
            }
        }

        false
    }

    /// Returns a reference to the value corresponding to the given key, or `None` if no such key
    /// exists in the binary search tree
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering on the borrowed
    /// form must match the ordering on the key type.
    ///
    /// Time complexity: `O(log n)`
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTMap;
    ///
    /// let mut map = BSTMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
        where K: Borrow<Q>,
              Q: Ord + ?Sized,
    {
        let mut current = self.root();
        while let Some(node) = current {
            match key.cmp(node.key().borrow()) {
                Ordering::Less => current = node.left(),
                Ordering::Greater => current = node.right(),
                Ordering::Equal => return Some(node.value()),
            }
        }

        None
    }

    /// Returns a mutable reference to the value corresponding to the given key, or `None` if no
    /// such key exists in the binary search tree
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering on the borrowed
    /// form must match the ordering on the key type.
    ///
    /// Time complexity: `O(log n)`
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTMap;
    ///
    /// let mut map = BSTMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// if let Some(x) = map.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map.get(&1), Some(&"b"));
    ///
    /// assert_eq!(map.get_mut(&2), None);
    /// ```
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
        where K: Borrow<Q>,
              Q: Ord + ?Sized,
    {
        let mut current = self.root_mut();
        while let Some(node) = current.take() {
            match key.cmp(node.key().borrow()) {
                Ordering::Less => current = node.left(),
                Ordering::Greater => current = node.right(),
                Ordering::Equal => return Some(node.into_value_mut()),
            }
        }

        None
    }

    /// Returns a key-value pair corresponding to the given key, or `None` if no such key exists in
    /// the binary search tree
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering on the borrowed
    /// form must match the ordering on the key type.
    ///
    /// Time complexity: `O(log n)`
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTMap;
    ///
    /// let mut map = BSTMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get_entry(&1), Some((&1, &"a")));
    /// assert_eq!(map.get_entry(&2), None);
    /// ```
    pub fn get_entry<Q>(&self, key: &Q) -> Option<(&K, &V)>
        where K: Borrow<Q>,
              Q: Ord + ?Sized,
    {
        let mut current = self.root();
        while let Some(node) = current {
            match key.cmp(node.key().borrow()) {
                Ordering::Less => current = node.left(),
                Ordering::Greater => current = node.right(),
                Ordering::Equal => return Some((node.key(), node.value())),
            }
        }

        None
    }

    /// Inserts a new value into the binary search tree
    ///
    /// Returns the previous value if the key was already present in an
    /// existing node or `None` if a new node was inserted.
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTMap;
    ///
    /// let mut map = BSTMap::new();
    /// # assert!(map.is_empty());
    /// assert_eq!(map.insert(37, "a"), None);
    /// assert!(!map.is_empty());
    ///
    /// map.insert(37, "b");
    /// assert_eq!(map.insert(37, "c"), Some("b"));
    /// assert_eq!(map.get(&37), Some(&"c"));
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let mut current = match self.root_mut() {
            Some(root) => Some(root),
            None => {
                let index = push_node(&mut self.nodes, key, value);
                self.root = index;
                return None;
            },
        };

        while let Some(mut node) = current.take() {
            match key.cmp(node.key().borrow()) {
                Ordering::Less => {
                    // Key not found, insert where we stopped
                    if !node.has_left() {
                        node.push_left(key, value);
                        break;
                    }
                    current = node.left();
                },

                Ordering::Greater => {
                    // Key not found, insert where we stopped
                    if !node.has_right() {
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

    /// Removes a key from the map, returning the value at the key if the key was previously in the
    /// map.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering on the borrowed
    /// form must match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTMap;
    ///
    /// let mut map = BSTMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
        where K: Borrow<Q>,
              Q: Ord + ?Sized,
    {
        self.remove_entry(key).map(|(_, value)| value)
    }

    /// Removes a key from the map, returning the (key, value) pair for that key if it was
    /// previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering on the borrowed
    /// form must match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTMap;
    ///
    /// let mut map = BSTMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove_entry(&1), Some((1, "a")));
    /// assert_eq!(map.remove_entry(&1), None);
    /// ```
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
        where K: Borrow<Q>,
              Q: Ord + ?Sized,
    {
        let mut parent = Ptr::null();
        let mut current = self.root;

        while let Some(index) = current.into_index() {
            // Safety: any indexes in the tree are valid in `self.nodes`
            let node = unsafe { self.nodes.get_unchecked(index) };

            match key.cmp(node.key.borrow()) {
                Ordering::Less => {
                    parent = current;
                    current = node.left
                },

                Ordering::Greater => {
                    parent = current;
                    current = node.right
                },

                Ordering::Equal => break,
            }
        }

        // If a node was found, remove it, otherwise return None
        let index = current.into_index()?;
        // Safety: any indexes in the tree are valid in `self.nodes`
        let node = unsafe { self.nodes.get_unchecked(index) };

        match (node.left.into_index(), node.right.into_index()) {
            // No child nodes, just delete the node
            (None, None) => {
                // Safety: any indexes in the tree are valid in `self.nodes`
                // The previous `node` variable which was referencing this memory will end here so
                // there is no overlap in lifetimes. We also shadow the name to extra make sure that
                // there can be no UB.
                let node = unsafe { self.nodes.remove(index) };

                if let Some(parent_index) = parent.into_index() {
                    let parent_node = unsafe { self.nodes.get_unchecked_mut(parent_index) };

                    if parent_node.left == current {
                        parent_node.left = Ptr::null();

                    } else if parent_node.right == current {
                        parent_node.right = Ptr::null();
                    }
                }

                if self.root == current {
                    self.root = Ptr::null();
                }

                Some((node.key, node.value))
            },

            // Only one child node, so we can just replace the node with its child
            (None, Some(child_index)) |
            (Some(child_index), None) => {
                // Safety: if this was a valid pointer before, it is still valid now
                let child_ptr = unsafe { Ptr::new_unchecked(child_index) };

                // Safety: any indexes in the tree are valid in `self.nodes`
                // The previous `node` variable which was referencing this memory will end here so
                // there is no overlap in lifetimes. We also shadow the name to extra make sure that
                // there can be no UB.
                let node = unsafe { self.nodes.remove(index) };

                if let Some(parent_index) = parent.into_index() {
                    // Safety: any indexes from the tree are valid in `self.nodes`
                    let parent_node = unsafe { self.nodes.get_unchecked_mut(parent_index) };

                    if parent_node.left == current {
                        parent_node.left = child_ptr;

                    } else if parent_node.right == current {
                        parent_node.right = child_ptr;
                    }
                }

                // Update the root node if that is what we're removing
                if self.root == current {
                    self.root = child_ptr;
                }

                Some((node.key, node.value))
            },

            // Two child nodes, swap the current node for its in-order successor
            (Some(left_index), Some(right_index)) => {
                // the parent of `right_index` is the index from `current`
                let mut inorder_succ_parent = index;
                let mut inorder_succ = right_index;

                loop {
                    // Safety: any indexes from the tree are valid in `self.nodes`
                    let node = unsafe { self.nodes.get_unchecked(inorder_succ) };

                    match node.left.into_index() {
                        Some(node_left_index) => {
                            inorder_succ_parent = inorder_succ;
                            inorder_succ = node_left_index;
                        },

                        None => break,
                    }
                }

                // Safety: any indexes from the tree are valid in `self.nodes`
                //   This index may not be unique from `index`, so `node` may not be used again
                //   after this line. If it is, the lifetime of `node` and this variable will
                //   overlap and we'll have both a mutable ref and immutable ref to the same data.
                let inorder_succ_node = unsafe { self.nodes.get_unchecked_mut(inorder_succ) };
                // Update the left child of the in-order successor
                // Safety: if this was a valid pointer before, it is still valid now
                inorder_succ_node.left = unsafe { Ptr::new_unchecked(left_index) };
                // Store the right subtree of the in-order successor so we can use it when we remove
                // the in-order successor from its parent
                let inorder_succ_right = inorder_succ_node.right;
                // Update the right child of the in-order successor to be the right child of the
                // `current` node being removed so we don't lose that subtree
                // Only need to do this if the in-order successor is not already the right subtree
                if inorder_succ != right_index {
                    // Safety: if this was a valid pointer before, it is still valid now
                    inorder_succ_node.right = unsafe { Ptr::new_unchecked(right_index) };
                }

                // Safety: any indexes from the tree are valid in `self.nodes`
                //   Furthermore, the only other reference in scope is `node`. Since we started
                //   finding `inorder_succ` at `right_index`, and `right_index` is not the same
                //   as `index` (from `current`), we know that `inorder_succ_parent_index`
                //   cannot be the same as `index`. Thus, this mutable reference is unique.
                let inorder_succ_parent_node = unsafe { self.nodes.get_unchecked_mut(inorder_succ_parent) };
                // Remove the in-order successor from its parent (the parent might be the current node)
                // Note: in-order successor is always the zero or one child remove case since we
                // find it by checking if there is a left child
                if inorder_succ_parent == index {
                    // Remove the right child from the current node
                    inorder_succ_parent_node.right = inorder_succ_right;
                } else {
                    // Remove the left child from the parent of the in-order successor
                    inorder_succ_parent_node.left = inorder_succ_right;
                }

                // Safety: the code above guarantees that in-order successor is a valid pointer and
                //   will not be `usize::MAX` (since all indexes in the tree are valid)
                let inorder_succ_ptr = unsafe { Ptr::new_unchecked(inorder_succ) };
                // Assign the in-order successor as the new child of the parent of `current`
                if let Some(parent_index) = parent.into_index() {
                    // Safety: any indexes from the tree are valid in `self.nodes`
                    let parent_node = unsafe { self.nodes.get_unchecked_mut(parent_index) };

                    if parent_node.left == current {
                        parent_node.left = inorder_succ_ptr;

                    } else if parent_node.right == current {
                        parent_node.right = inorder_succ_ptr;
                    }
                }

                // Update the root node if that is what we're removing
                if self.root == current {
                    self.root = inorder_succ_ptr;
                }

                // Safety: any indexes in the tree are valid in `self.nodes`
                //   The previous `node` variable which was referencing this memory will end here so
                //   there is no overlap in lifetimes. The `inorder_succ_node` which may also
                //   overlap is also not used after this point, so there will be no overlap in
                //   lifetime there either. We also shadow the name to extra make sure that there
                //   can be no UB.
                let node = unsafe { self.nodes.remove(index) };

                Some((node.key, node.value))
            },
        }
    }

    /// Clears the map, removing all elements
    ///
    /// Note that this method has no effect on the allocated capacity of the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTMap;
    ///
    /// let mut map = BSTMap::new();
    /// map.insert(1, "a");
    /// # let capacity = map.capacity();
    /// assert!(!map.is_empty());
    /// map.clear();
    /// assert!(map.is_empty());
    /// # assert_eq!(map.capacity(), capacity);
    /// ```
    pub fn clear(&mut self) {
        let Self {nodes, root} = self;

        nodes.clear();
        *root = Ptr::default();
    }

    /// Performs a pre-order traversal of the tree
    pub fn iter_preorder(&self) -> IterPreorder<K, V> {
        IterPreorder::new(&self.nodes, self.root)
    }

    /// Performs an in-order traversal of the tree
    pub fn iter_inorder(&self) -> IterInorder<K, V> {
        IterInorder::new(&self.nodes, self.root)
    }

    /// Performs a post-order traversal of the tree
    pub fn iter_postorder(&self) -> IterPostorder<K, V> {
        IterPostorder::new(&self.nodes, self.root)
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
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use bst::{BSTMap, map::Node};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Stats {
    ///     pub score: u32,
    ///     // ...other fields...
    /// }
    ///
    /// // Custom traversal through the values in the map
    /// fn find_score(node: Option<Node<i32, Stats>>, target_score: u32) -> Option<Node<i32, Stats>> {
    ///     let node = node?;
    ///     if node.value().score == target_score {
    ///         Some(node)
    ///     } else {
    ///         // Recurse through left and right subtrees, just like you would in a GC'd language!
    ///         find_score(node.left(), target_score)
    ///             .or_else(|| find_score(node.right(), target_score))
    ///     }
    /// }
    ///
    /// fn main() {
    ///     let mut map = BSTMap::new();
    ///
    ///     map.insert(1, Stats {
    ///         score: 39382,
    ///         // ...other fields...
    ///     });
    ///     // ...more insertions...
    ///
    ///     // Find the node with score == 500
    ///     println!("{:?}", find_score(map.root(), 500));
    /// }
    /// ```
    pub fn root(&self) -> Option<Node<K, V>> {
        // Safety: `self.root` is a valid index into `self.nodes`
        unsafe { Node::new(&self.nodes, self.root) }
    }

    /// Returns the root node of the tree, or `None` if the tree is empty
    ///
    /// Note that the root can be **any** node inserted into the tree. This may change depending on
    /// the self-balancing characteristics of the implementation. For a guaranteed ordering, use the
    /// various iteration methods.
    ///
    /// This is a low-level API meant to be used for implementing traversals. The inner structure of
    /// the tree can be anything that satisfies the BST properties.
    pub fn root_mut(&mut self) -> Option<NodeMut<K, V>> {
        // Safety: `self.root` is a valid index into `self.nodes`
        unsafe { NodeMut::new(&mut self.nodes, self.root) }
    }

    /// Reserves capacity for at least `additional` more elements to be inserted in the map. The
    /// collection may reserve more space to avoid frequent reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows `usize`.
    pub fn reserve(&mut self, additional: usize) {
        self.nodes.reserve(additional)
    }

    /// Shrinks the capacity of the map as much as possible. It will drop down as much as possible
    /// while maintaining the internal rules and possibly leaving some space in accordance with the
    /// resize policy.
    pub fn shrink_to_fit(&mut self) {
        self.nodes.shrink_to_fit()
    }
}

impl<K: Ord, V> Extend<(K, V)> for BSTMap<K, V> {
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        let iter = iter.into_iter();

        // Avoid allocating too many times by reserving the space we know we will need
        let (min_len, max_len) = iter.size_hint();
        let len = max_len.unwrap_or(min_len);
        self.reserve(len);

        for (key, value) in iter {
            self.insert(key, value);
        }
    }
}

impl<K: Ord, V> FromIterator<(K, V)> for BSTMap<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let iter = iter.into_iter();

        // Avoid allocating too many times by reserving the space we know we will need
        let (min_len, max_len) = iter.size_hint();
        let len = max_len.unwrap_or(min_len);
        let mut map = Self::with_capacity(len);

        for (key, value) in iter {
            map.insert(key, value);
        }

        map
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::collections::HashMap;

    use rand::prelude::*;

    #[test]
    fn test_map_insert_get() {
        let mut map = BSTMap::new();

        assert_eq!(map.get(&3), None);
        assert_eq!(map.insert(3, 1), None);
        assert_eq!(map.get(&3), Some(&1));

        assert_eq!(map.get(&4), None);
        assert_eq!(map.insert(4, -2), None);
        assert_eq!(map.get(&3), Some(&1));
        assert_eq!(map.get(&4), Some(&-2));

        assert_eq!(map.get(&0), None);
        assert_eq!(map.insert(0, 44), None);
        assert_eq!(map.get(&3), Some(&1));
        assert_eq!(map.get(&4), Some(&-2));
        assert_eq!(map.get(&0), Some(&44));
    }

    #[test]
    fn test_map_insert_get_remove() {
        let mut map = BSTMap::new();

        // Remove on an empty map
        assert_eq!(map.remove(&0), None);

        // Remove from a map with one entry
        assert_eq!(map.insert(99, -3), None);
        assert_eq!(map.remove(&99), Some(-3));

        assert_eq!(map.get(&3), None);
        assert_eq!(map.insert(3, 1), None);
        assert_eq!(map.get(&3), Some(&1));

        assert_eq!(map.get(&4), None);
        assert_eq!(map.insert(4, -2), None);
        assert_eq!(map.get(&3), Some(&1));

        assert_eq!(map.remove_entry(&4), Some((4, -2)));
        assert_eq!(map.remove_entry(&4), None);
        assert_eq!(map.get(&3), Some(&1));

        assert_eq!(map.get(&0), None);
        assert_eq!(map.insert(0, 44), None);
        assert_eq!(map.get(&3), Some(&1));
        assert_eq!(map.get(&4), None);
        assert_eq!(map.get(&0), Some(&44));

        assert_eq!(map.remove(&0), Some(44));
        assert_eq!(map.remove(&0), None);
        assert_eq!(map.get(&3), Some(&1));
        assert_eq!(map.get(&4), None);
    }

    #[test]
    fn test_map_insert_remove_two_children() {
        // Using a map with a type that implements Drop
        let mut map: BSTMap<String, _> = BSTMap::new();

        assert_eq!(map.insert("b".to_string(), 0), None);
        assert_eq!(map.insert("a".to_string(), 89), None);
        assert_eq!(map.insert("c".to_string(), 391), None);

        // Remove an entry with two children
        assert_eq!(map.remove("b"), Some(0));
        assert_eq!(map.remove("b"), None);

        // remove should not impact other items
        assert_eq!(map.get("a"), Some(&89));
        assert_eq!(map.get("c"), Some(&391));

        // remove should detect keys that don't exist
        assert_eq!(map.remove(""), None);
    }

    #[test]
    fn test_map_insert_replace() {
        let mut map = BSTMap::new();

        assert_eq!(map.get(&3), None);
        assert_eq!(map.insert(3, 1), None);
        assert_eq!(map.get(&3), Some(&1));

        assert_eq!(map.get(&4), None);
        assert_eq!(map.insert(4, -2), None);
        assert_eq!(map.get(&3), Some(&1));
        assert_eq!(map.get(&4), Some(&-2));

        assert_eq!(map.insert(3, 933), Some(1));
        assert_eq!(map.get(&3), Some(&933));
        assert_eq!(map.get(&4), Some(&-2));

        assert_eq!(map.insert(3, 11), Some(933));
        assert_eq!(map.get(&3), Some(&11));
        assert_eq!(map.get(&4), Some(&-2));

        assert_eq!(map.insert(4, 3), Some(-2));
        assert_eq!(map.get(&3), Some(&11));
        assert_eq!(map.get(&4), Some(&3));
    }

    #[test]
    fn test_map_insert_get_borrow() {
        let mut map: BSTMap<String, _> = BSTMap::new();

        assert_eq!(map.get("abc"), None);
        assert_eq!(map.insert("abc".to_string(), 1), None);
        assert_eq!(map.get("abc"), Some(&1));

        assert_eq!(map.get("COOL"), None);
        assert_eq!(map.insert("COOL".to_string(), 3), None);
        assert_eq!(map.get("abc"), Some(&1));
        assert_eq!(map.get("COOL"), Some(&3));

        assert_eq!(map.get(""), None);
        assert_eq!(map.insert("".to_string(), 898989), None);
        assert_eq!(map.get("abc"), Some(&1));
        assert_eq!(map.get("COOL"), Some(&3));
        assert_eq!(map.get(""), Some(&898989));
    }

    #[test]
    fn test_random_operations() {
        cfg_if::cfg_if! {
            if #[cfg(miri)] {
                const TEST_CASES: usize = 16;
                const OPERATIONS: usize = 24;

                (0..TEST_CASES).into_iter().for_each(|_| test_case());

            } else {
                use rayon::prelude::*;

                const TEST_CASES: usize = 1024;
                const OPERATIONS: usize = 128;

                (0..TEST_CASES).into_par_iter().for_each(|_| test_case());
            }
        }

        fn test_case() {
            let mut map = BSTMap::new();
            // Compare against a HashMap
            let mut expected = HashMap::new();
            // The list of keys that have been inserted
            let mut keys = Vec::new();

            let seed = thread_rng().gen();
            println!("Seed: {:?}", seed);
            let mut rng = StdRng::from_seed(seed);
            for _ in 0..rng.gen_range(OPERATIONS..=OPERATIONS*2) {
                assert_eq!(map.is_empty(), expected.is_empty());
                assert_eq!(map.len(), expected.len());

                match rng.gen_range(1..=100) {
                    // Check for a key that hasn't been inserted
                    1..=10 => {
                        // Not inserting any negative numbers
                        let key = -rng.gen_range(1..=64);
                        assert_eq!(map.get(&key), expected.get(&key));
                        assert_eq!(map.get_mut(&key), expected.get_mut(&key));
                    },

                    // Check for a key that has been inserted
                    11..=30 => {
                        let key = match keys.choose(&mut rng).copied() {
                            Some(key) => key,
                            None => continue,
                        };
                        assert_eq!(map.get(&key), expected.get(&key));
                        assert_eq!(map.get_mut(&key), expected.get_mut(&key));
                    },

                    // Modify an existing key
                    31..=50 => {
                        let key = match keys.choose(&mut rng).copied() {
                            Some(key) => key,
                            None => continue,
                        };

                        let value = rng.gen_range(100..=200);

                        assert_eq!(map.get(&key), expected.get(&key));
                        match (map.get_mut(&key), expected.get_mut(&key)) {
                            (Some(entry1), Some(entry2)) => {
                                *entry1 = value;
                                *entry2 = value;
                            },

                            _ => continue,
                        }
                        assert_eq!(map.get(&key), expected.get(&key));
                        assert_eq!(map.get_mut(&key), expected.get_mut(&key));
                    },

                    // Remove an existing key
                    51..=70 => {
                        let key = match keys.choose(&mut rng).copied() {
                            Some(key) => key,
                            None => continue,
                        };

                        assert_eq!(map.remove(&key), expected.remove(&key));
                        // Second remove should yield `None`
                        assert_eq!(map.remove(&key), expected.remove(&key));
                    },

                    // Insert a key
                    71..=100 => {
                        // Only inserting positive values
                        let key = rng.gen_range(0..=64);
                        let value = rng.gen_range(100..=200);
                        keys.push(key);

                        assert_eq!(map.get(&key), expected.get(&key));
                        assert_eq!(map.get_mut(&key), expected.get_mut(&key));

                        assert_eq!(map.insert(key, value), expected.insert(key, value));

                        assert_eq!(map.get(&key), expected.get(&key));
                        assert_eq!(map.get_mut(&key), expected.get_mut(&key));
                    },

                    _ => unreachable!(),
                }
            }

            for &key in &keys {
                assert_eq!(map.get(&key), expected.get(&key));
                assert_eq!(map.get_mut(&key), expected.get_mut(&key));
            }

            map.clear();
            expected.clear();

            assert_eq!(map.is_empty(), expected.is_empty());
            assert_eq!(map.len(), expected.len());

            for &key in &keys {
                assert_eq!(map.get(&key), expected.get(&key));
                assert_eq!(map.get_mut(&key), expected.get_mut(&key));
            }
        }
    }

    #[test]
    fn traversals() {
        //TODO: This test is brittle and relies on insertion behaviour. Really we want to encode the
        // shape of the tree in the test itself. Maybe with some unsafe `with_tree_structure`
        // constructor for BSTMap or something.

        let mut map = BSTMap::new();
        // Create the following tree:
        //      4
        //   2     5
        // 1   3
        //
        // Inserting the tree one level at a time so it makes this shape:
        map.insert(4, 4);
        map.insert(5, 5);
        map.insert(2, 2);
        map.insert(3, 3);
        map.insert(1, 1);

        let values: Vec<_> = map.iter_preorder().map(|(k, _)| *k).collect();
        assert_eq!(&values, &[4, 2, 1, 3, 5]);

        let values: Vec<_> = map.iter_inorder().map(|(k, _)| *k).collect();
        assert_eq!(&values, &[1, 2, 3, 4, 5]);

        let values: Vec<_> = map.iter_postorder().map(|(k, _)| *k).collect();
        assert_eq!(&values, &[1, 3, 2, 5, 4]);
    }

    #[test]
    fn test_custom_traversal() {
        #[derive(Debug, PartialEq, Eq)]
        struct Stats {
            pub score: u32,
        }

        // Custom traversal through the values in the map
        fn find_score(node: Option<Node<i32, Stats>>, target_score: u32) -> Option<Node<i32, Stats>> {
            let node = node?;
            if node.value().score == target_score {
                Some(node)
            } else {
                // Recurse through left and right subtrees, just like you would in a GC'd language!
                find_score(node.left(), target_score)
                    .or_else(|| find_score(node.right(), target_score))
            }
        }

        let mut map = BSTMap::new();

        map.insert(1, Stats {
            score: 39382,
        });
        map.insert(0, Stats {
            score: 400,
        });
        map.insert(40, Stats {
            score: 999,
        });
        map.insert(42, Stats {
            score: 33,
        });

        // Find the node with score == 500
        assert_eq!(find_score(map.root(), 500), None);
        assert_eq!(find_score(map.root(), 39382).map(|node| *node.key()), Some(1));
        assert_eq!(find_score(map.root(), 999).map(|node| *node.key()), Some(40));
        assert_eq!(find_score(map.root(), 33).map(|node| *node.key()), Some(42));
    }

    #[test]
    fn test_eq() {
        let mut map1 = BSTMap::new();

        for i in 0..10 {
            map1.insert(i, i);
        }

        // Reflexivity
        assert_eq!(map1, map1);

        let mut map2 = BSTMap::new();

        for i in (0..10).rev() {
            map2.insert(i, i);
        }

        // Reflexivity
        assert_eq!(map2, map2);
        // Symmetry
        assert_eq!(map1, map2);
        assert_eq!(map2, map1);

        let mut map3 = BSTMap::new();

        for i in 10..20 {
            map3.insert(i, i);
        }

        // Reflexivity
        assert_eq!(map3, map3);
        // Completely different maps, same lengths
        assert_eq!(map1.len(), map3.len());
        assert_ne!(map1, map3);
        assert_ne!(map2, map3);

        let mut map4 = BSTMap::new();

        for i in 10..20 {
            // Different value
            map4.insert(i, i * 10);
        }

        // Reflexivity
        assert_eq!(map4, map4);
        // Completely different maps, same lengths
        assert_eq!(map1.len(), map4.len());
        assert_ne!(map1, map4);
        assert_ne!(map2, map4);
        // Same keys, different values
        assert_ne!(map3, map4);

        let map5 = BSTMap::new();

        // Reflexivity
        assert_eq!(map5, map5);
        // Completely different maps, different lengths
        assert_ne!(map1.len(), map5.len());
        assert_ne!(map1, map5);
        assert_ne!(map2, map5);
        assert_ne!(map3, map5);
        assert_ne!(map4, map5);

        // Empty maps should be equal
        assert!(map5.is_empty());
        assert_eq!(map5, BSTMap::default());
    }

    #[test]
    fn test_clone_eq() {
        let mut map = BSTMap::new();

        for i in 0..10 {
            map.insert(i, -i * 25);
        }

        map.remove(&0);
        map.remove(&1);
        map.remove(&5);

        assert_eq!(map, map.clone());
    }
}

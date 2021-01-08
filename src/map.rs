mod index;
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

use index::NodeIndex;

#[derive(Clone, PartialEq, Eq)]
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

fn push_node<K, V>(nodes: &mut Vec<InnerNode<K, V>>, key: K, value: V) -> NodeIndex {
    let index = nodes.len();
    nodes.push(InnerNode::new(key, value));
    NodeIndex::new(index).expect("cannot have more than usize::MAX - 1 nodes")
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
#[derive(Clone, PartialEq, Eq)]
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
            nodes: Vec::with_capacity(capacity),
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
        debug_assert!(self.nodes.is_empty() == self.root.is_none());
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
    /// ```ignore
    /// use bst::BSTMap;
    ///
    /// let mut map = BSTMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    pub fn remove<Q>(&mut self, _key: &Q) -> Option<V>
        where K: Borrow<Q>,
              Q: Ord + ?Sized,
    {
        //TODO: Re-enable doctest for this method
        todo!()
    }

    /// Clears the map, removing all elements
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTMap;
    ///
    /// let mut map = BSTMap::new();
    /// map.insert(1, "a");
    /// assert!(!map.is_empty());
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn clear(&mut self) {
        *self = Self::new();
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

    use rayon::prelude::*;
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
        const TEST_CASES: usize = 1024;
        const OPERATIONS: usize = 128;

        (0..TEST_CASES).into_par_iter().for_each(|_| {
            let mut map = BSTMap::new();
            // Compare against a HashMap
            let mut expected = HashMap::new();
            // The list of keys that have been inserted
            let mut keys = Vec::new();

            let mut rng = rand::thread_rng();
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
                        // Unwrap is safe because we're selected from the list of existing keys
                        *map.get_mut(&key).unwrap() = value;
                        *expected.get_mut(&key).unwrap() = value;
                        assert_eq!(map.get(&key), expected.get(&key));
                        assert_eq!(map.get_mut(&key), expected.get_mut(&key));
                    },

                    // Insert a key
                    51..=100 => {
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

                    //TODO: Test `remove()`

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
        });
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
}

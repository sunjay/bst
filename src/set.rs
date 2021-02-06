mod node;
mod preorder;
mod inorder;
mod postorder;

pub use node::*;
pub use preorder::*;
pub use inorder::*;
pub use postorder::*;

use std::fmt;
use std::borrow::Borrow;
use std::iter::FromIterator;

/// A binary search tree (BST)
///
/// BST properties: For each node with value `v`:
/// - The value of each node in the left subtree is less than `v`
/// - The value of each node in the right subtree is greater than `v`
///
/// Duplicate values are not allowed. Inserting a values that already exists in the map does not
/// modify the map.
///
/// The tree is not guaranteed to be structured or balanced in any particular way. The
/// implementation may structure the tree however is needed to fulfill the BST properties.
#[derive(Clone)]
pub struct BSTSet<T> {
    items: crate::map::BSTMap<T, ()>,
}

impl<T> Default for BSTSet<T> {
    fn default() -> Self {
        Self {
            items: Default::default(),
        }
    }
}

impl<T> fmt::Debug for BSTSet<T>
    where T: Ord + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BSTSet")
            .field("root", &self.root())
            .finish()
    }
}

impl<T: Ord + PartialEq> PartialEq for BSTSet<T> {
    fn eq(&self, other: &Self) -> bool {
        self.items.eq(&other.items)
    }
}

impl<T: Ord + Eq> Eq for BSTSet<T> {}

impl<T: Ord> BSTSet<T> {
    /// Creates an empty `BSTSet`
    ///
    /// The set is initially created with a capacity of 0, so it will not allocate until it is first
    /// inserted into.
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTSet;
    /// let mut set: BSTSet<&str> = BSTSet::new();
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates an empty set with the specified capacity.
    ///
    /// The set will be able to hold at least `capacity` elements without reallocating. If
    /// `capacity` is 0, the set will not allocate.
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTSet;
    /// let mut set: BSTSet<&str> = BSTSet::with_capacity(10);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            items: crate::map::BSTMap::with_capacity(capacity),
        }
    }

    /// Returns the number of items in the set (i.e. the number of nodes in the binary search tree)
    ///
    /// Time complexity: `O(1)`
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTSet;
    ///
    /// let mut set = BSTSet::new();
    /// assert_eq!(set.len(), 0);
    /// set.insert(1);
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.items.len()
    }

    /// Returns the number of elements the set can hold without reallocating.
    ///
    /// This number is a lower bound; the set might be able to hold more, but is guaranteed to be
    /// able to hold at least this many.
    ///
    /// Time complexity: `O(1)`
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTSet;
    /// let mut set: BSTSet<&str> = BSTSet::with_capacity(100);
    /// assert!(set.capacity() >= 100);
    /// ```
    pub fn capacity(&self) -> usize {
        self.items.capacity()
    }

    /// Returns true if the set is empty
    ///
    /// Time complexity: `O(1)`
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTSet;
    ///
    /// let mut set = BSTSet::new();
    /// assert!(set.is_empty());
    /// set.insert(1);
    /// assert!(!set.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// Returns `true` if the set contains the specified value.
    ///
    /// The value may be any borrowed form of the set's value type, but the ordering on the borrowed
    /// form must match the ordering on the value type.
    ///
    /// Time complexity: `O(log n)`
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTSet;
    ///
    /// let mut set = BSTSet::new();
    /// # assert!(!set.contains(&1));
    /// set.insert(1);
    /// assert!(set.contains(&1));
    /// assert!(!set.contains(&2));
    /// ```
    pub fn contains<Q>(&self, value: &Q) -> bool
        where T: Borrow<Q>,
              Q: Ord + ?Sized,
    {
        self.items.contains_key(value)
    }

    /// Returns a reference to the value in the set, or `None` if no such value exists in its binary
    /// search tree
    ///
    /// The value may be any borrowed form of the set's value type, but the ordering on the borrowed
    /// form must match the ordering on the value type.
    ///
    /// Time complexity: `O(log n)`
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTSet;
    ///
    /// let mut set = BSTSet::new();
    /// set.insert(String::from("abc"));
    /// assert!(set.contains("abc"));
    /// assert!(!set.contains("def"));
    /// ```
    pub fn get<Q>(&self, value: &Q) -> Option<&T>
        where T: Borrow<Q>,
              Q: Ord + ?Sized,
    {
        self.items.get_entry(value).map(|(value, ())| value)
    }

    /// Inserts a new value into the set
    ///
    /// If the set did not have this value present, `true` is returned.
    ///
    /// If the set did have this value present, `false` is returned, and the entry is not updated.
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTSet;
    ///
    /// let mut set = BSTSet::new();
    /// # assert!(set.is_empty());
    /// assert!(set.insert(37));
    /// assert!(!set.is_empty());
    ///
    /// set.insert(37);
    /// assert!(!set.insert(37));
    /// assert!(set.contains(&37));
    /// ```
    pub fn insert(&mut self, value: T) -> bool {
        self.items.insert(value, ()).is_none()
    }

    /// Removes a value from the set. Returns whether the value was present in the set.
    ///
    /// The value may be any borrowed form of the set's value type, but the ordering on the borrowed
    /// form must match the ordering on the value type.
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTSet;
    ///
    /// let mut set = BSTSet::new();
    /// set.insert(String::from("abc"));
    /// assert!(set.remove("abc"));
    /// assert!(!set.remove("def"));
    /// ```
    pub fn remove<Q>(&mut self, value: &Q) -> bool
        where T: Borrow<Q>,
              Q: Ord + ?Sized,
    {
        self.take(value).is_some()
    }

    /// Removes and returns the value in the set, if any, that is equal to the given one.
    ///
    /// The value may be any borrowed form of the set's value type, but the ordering on the borrowed
    /// form must match the ordering on the value type.
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTSet;
    ///
    /// let mut set = BSTSet::new();
    /// set.insert(String::from("abc"));
    /// assert_eq!(set.take("abc"), Some(String::from("abc")));
    /// assert_eq!(set.take("def"), None);
    /// ```
    pub fn take<Q>(&mut self, value: &Q) -> Option<T>
        where T: Borrow<Q>,
              Q: Ord + ?Sized,
    {
        self.items.remove_entry(value).map(|(value, ())| value)
    }

    /// Clears the set, removing all elements
    ///
    /// Note that this method has no effect on the allocated capacity of the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::BSTSet;
    ///
    /// let mut set = BSTSet::new();
    /// set.insert("abc");
    /// # let capacity = set.capacity();
    /// assert!(!set.is_empty());
    /// set.clear();
    /// assert!(set.is_empty());
    /// # assert_eq!(set.capacity(), capacity);
    /// ```
    pub fn clear(&mut self) {
        self.items.clear();
    }

    /// Performs a pre-order traversal of the tree
    pub fn iter_preorder(&self) -> IterPreorder<T> {
        IterPreorder::new(&self.items)
    }

    /// Performs an in-order traversal of the tree
    pub fn iter_inorder(&self) -> IterInorder<T> {
        IterInorder::new(&self.items)
    }

    /// Performs a post-order traversal of the tree
    pub fn iter_postorder(&self) -> IterPostorder<T> {
        IterPostorder::new(&self.items)
    }

    /// Returns the root node of the tree, or `None` if the tree is empty
    ///
    /// Note that the root can be **any** node inserted into the tree. This may change depending on
    /// the self-balancing characteristics of the implementation. For a guaranteed ordering, use the
    /// various iteration methods.
    ///
    /// This is a low-level API meant to be used for implementing traversals. The inner structure of
    /// the tree can be anything that satisfies the BST properties.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use bst::{BSTSet, set::Node};
    ///
    /// #[derive(Debug, PartialOrd, Ord, PartialEq, Eq)]
    /// struct Person {
    ///     pub name: String,
    ///     // ...other fields...
    /// }
    ///
    /// // Custom traversal through the values in the set
    /// fn find_name<'a>(node: Option<Node<'a, Person>>, target_name: &str) -> Option<Node<'a, Person>> {
    ///     let node = node?;
    ///     if node.value().name == target_name {
    ///         Some(node)
    ///     } else {
    ///         // Recurse through left and right subtrees, just like you would in a GC'd language!
    ///         find_name(node.left(), target_name)
    ///             .or_else(|| find_name(node.right(), target_name))
    ///     }
    /// }
    ///
    /// fn main() {
    ///     let mut set = BSTSet::new();
    ///
    ///     set.insert(Person {
    ///         name: String::from("Manish"),
    ///         // ...other fields...
    ///     });
    ///     // ...more insertions...
    ///
    ///     // Find the node with name == "Jane"
    ///     println!("{:?}", find_name(set.root(), "Jane"));
    /// }
    /// ```
    pub fn root(&self) -> Option<Node<T>> {
        self.items.root().map(Node::new)
    }

    /// Reserves capacity for at least `additional` more elements to be inserted in the set. The
    /// collection may reserve more space to avoid frequent reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows `usize`.
    pub fn reserve(&mut self, additional: usize) {
        self.items.reserve(additional)
    }

    /// Shrinks the capacity of the set as much as possible. It will drop down as much as possible
    /// while maintaining the internal rules and possibly leaving some space in accordance with the
    /// resize policy.
    pub fn shrink_to_fit(&mut self) {
        self.items.shrink_to_fit()
    }
}

impl<T: Ord> Extend<T> for BSTSet<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.items.extend(iter.into_iter().map(|value| (value, ())))
    }
}

impl<T: Ord> FromIterator<T> for BSTSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self {
            items: iter.into_iter().map(|value| (value, ())).collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::collections::HashSet;

    use rand::prelude::*;

    #[test]
    fn test_set_insert_get() {
        let mut set = BSTSet::new();

        assert!(!set.contains(&3));
        assert!(set.insert(3));
        assert!(set.contains(&3));

        assert!(!set.contains(&4));
        assert!(set.insert(4));
        assert!(set.contains(&3));
        assert!(set.contains(&4));

        assert!(!set.contains(&0));
        assert!(set.insert(0));
        assert!(set.contains(&3));
        assert!(set.contains(&4));
        assert!(set.contains(&0));
    }

    #[test]
    fn test_set_insert_replace() {
        let mut set = BSTSet::new();

        assert!(!set.contains(&3));
        assert!(set.insert(3));
        assert!(set.contains(&3));

        assert!(!set.contains(&4));
        assert!(set.insert(4));
        assert!(set.contains(&3));
        assert!(set.contains(&4));

        assert!(!set.insert(3));
        assert!(set.contains(&3));
        assert!(set.contains(&4));

        assert!(!set.insert(4));
        assert!(set.contains(&3));
        assert!(set.contains(&4));
    }

    #[test]
    fn test_set_insert_get_borrow() {
        let mut set: BSTSet<String> = BSTSet::new();

        assert!(!set.contains("abc"));
        assert!(set.insert("abc".to_string()));
        assert!(set.contains("abc"));

        assert!(!set.contains("COOL"));
        assert!(set.insert("COOL".to_string()));
        assert!(set.contains("abc"));
        assert!(set.contains("COOL"));

        assert!(!set.contains(""));
        assert!(set.insert("".to_string()));
        assert!(set.contains("abc"));
        assert!(set.contains("COOL"));
        assert!(set.contains(""));
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
            let mut set = BSTSet::new();
            // Compare against a HashSet
            let mut expected = HashSet::new();
            // The list of values that have been inserted
            let mut values = Vec::new();

            let mut rng = rand::thread_rng();
            for _ in 0..rng.gen_range(OPERATIONS..=OPERATIONS*2) {
                assert_eq!(set.is_empty(), expected.is_empty());
                assert_eq!(set.len(), expected.len());

                match rng.gen_range(1..=100) {
                    // Check for a value that hasn't been inserted
                    1..=20 => {
                        // Not inserting any negative numbers
                        let value = -rng.gen_range(1..=64);
                        assert_eq!(set.contains(&value), expected.contains(&value));
                        assert_eq!(set.get(&value), expected.get(&value));
                    },

                    // Check for a value that has been inserted
                    21..=40 => {
                        let value = match values.choose(&mut rng).copied() {
                            Some(value) => value,
                            None => continue,
                        };

                        assert_eq!(set.contains(&value), expected.contains(&value));
                        assert_eq!(set.get(&value), expected.get(&value));
                    },

                    // Remove an existing value
                    41..=60 => {
                        let value = match values.choose(&mut rng).copied() {
                            Some(value) => value,
                            None => continue,
                        };

                        assert_eq!(set.take(&value), expected.take(&value));
                        // Should always return `None`
                        assert_eq!(set.take(&value), expected.take(&value));
                        // Should always be `false` since value has been removed already
                        assert_eq!(set.remove(&value), expected.remove(&value));
                    },

                    // Insert a value
                    61..=100 => {
                        // Only inserting positive values
                        let value = rng.gen_range(0..=64);
                        values.push(value);

                        assert_eq!(set.contains(&value), expected.contains(&value));
                        assert_eq!(set.get(&value), expected.get(&value));

                        assert_eq!(set.insert(value), expected.insert(value));

                        assert_eq!(set.contains(&value), expected.contains(&value));
                        assert_eq!(set.get(&value), expected.get(&value));
                    },

                    _ => unreachable!(),
                }
            }

            for &value in &values {
                assert_eq!(set.contains(&value), expected.contains(&value));
                assert_eq!(set.get(&value), expected.get(&value));
            }

            set.clear();
            expected.clear();

            assert_eq!(set.is_empty(), expected.is_empty());
            assert_eq!(set.len(), expected.len());

            for &value in &values {
                assert_eq!(set.contains(&value), expected.contains(&value));
                assert_eq!(set.get(&value), expected.get(&value));
            }
        }
    }

    #[test]
    fn traversals() {
        //TODO: This test is brittle and relies on insertion behaviour. Really we want to encode the
        // shape of the tree in the test itself. Maybe with some unsafe `with_tree_structure`
        // constructor for BSTSet or something.

        let mut set = BSTSet::new();
        // Create the following tree:
        //      4
        //   2     5
        // 1   3
        //
        // Inserting the tree one level at a time so it makes this shape:
        set.insert(4);
        set.insert(5);
        set.insert(2);
        set.insert(3);
        set.insert(1);

        let values: Vec<_> = set.iter_preorder().copied().collect();
        assert_eq!(&values, &[4, 2, 1, 3, 5]);

        let values: Vec<_> = set.iter_inorder().copied().collect();
        assert_eq!(&values, &[1, 2, 3, 4, 5]);

        let values: Vec<_> = set.iter_postorder().copied().collect();
        assert_eq!(&values, &[1, 3, 2, 5, 4]);
    }

    #[test]
    fn test_custom_traversal() {
        #[derive(Debug, PartialOrd, Ord, PartialEq, Eq)]
        struct Person {
            pub name: String,
        }

        // Custom traversal through the values in the set
        fn find_name<'a>(node: Option<Node<'a, Person>>, target_name: &str) -> Option<Node<'a, Person>> {
            let node = node?;
            if node.value().name == target_name {
                Some(node)
            } else {
                // Recurse through left and right subtrees, just like you would in a GC'd language!
                find_name(node.left(), target_name)
                    .or_else(|| find_name(node.right(), target_name))
            }
        }

        let mut set = BSTSet::new();

        set.insert(Person {
            name: String::from("Manish"),
        });

        fn get_name(node: Option<Node<Person>>) -> Option<&str> {
            node.map(|node| &*node.value().name)
        }

        // Find the node with name == "Jane"
        assert_eq!(get_name(find_name(set.root(), "Jane")), None);
        assert_eq!(get_name(find_name(set.root(), "Manish")), Some("Manish"));
    }
}

# Binary Search Tree (BST)

This library implements a map type `BSTMap` and a set type `BSTSet` (coming soon!) based on a binary
search tree. The API is designed to be similar in usage to types like `HashMap`/`HashSet` and
`BTreeMap`/`BTreeSet` while also providing the ability to implement your own traversals using lower
level `root` and `root_mut` methods.

Rather than performing an allocation per node, these data structures are backed by a `Vec` which
only allocates occasionally to increase its capacity. Indexes are used internally to keep node IDs
from being invalidated. All of these details are completely hidden in the API. The `root` and
`root_mut` methods return types that provide `left` and `right` methods for convenient and intuitive
traversal through the tree. It almost feels like the tree API you would expect in a garbage
collected language, but without the extra overhead and with all the usual protections of the Rust
borrow checker.

```rust
use bst::BSTMap;

#[derive(Debug, PartialEq, Eq)]
struct Stats {
    pub score: u32,
    // ...other fields...
}

// Custom traversal through the values in the map
fn find_score(node: Option<BSTNode<i32, Stats>>, target_score: u32) -> Option<BSTNode<i32, Stats>> {
    let node = node?;
    if node.value().score == target_score {
        Some(node)
    } else {
        // Recurse through left and right subtrees, just like you would in a GC'd language!
        find_score(node.left(), target_score)
            .or_else(|| find_score(node.right(), target_score))
    }
}

fn main() {
    let mut map = BSTMap::new();

    map.insert(1, Stats {
        score: 39382,
        // ...other fields...
    });
    // ...more insertions...

    // Find the node with score == 500
    println!("{:?}", find_score(map.root(), 500));
}
```

## Implementation Progress

- [ ] `BSTMap`
    - [x] `new` / `default`
    - [x] `with_capacity`
    - [x] `reserve`
    - [x] `shrink_to_fit`
    - [x] `len` / `is_empty`
    - [x] `get` / `get_mut`
    - [ ] `get_entry` / `get_entry_mut` - return `Option<(&K, &V)>` and `Option<(&K, &mut V)>` respectively
    - [x] `contains_key`
    - [x] `insert`
    - [ ] `remove`
    - [ ] `remove_entry`
    - [ ] `retain` - arbitrary order?
    - [x] `clear`
    - [x] `iter_preorder` - pre-order traversal
    - [x] `iter_inorder` - in-order traversal
    - [x] `iter_postorder` - post-order traversal
    - [ ] `iter_mut_preorder` - pre-order traversal (mutable)
    - [ ] `iter_mut_inorder` - in-order traversal (mutable)
    - [ ] `iter_mut_postorder` - post-order traversal (mutable)
    - [x] `root` - returns the root node of the tree and allows you to traverse all nodes
    - [x] `root_mut` - returns the root node of the tree and allows you to traverse all nodes (mutable)
    - [ ] `extend` - `Extend` trait
    - [ ] `append`
    - [ ] `entry`
    - [ ] `keys` / `values` / `values_mut` - might not be needed? arbitrary order?
    - [ ] self-balancing via AVL or red/black or something else
    - [ ] proper `Debug` impls for all public types
    - [ ] implement other traits from `std::iter` on iterators (e.g. `ExactSizeIterator` or `FusedIterator`)
- [ ] `BSTSet` - implemented as an API over `BSTMap<K, ()>`

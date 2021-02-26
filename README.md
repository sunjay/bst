# Binary Search Tree (BST)

[![Build Status](https://github.com/sunjay/bst/workflows/CI/badge.svg)](https://github.com/sunjay/bst/actions)
[![Line Count](https://tokei.rs/b1/github/sunjay/bst)](https://github.com/sunjay/bst)

This library implements a map type `BSTMap` and a set type `BSTSet` based on a binary search tree.
The API is designed to be similar in usage to types like `HashMap`/`HashSet` and
`BTreeMap`/`BTreeSet` while also providing the ability to implement your own traversals using the
lower level `root` and `root_mut` methods.

Rather than performing an allocation per node, these data structures are backed by an arena
allocator that only allocates occasionally to increase its capacity. The arena allocates memory in
chunks without invalidating any addresses it previously produced. This is great for insertion
performance since we don't have to copy and update all the previously allocated nodes every time we
need more space. There is also a good probability that the nodes you are operating on are laid out
contiguously in memory which is great for cache locality.

The `root` and `root_mut` methods return types that provide `left` and `right` methods for
convenient and intuitive traversal through the tree. It almost feels like the tree API you would
expect in a garbage collected language, but without the extra overhead and with all the usual
protections of the Rust borrow checker.

```rust
use bst::{BSTMap, map::Node};

#[derive(Debug, PartialEq, Eq)]
struct Stats {
    pub score: u32,
    // ...other fields...
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

- [x] `BSTMap`
    - [x] `new` / `default`
    - [x] `with_capacity`
    - [x] `capacity`
    - [x] `reserve`
    - [x] `shrink_to_fit`
    - [x] `len` / `is_empty`
    - [x] `get` / `get_mut`
    - [x] `get_entry` - returns `Option<(&K, &V)>`
    - [ ] `get_entry_mut` - returns `Option<(&K, &mut V)>`
    - [ ] `entry`
    - [x] `contains_key`
    - [x] `insert`
    - [x] `remove`
    - [x] `remove_entry`
    - [ ] `retain` - arbitrary order?
    - [x] `clear`
    - [x] `iter_preorder` - pre-order traversal
    - [x] `iter_inorder` - in-order traversal
    - [x] `iter_postorder` - post-order traversal
    - [ ] `iter_mut_preorder` - pre-order traversal (mutable)
    - [ ] `iter_mut_inorder` - in-order traversal (mutable)
    - [ ] `iter_mut_postorder` - post-order traversal (mutable)
    - [ ] `into_iter_preorder` - pre-order traversal (owned)
    - [ ] `into_iter_inorder` - in-order traversal (owned)
    - [ ] `into_iter_postorder` - post-order traversal (owned)
    - [x] `root` - returns the root node of the tree and allows you to traverse all nodes
    - [x] `root_mut` - returns the root node of the tree and allows you to traverse all nodes (mutable)
    - [x] `FromIterator` trait
    - [x] `Extend` trait
    - [ ] `append`
    - [ ] `keys` / `values` / `values_mut` - might not be needed? arbitrary order?
    - [ ] self-balancing via AVL or red/black or something else
    - [x] `Debug` impls for public types that don't expose implementation details
    - [x] implement other traits from `std::iter` on iterators (e.g. `ExactSizeIterator` or `FusedIterator`)
- [x] `BSTSet` - implemented as an API over `BSTMap<K, ()>`
    - [x] `new` / `default`
    - [x] `with_capacity`
    - [x] `capacity`
    - [x] `reserve`
    - [x] `shrink_to_fit`
    - [x] `len` / `is_empty`
    - [x] `get`
    - [x] `contains`
    - [x] `insert`
    - [x] `remove`
    - [x] `take`
    - [ ] `retain` - arbitrary order?
    - [x] `clear`
    - [x] `iter_preorder` - pre-order traversal
    - [x] `iter_inorder` - in-order traversal
    - [x] `iter_postorder` - post-order traversal
    - [ ] `into_iter_preorder` - pre-order traversal (owned)
    - [ ] `into_iter_inorder` - in-order traversal (owned)
    - [ ] `into_iter_postorder` - post-order traversal (owned)
    - [x] `root` - returns the root node of the tree and allows you to traverse all nodes
    - [x] `FromIterator` trait
    - [x] `Extend` trait
    - [ ] `append`
    - [x] `Debug` impls for public types that don't expose implementation details
    - [x] implement other traits from `std::iter` on iterators (e.g. `ExactSizeIterator` or `FusedIterator`)

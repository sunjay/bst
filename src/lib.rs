pub mod map;
pub mod set;

pub use map::BSTMap;
pub use set::BSTSet;

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

#[macro_export(local_inner_macros)]
macro_rules! bstset {
    (@single $($x:tt)*) => (());
    (@count $($rest:expr),*) => (<[()]>::len(&[$(bstset!(@single $rest)),*]));

    ($($key:expr,)+) => { bstset!($($key),+) };
    ($($key:expr),*) => {
        {
            let _cap = bstset!(@count $($key),*);
            let mut _set = $crate::BSTSet::with_capacity(_cap);
            $(
                let _ = _set.insert($key);
            )*
            _set
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bstmap_macro() {
        let map = bstmap! {
            1 => 2,
            3 => 4,
            2 => 3, // trailing comma
        };

        let pairs: Vec<(_, _)> = map.iter_inorder()
            .map(|(&key, &value)| (key, value))
            .collect();
        assert_eq!(&pairs, &[(1, 2), (2, 3), (3, 4)]);

        // No trailing comma
        let map = bstmap![3 => 4];

        let pairs: Vec<(_, _)> = map.iter_inorder()
            .map(|(&key, &value)| (key, value))
            .collect();
        assert_eq!(&pairs, &[(3, 4)]);

        // Zero items
        let map = bstmap!();

        let pairs: Vec<(i32, i32)> = map.iter_inorder()
            .map(|(&key, &value)| (key, value))
            .collect();
        assert_eq!(&pairs, &[]);
    }

    #[test]
    fn bstset_macro() {
        let set = bstset! {
            1,
            3,
            2, // trailing comma
        };

        let items: Vec<_> = set.iter_inorder().copied().collect();
        assert_eq!(&items, &[1, 2, 3]);

        // No trailing comma
        let set = bstset![99];

        let items: Vec<_> = set.iter_inorder().copied().collect();
        assert_eq!(&items, &[99]);

        // Zero items
        let set = bstset!();

        let items: Vec<i32> = set.iter_inorder().copied().collect();
        assert_eq!(&items, &[]);
    }
}

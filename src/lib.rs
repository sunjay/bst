pub mod map;

pub use map::BSTMap;

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

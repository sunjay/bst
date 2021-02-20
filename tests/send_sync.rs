//! Based on: https://github.com/tokio-rs/tokio/blob/d74d17307dd53215061c4a8a1f20a0e30461e296/tokio/tests/async_send_sync.rs

#![warn(rust_2018_idioms)]

use std::{any::Any, cell::Cell};
use std::rc::Rc;

use bst::{BSTMap, BSTSet, map, set};

fn require_send<T: Send>(_t: &T) {}
fn require_sync<T: Sync>(_t: &T) {}

struct NotSend {
    _a: Box<dyn Any + Sync>,
}

impl PartialEq for NotSend {
    fn eq(&self, _other: &Self) -> bool {
        false
    }
}

impl Eq for NotSend {}

impl PartialOrd for NotSend {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for NotSend {
    fn cmp(&self, _other: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

struct Invalid;

trait AmbiguousIfSend<A> {
    fn some_item(&self) {}
}
impl<T: ?Sized> AmbiguousIfSend<()> for T {}
impl<T: ?Sized + Send> AmbiguousIfSend<Invalid> for T {}

trait AmbiguousIfSync<A> {
    fn some_item(&self) {}
}
impl<T: ?Sized> AmbiguousIfSync<()> for T {}
impl<T: ?Sized + Sync> AmbiguousIfSync<Invalid> for T {}

trait AmbiguousIfUnpin<A> {
    fn some_item(&self) {}
}
impl<T: ?Sized> AmbiguousIfUnpin<()> for T {}
impl<T: ?Sized + Unpin> AmbiguousIfUnpin<Invalid> for T {}

macro_rules! assert_value {
    ($type:ty: Send & Sync) => {
        #[allow(unreachable_code)]
        #[allow(unused_variables)]
        pub const _: fn() = || {
            let f: $type = todo!();
            require_send(&f);
            require_sync(&f);
        };
    };
    ($type:ty: !Send & Sync) => {
        #[allow(unreachable_code)]
        #[allow(unused_variables)]
        pub const _: fn() = || {
            let f: $type = todo!();
            AmbiguousIfSend::some_item(&f);
            require_sync(&f);
        };
    };
    ($type:ty: Send & !Sync) => {
        #[allow(unreachable_code)]
        #[allow(unused_variables)]
        pub const _: fn() = || {
            let f: $type = todo!();
            require_send(&f);
            AmbiguousIfSync::some_item(&f);
        };
    };
    ($type:ty: !Send & !Sync) => {
        #[allow(unreachable_code)]
        #[allow(unused_variables)]
        pub const _: fn() = || {
            let f: $type = todo!();
            AmbiguousIfSend::some_item(&f);
            AmbiguousIfSync::some_item(&f);
        };
    };
}

assert_value!(BSTMap<i32, i32>: Send & Sync);
assert_value!(BSTMap<Rc<i32>, i32>: !Send & !Sync);
assert_value!(BSTMap<Cell<i32>, i32>: Send & !Sync);
assert_value!(BSTMap<i32, NotSend>: !Send & Sync);

assert_value!(map::Node<'_, i32, i32>: Send & Sync);
assert_value!(map::Node<'_, Rc<i32>, i32>: !Send & !Sync);
assert_value!(map::Node<'_, Cell<i32>, i32>: !Send & !Sync);
assert_value!(map::Node<'_, i32, NotSend>: Send & Sync);

assert_value!(map::NodeMut<'_, i32, i32>: Send & Sync);
assert_value!(map::NodeMut<'_, Rc<i32>, i32>: !Send & !Sync);
assert_value!(map::NodeMut<'_, Cell<i32>, i32>: Send & !Sync);
assert_value!(map::NodeMut<'_, i32, NotSend>: !Send & Sync);

assert_value!(map::IterPreorder<'_, i32, i32>: Send & Sync);
assert_value!(map::IterPreorder<'_, Rc<i32>, i32>: !Send & !Sync);
assert_value!(map::IterPreorder<'_, Cell<i32>, i32>: !Send & !Sync);
assert_value!(map::IterPreorder<'_, i32, NotSend>: Send & Sync);

assert_value!(map::IterInorder<'_, i32, i32>: Send & Sync);
assert_value!(map::IterInorder<'_, Rc<i32>, i32>: !Send & !Sync);
assert_value!(map::IterInorder<'_, Cell<i32>, i32>: !Send & !Sync);
assert_value!(map::IterInorder<'_, i32, NotSend>: Send & Sync);

assert_value!(map::IterPostorder<'_, i32, i32>: Send & Sync);
assert_value!(map::IterPostorder<'_, Rc<i32>, i32>: !Send & !Sync);
assert_value!(map::IterPostorder<'_, Cell<i32>, i32>: !Send & !Sync);
assert_value!(map::IterPostorder<'_, i32, NotSend>: Send & Sync);

assert_value!(BSTSet<i32>: Send & Sync);
assert_value!(BSTSet<Rc<i32>>: !Send & !Sync);
assert_value!(BSTSet<Cell<i32>>: Send & !Sync);
assert_value!(BSTSet<NotSend>: !Send & Sync);

assert_value!(set::Node<'_, i32>: Send & Sync);
assert_value!(set::Node<'_, Rc<i32>>: !Send & !Sync);
assert_value!(set::Node<'_, Cell<i32>>: !Send & !Sync);
assert_value!(set::Node<'_, NotSend>: Send & Sync);

assert_value!(set::IterPreorder<'_, i32>: Send & Sync);
assert_value!(set::IterPreorder<'_, Rc<i32>>: !Send & !Sync);
assert_value!(set::IterPreorder<'_, Cell<i32>>: !Send & !Sync);
assert_value!(set::IterPreorder<'_, NotSend>: Send & Sync);

assert_value!(set::IterInorder<'_, i32>: Send & Sync);
assert_value!(set::IterInorder<'_, Rc<i32>>: !Send & !Sync);
assert_value!(set::IterInorder<'_, Cell<i32>>: !Send & !Sync);
assert_value!(set::IterInorder<'_, NotSend>: Send & Sync);

assert_value!(set::IterPostorder<'_, i32>: Send & Sync);
assert_value!(set::IterPostorder<'_, Rc<i32>>: !Send & !Sync);
assert_value!(set::IterPostorder<'_, Cell<i32>>: !Send & !Sync);
assert_value!(set::IterPostorder<'_, NotSend>: Send & Sync);

use std::mem::{self, ManuallyDrop};
use std::marker::PhantomData;

// Source: https://docs.rs/static_assertions/1.1.0/src/static_assertions/const_assert.rs.html#52-57
#[macro_export]
macro_rules! const_assert {
    ($x:expr $(,)?) => {
        #[allow(unknown_lints, eq_op)]
        const _: [(); 0 - !{ const ASSERT: bool = $x; ASSERT } as usize] = [];
    };
}

#[macro_export]
macro_rules! const_assert_eq {
    ($x:expr, $y:expr $(,)?) => {
        const_assert!($x == $y);
    };
}

/// An index into a slab, or "null"
///
/// This type is essentially `Option<usize>`. The value usize::MAX is
/// reserved to represent `None` or "null".
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Ptr(usize);

// We've designed `Ptr` to use as little space as possible to help with cache
const_assert_eq!(mem::size_of::<Ptr>(), 8);
// Using `Option<usize>` directly would use more space.
const_assert_eq!(mem::size_of::<Option<usize>>(), 16);

impl Default for Ptr {
    #[inline(always)]
    fn default() -> Self {
        Self::null()
    }
}

impl Ptr {
    #[inline(always)]
    fn new(index: usize) -> Option<Self> {
        if index == usize::MAX {
            None
        } else {
            Some(Ptr(index))
        }
    }

    #[inline(always)]
    pub unsafe fn new_unchecked(index: usize) -> Self {
        Ptr(index)
    }

    #[inline(always)]
    pub fn null() -> Self {
        Ptr(usize::MAX)
    }

    // Methods on this type must be `#[inline]` to help the compiler see that the `Option` values
    // are only intermediate values used to make writing code easier. Instead of checking for `None`
    // and then `usize::MAX`, we want the compiler to just check the latter.
    #[inline(always)]
    pub fn into_index(self) -> Option<usize> {
        let Ptr(index) = self;
        if index == usize::MAX {
            None
        } else {
            Some(index)
        }
    }

    #[inline(always)]
    pub fn is_null(self) -> bool {
        self.0 == usize::MAX
    }
}


#[repr(C)]
union Entry<T> {
    value: ManuallyDrop<T>,
    free: FreeEntry,
}

// It is important to assert that the compiler thinks that any entry (even an entry with a type that
// needs to be dropped) does not need to be dropped. This is necessary because we manually drop each
// entry and we do not want the entry to be dropped twice. Having this also enables some important
// performance improvements since `Vec` may do less work when the inner type does not need to be
// dropped.
const_assert!(!mem::needs_drop::<Entry<Vec<i32>>>());
// Explicitly tracking the size of entry because we want to limit the overhead added to each entry
// because of the free list implementation.
const_assert_eq!(mem::size_of::<Entry<()>>(), 8); // max of 8 bytes overhead per entry

/// An item in the free list
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct FreeEntry {
    /// The index of the next entry in the free list or `Ptr::null()` if this is the last entry in
    /// the free list
    next: Ptr,
}

/// An allocation primitive similar to `Vec`, but implemented to reuse space from removed entries.
///
/// Items are kept contiguously in memory, but indexes are not shifted when an individual item is
/// removed. Instead of always pushing items after the previously pushed item, this data structure
/// will reuse space from previously removed entries when possible. This makes removal cheaper than
/// a standard `Vec<T>`.
///
/// The slab is unsafe because it does not explicitly add data to each entry to track whether it was
/// previously removed. That means that it is possible to call one of the unsafe get methods using
/// an index to memory that is no longer considered initialized.
pub struct UnsafeSlab<T> {
    items: Vec<Entry<T>>,
    /// The index of the first entry in the free list or Ptr::null() if the free list is empty
    ///
    /// The free list is a linked list stored in `items` that is used as a stack to track which
    /// entries have space that can be reused in calls to `push`. This is an internal-only
    /// implementation detail and no methods make guarantees about how the free list will be
    /// manipulated.
    free_list_head: Ptr,
    /// The length of the free list
    free_len: usize,
    // NOTE: this marker has no consequences for variance, but is necessary for the drop checker to
    // understand that we logically own a `T`. Needed because of our use of `ManuallyDrop<T>`.
    //
    // For details, see:
    // https://forge.rust-lang.org/libs/maintaining-std.html#is-there-a-manual-drop-implementation
    // https://github.com/rust-lang/rfcs/blob/master/text/0769-sound-generic-drop.md#phantom-data
    _marker: PhantomData<T>,
}

impl<T> Default for UnsafeSlab<T> {
    fn default() -> Self {
        Self {
            items: Vec::default(),
            free_list_head: Ptr::null(),
            free_len: 0,
            _marker: PhantomData,
        }
    }
}

impl<T> UnsafeSlab<T> {
    /// Creates an empty slab
    ///
    /// The slab is initially created with a capacity of 0, so it will not allocate until it is
    /// first inserted into.
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates an empty slab with the specified capacity.
    ///
    /// The slab will be able to hold at least `capacity` elements without reallocating. If
    /// `capacity` is 0, the slab will not allocate.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            items: Vec::with_capacity(capacity),
            ..Self::default()
        }
    }

    /// Returns the number of entries that contain values
    pub fn len(&self) -> usize {
        self.items.len() - self.free_len
    }

    /// Returns true if the slab is empty
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the number of elements the slab can hold without reallocating.
    ///
    /// This number is a lower bound; the slab might be able to hold more, but is guaranteed to be
    /// able to hold at least this many.
    pub fn capacity(&self) -> usize {
        self.items.capacity()
    }

    /// Returns a reference to a value in the slab
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index or an index that was previously removed is
    /// undefined behavior even if the resulting reference is not used.
    pub unsafe fn get_unchecked(&self, index: usize) -> &T {
        &self.items.get_unchecked(index).value
    }

    /// Returns a mutable reference to a value in the slab
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index or an index that was previously removed is
    /// undefined behavior even if the resulting reference is not used.
    pub unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut T {
        &mut self.items.get_unchecked_mut(index).value
    }

    /// Pushes a value into the slab and returns the index at which it was inserted.
    ///
    /// The item may be inserted at the end of the list, or in the space from an item was previously
    /// removed. Indexes returned from this method are considered valid for use with the get
    /// methods.
    pub fn push(&mut self, value: T) -> usize {
        // Check if we can reuse some space from the free list
        if let Some(free_list_head) = self.free_list_head.into_index() {
            // Safety: Items on the free list are guaranteed to be valid indexes
            let entry = unsafe { self.items.get_unchecked_mut(free_list_head) };

            // Update the free list to point to the next free list entry
            // Safety: All items on the free list are guaranteed to be FreeEntry structs
            let next_free = unsafe { entry.free }.next;
            self.free_list_head = next_free;
            self.free_len -= 1;

            // No need to worry about dropping FreeEntry because it is Copy
            *entry = Entry {value: ManuallyDrop::new(value)};

            return free_list_head;
        }

        let index = self.items.len();
        // Since we store `Ptr` internally, we can't have usize::MAX as a valid index into the slab
        if index >= usize::MAX {
            panic!("cannot have more than usize::MAX - 1 entries in slab");
        }

        self.items.push(Entry {value: ManuallyDrop::new(value)});

        index
    }

    /// Removes an item from the slab, returning its value.
    ///
    /// Note that this method has no effect on the allocated capacity of the slab.
    ///
    /// The space for the item will be reused in future calls to `push`. This does not move or
    /// modify any other entries in the slab. Their indexes remain the same and can still be used.
    ///
    /// Use `clear` (and possibly `shrink_to_fit`) to reclaim the space used by removed entries.
    pub unsafe fn remove(&mut self, index: usize) -> T {
        //TODO: If removing this makes len() == 0, we can clear the free list
        //TODO: If removing from the end of the slab, we may be able to call `set_len` instead of
        //      using the free list
        let entry = self.items.get_unchecked_mut(index);
        let prev_value = mem::replace(entry, Entry {
            free: FreeEntry {next: self.free_list_head},
        });
        self.free_list_head = Ptr::new_unchecked(index);
        self.free_len += 1;
        ManuallyDrop::into_inner(prev_value.value)
    }

    /// Clears the slab, removing all values.
    ///
    /// Note that this method has no effect on the allocated capacity of the slab.
    ///
    /// This invalidates all previous indexes returned from `push`.
    pub fn clear(&mut self) {
        use std::collections::HashSet;

        // If all items have already been freed, we don't need to do anything
        if self.items.len() == self.free_len {
            return;
        }

        // Record the indexes that are in the free list so we don't need to iterate through it over
        // and over again as we go through each entry in the slab to drop them all
        //TODO: We can use `bitvec::BitVec` instead of `HashSet` to save on space
        let mut free_indexes = HashSet::with_capacity(self.free_len);

        let mut current = self.free_list_head;
        while let Some(index) = current.into_index() {
            free_indexes.insert(index);

            // Safety: Items on the free list are guaranteed to be valid indexes
            let entry = unsafe { self.items.get_unchecked(index) };
            // Safety: All items on the free list are guaranteed to be FreeEntry structs
            let next_free = unsafe { entry.free }.next;
            current = next_free;
        }

        for index in 0..self.items.len() {
            if free_indexes.contains(&index) {
                continue;
            }

            // Safety: The `index` is between 0 and self.items.len(), so it must be valid
            let entry = unsafe { self.items.get_unchecked_mut(index) };
            // Safety: The item was not on the free list, so it must be a value
            let value = unsafe { &mut entry.value };
            // Safety: This call only happens once because `Entry` must be dropped manually and each
            // `index` is unique
            unsafe { ManuallyDrop::drop(value); }
        }

        let Self {items, free_list_head, free_len, _marker} = self;
        // Clearing `items` has the effect of marking every entry as free without affecting the
        // allocated capacity.
        items.clear();
        // Need to clear the free list so we don't end up indexing out of bounds.
        *free_list_head = Ptr::null();
        *free_len = 0;
    }

    pub fn reserve(&mut self, additional: usize) {
        self.items.reserve(additional)
    }

    //TODO: Provide an API for safe memory compaction (clears the free list while yielding indexes)
    pub fn shrink_to_fit(&mut self) {
        self.items.shrink_to_fit()
    }
}

//TODO: This needs a `#[may_dangle]` attribute on `T`
// See: https://forge.rust-lang.org/libs/maintaining-std.html#is-there-a-manual-drop-implementation
impl<T> Drop for UnsafeSlab<T> {
    fn drop(&mut self) {
        // Fast path: ignore if `T` does not need to be dropped
        if !mem::needs_drop::<T>() {
            return;
        }

        self.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ptr_api() {
        let ptr = Ptr::new(0).unwrap();
        assert_eq!(ptr.into_index(), Some(0));
        assert!(!ptr.is_null());

        let ptr = Ptr::new(1).unwrap();
        assert_eq!(ptr.into_index(), Some(1));
        assert!(!ptr.is_null());

        let ptr = Ptr::new(5).unwrap();
        assert_eq!(ptr.into_index(), Some(5));
        assert!(!ptr.is_null());

        let ptr = Ptr::new(usize::MAX);
        assert_eq!(ptr, None);

        let ptr = Ptr::null();
        assert_eq!(ptr.into_index(), None);
        assert!(ptr.is_null());
    }

    #[test]
    fn slab_push_remove() {
        let mut slab = UnsafeSlab::new();

        assert_eq!(slab.len(), 0);
        assert!(slab.is_empty());
        assert_eq!(slab.capacity(), 0);

        // Push a single value
        let index0 = slab.push(19384);
        assert_eq!(unsafe { *slab.get_unchecked(index0) }, 19384);

        assert_eq!(slab.len(), 1);
        assert!(!slab.is_empty());
        assert!(slab.capacity() > 0);

        // Remove the only value in the slab
        assert_eq!(unsafe { slab.remove(index0) }, 19384);

        assert_eq!(slab.len(), 0);
        assert!(slab.is_empty());
        assert!(slab.capacity() > 0);

        // Push another value
        let index0 = slab.push(831783);
        assert_eq!(unsafe { *slab.get_unchecked(index0) }, 831783);

        assert_eq!(slab.len(), 1);
        assert!(!slab.is_empty());
        assert!(slab.capacity() > 0);

        // Push a second value
        let index1 = slab.push(57);
        assert_eq!(unsafe { *slab.get_unchecked(index0) }, 831783);
        assert_eq!(unsafe { *slab.get_unchecked(index1) }, 57);

        assert_eq!(slab.len(), 2);
        assert!(!slab.is_empty());
        assert!(slab.capacity() > 0);

        // Remove the first value (second should still be available)
        assert_eq!(unsafe { slab.remove(index0) }, 831783);
        assert_eq!(unsafe { *slab.get_unchecked(index1) }, 57);

        assert_eq!(slab.len(), 1);
        assert!(!slab.is_empty());
        assert!(slab.capacity() > 0);

        // Push another value (may end up where the first value was)
        let index2 = slab.push(999);
        assert_eq!(unsafe { *slab.get_unchecked(index1) }, 57);
        assert_eq!(unsafe { *slab.get_unchecked(index2) }, 999);

        assert_eq!(slab.len(), 2);
        assert!(!slab.is_empty());
        assert!(slab.capacity() > 0);

        //TODO: Remove the second value (first value should remain)
        //TODO: Remove the first value
        unimplemented!();
    }

    #[test]
    fn slab_get() {
        //TODO: test `get_unchecked` and `get_unchecked_mut`
        unimplemented!()
    }

    #[test]
    fn slab_clear() {
        let mut slab = UnsafeSlab::new();

        slab.push("abc");
        assert!(!slab.is_empty());
        let capacity = slab.capacity();

        slab.clear();
        assert!(slab.is_empty());
        assert_eq!(slab.capacity(), capacity);

        // clear an empty slab (insertions and removals after this should still work)
        slab.clear();
        assert!(slab.is_empty());
        assert_eq!(slab.capacity(), capacity);

        // push 2 values and remove one, so that clear has to account for the free space
        let index = slab.push("ddd");
        slab.push("fff");
        let capacity = slab.capacity();

        unsafe { slab.remove(index); }

        assert!(!slab.is_empty());
        slab.clear();
        assert!(slab.is_empty());
        assert_eq!(slab.capacity(), capacity);
    }

    #[test]
    fn drop_non_empty() {
        use std::sync::Arc;

        let mut slab = UnsafeSlab::new();

        let weak_ref1;
        let weak_ref2;
        {
            let value1 = Arc::new(1);
            let value2 = Arc::new(2);
            weak_ref1 = Arc::downgrade(&value1);
            weak_ref2 = Arc::downgrade(&value2);

            slab.push(value1);
            slab.push(value2);
        }

        assert_eq!(*weak_ref1.upgrade().unwrap(), 1);
        assert_eq!(*weak_ref2.upgrade().unwrap(), 2);

        drop(slab);

        assert!(weak_ref1.upgrade().is_none());
        assert!(weak_ref2.upgrade().is_none());
    }

    #[test]
    fn drop_removed() {
        use std::sync::Arc;

        let mut slab = UnsafeSlab::new();

        let index0;
        let weak_ref1;
        let weak_ref2;
        {
            let value1 = Arc::new(1);
            let value2 = Arc::new(2);
            weak_ref1 = Arc::downgrade(&value1);
            weak_ref2 = Arc::downgrade(&value2);

            index0 = slab.push(value1);
            slab.push(value2);
        }

        assert_eq!(*weak_ref1.upgrade().unwrap(), 1);
        assert_eq!(*weak_ref2.upgrade().unwrap(), 2);

        let weak_ref3;
        {
            // Drop one of the values via remove, but then reuse the space
            unsafe { slab.remove(index0); }

            let value3 = Arc::new(3);
            weak_ref3 = Arc::downgrade(&value3);

            slab.push(value3);
        }

        assert!(weak_ref1.upgrade().is_none());
        assert_eq!(*weak_ref2.upgrade().unwrap(), 2);
        assert_eq!(*weak_ref3.upgrade().unwrap(), 3);

        // Drop all values
        drop(slab);

        assert!(weak_ref1.upgrade().is_none());
        assert!(weak_ref2.upgrade().is_none());
        // Value that was in the reused space should still be dropped normally
        assert!(weak_ref3.upgrade().is_none());
    }

    #[test]
    fn slab_capacity() {
        //TODO: test `with_capacity`, `capacity`, `reserve` and `shrink_to_fit`
        //TODO: test that all methods that say they don't modify capacity actually don't
        unimplemented!()
    }
}

use std::mem::{self, ManuallyDrop};

/// An index into a slab, or "null"
///
/// This type is essentially `Option<usize>`. The value usize::MAX is
/// reserved to represent `None` or "null".
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Ptr(usize);

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

/// An item in the free list
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct FreeEntry {
    /// The index of the next entry in the free list or `Ptr::null()` if this is the last entry in
    /// the free list
    next_free: Ptr,
}

/// An allocation primitive similar to `Vec`, but implemented with a free list to make removals
/// cheap and to allow freed spots to be reused
///
/// The slab is unsafe because it does not explicitly track whether an individual entry is free or
/// not. That means that certain operations like `get` are always unsafe and unchecked.
pub struct UnsafeSlab<T> {
    items: Vec<Entry<T>>,
    /// The index of the first entry in the free list or Ptr::null() if the free list is empty
    free_list_head: Ptr,
    /// The length of the free list
    free_len: usize,
}

impl<T> Default for UnsafeSlab<T> {
    fn default() -> Self {
        Self {
            items: Vec::default(),
            free_list_head: Ptr::null(),
            free_len: 0,
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

    /// Returns the number of free (removed) slots in the slab
    pub fn free_len(&self) -> usize {
        self.free_len
    }

    /// Returns the number of elements the slab can hold without reallocating.
    ///
    /// This number is a lower bound; the slab might be able to hold more, but is guaranteed to be
    /// able to hold at least this many.
    pub fn capacity(&self) -> usize {
        self.items.capacity()
    }

    pub unsafe fn get_unchecked(&self, index: usize) -> &T {
        &self.items.get_unchecked(index).value
    }

    pub unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut T {
        &mut self.items.get_unchecked_mut(index).value
    }

    pub fn push(&mut self, value: T) -> usize {
        // Check if we can reuse some space from the free list
        if let Some(free_list_head) = self.free_list_head.into_index() {
            // Safety: Items on the free list are guaranteed to be valid indexes
            let entry = unsafe { self.items.get_unchecked_mut(free_list_head) };

            // Update the free list to point to the next free list entry
            // Safety: All items on the free list are guaranteed to be FreeEntry structs
            let next_free = unsafe { entry.free }.next_free;
            self.free_list_head = next_free;
            self.free_len -= 1;

            // No need to worry about dropping FreeEntry because it is Copy
            *entry = Entry {value: ManuallyDrop::new(value)};

            return free_list_head;
        }

        let index = self.items.len();
        if index >= usize::MAX {
            panic!("cannot have more than usize::MAX - 1 entries in slab");
        }

        self.items.push(Entry {value: ManuallyDrop::new(value)});

        index
    }

    pub unsafe fn remove(&mut self, index: usize) -> T {
        let entry = self.items.get_unchecked_mut(index);
        let prev_value = mem::replace(entry, Entry {
            free: FreeEntry {next_free: self.free_list_head},
        });
        self.free_list_head = Ptr::new_unchecked(index);
        self.free_len += 1;
        ManuallyDrop::into_inner(prev_value.value)
    }

    pub fn clear(&mut self) {
        *self = Self::default();
    }

    pub fn reserve(&mut self, additional: usize) {
        self.items.reserve(additional)
    }

    //TODO: Provide an API for safe memory compaction (clears the free list while yielding indexes)
    pub fn shrink_to_fit(&mut self) {
        self.items.shrink_to_fit()
    }
}

impl<T> Drop for UnsafeSlab<T> {
    fn drop(&mut self) {
        // Fast path: ignore if `T` does not need to be dropped
        //                or if all items are free already
        if !mem::needs_drop::<T>() || self.free_len == self.items.len() {
            return;
        }

        use std::collections::HashSet;

        // Record the indexes that are in the free list
        //TODO: We can use `bitvec::BitVec` instead of `HashSet` to save on space
        let mut free_indexes = HashSet::with_capacity(self.free_len);

        let mut current = self.free_list_head;
        while let Some(index) = current.into_index() {
            free_indexes.insert(index);

            // Safety: Items on the free list are guaranteed to be valid indexes
            let entry = unsafe { self.items.get_unchecked(index) };
            // Safety: All items on the free list are guaranteed to be FreeEntry structs
            let next_free = unsafe { entry.free }.next_free;
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
            // Safety: This call only happens once because all indexes are unique
            unsafe { ManuallyDrop::drop(value); }
        }
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
}

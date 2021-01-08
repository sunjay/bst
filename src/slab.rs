use std::mem::{self, ManuallyDrop};

/// An index into a slab, or "null"
///
/// This type is essentially `Option<usize>`. The value usize::MAX is
/// reserved to represent `None` or "null".
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Ptr(usize);

impl Default for Ptr {
    fn default() -> Self {
        Self::null()
    }
}

impl Ptr {
    pub fn new(index: usize) -> Option<Self> {
        if index == usize::MAX {
            None
        } else {
            Some(Ptr(index))
        }
    }

    pub unsafe fn new_unchecked(index: usize) -> Self {
        Ptr(index)
    }

    pub fn null() -> Self {
        Ptr(usize::MAX)
    }

    pub fn into_index(self) -> Option<usize> {
        let Ptr(index) = self;
        if index == usize::MAX {
            None
        } else {
            Some(index)
        }
    }

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
}

impl<T> Default for UnsafeSlab<T> {
    fn default() -> Self {
        Self {
            items: Vec::default(),
            free_list_head: Ptr::null(),
        }
    }
}

impl<T> UnsafeSlab<T> {
    pub fn new() -> Self {
        Self::default()
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
            let next_free = unsafe { entry.free }.next_free;
            self.free_list_head = next_free;

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
        ManuallyDrop::into_inner(prev_value.value)
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
        todo!()
    }
}

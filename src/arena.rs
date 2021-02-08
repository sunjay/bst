use std::fmt;
use std::ptr::NonNull;
use std::mem::{self, MaybeUninit};
use std::marker::PhantomData;

/// The precise location of a value in a chunk
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ChunkPos {
    /// The index of the chunk to look in
    pub chunk_index: usize,
    /// The index within the chunk where the item will be
    pub item_index: usize,
}

trait AllocStrategy {
    /// Returns the length of the chunk with the given index
    fn chunk_len(&self, chunk_i: usize) -> usize;

    /// Returns the precise position of an item in the arena based on its index
    fn position_for(&self, index: usize) -> ChunkPos;
}

#[derive(Debug, Default)]
struct ExponentialAlloc {}

impl ExponentialAlloc {
    //TODO: Replace these with const generics
    const MULTIPLIER: usize = 8;
    const BASE: usize = 2;
}

impl AllocStrategy for ExponentialAlloc {
    fn chunk_len(&self, chunk_i: usize) -> usize {
        Self::MULTIPLIER * Self::BASE.pow(chunk_i as u32)
    }

    fn position_for(&self, index: usize) -> ChunkPos {
        todo!()
    }
}

/// An arena allocator that guarantees that the addresses produced remain usable regardless of how
/// many items are added.
///
/// Similar API to `Vec<T>` except allocating new values never requires copying all the previously
/// allocated values.
pub struct StableArena<T> {
    /// Chunks of allocated memory. Each chunk's size is known without storing it via the allocation
    /// strategy.
    ///
    /// We could use `Box<[...]>` here, but since the aliasing rules are still being worked out,
    /// it's probably easier to just use `NonNull<T>` and handle everything manually. See:
    /// https://github.com/rust-lang/unsafe-code-guidelines/issues/262
    chunks: Vec<NonNull<MaybeUninit<T>>>,

    /// The total number of items that have been pushed into the arena
    ///
    /// All entries with index < len are guaranteed to be initialized in chunks
    len: usize,

    /// This controls how chunks are allocated
    ///
    /// The arena could be generic over `AllocStrategy` but that isn't needed right now.
    strategy: ExponentialAlloc,

    // NOTE: this marker has no consequences for variance, but is necessary for the drop checker to
    // understand that we logically own a `T`. Needed because of our use of `MaybeUninit<T>`.
    //
    // For details, see:
    // https://forge.rust-lang.org/libs/maintaining-std.html#is-there-a-manual-drop-implementation
    // https://github.com/rust-lang/rfcs/blob/master/text/0769-sound-generic-drop.md#phantom-data
    _marker: PhantomData<T>,
}

impl<T> Default for StableArena<T> {
    fn default() -> Self {
        Self {
            chunks: Vec::default(),
            len: 0,
            strategy: ExponentialAlloc::default(),
            _marker: PhantomData,
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for StableArena<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T: PartialEq> PartialEq for StableArena<T> {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter().zip(other.iter()).all(|(v1, v2)| v1.eq(v2))
    }
}

impl<T: Eq> Eq for StableArena<T> {}

impl<T> StableArena<T> {
    /// Creates an empty arena
    ///
    /// The arena is initially created with a capacity of 0, so it will not allocate until it is
    /// first inserted into.
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates an empty arena with the specified capacity.
    ///
    /// The arena will be able to hold at least `capacity` elements without reallocating. If
    /// `capacity` is 0, the arena will not allocate.
    pub fn with_capacity(capacity: usize) -> Self {
        todo!()
    }

    /// Returns the number of entries in the arena that contain a value
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if the arena is empty
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the number of elements the arena can hold without reallocating.
    ///
    /// This number is a lower bound; the arena might be able to hold more, but is guaranteed to be
    /// able to hold at least this many.
    pub fn capacity(&self) -> usize {
        todo!()
    }

    /// Allocates the given value in the arena and returns a stable address to the value
    ///
    /// The returned pointer is guaranteed to be valid as long as no method is called that would
    /// invalidate the pointer (e.g. the `clear` method).
    pub fn alloc(&mut self, value: T) -> NonNull<T> {
        todo!()
    }

    /// Returns an iterator over the arena
    pub fn iter(&self) -> Iter<T> {
        todo!()
    }

    /// Returns an iterator over the arena that allows you to modify each value
    pub fn iter_mut(&mut self) -> IterMut<T> {
        todo!()
    }

    /// Clears the arena, removing all values.
    ///
    /// Note that this method has no effect on the allocated capacity of the arena.
    ///
    /// This invalidates all previous addresses returned from `alloc`.
    pub fn clear(&mut self) {
        todo!()
    }

    /// Reserves capacity for at least `additional` more elements to be inserted in the arena.
    ///
    /// The collection may reserve more space to avoid frequent reallocations. After calling
    /// reserve, capacity will be greater than or equal to `self.len() + additional`. Does nothing
    /// if capacity is already sufficient.
    pub fn reserve(&mut self, additional: usize) {
        todo!()
    }

    /// Shrinks the capacity of the arena as much as possible.
    ///
    /// It will drop down as close as possible to the length but may still be greater.
    pub fn shrink_to_fit(&mut self) {
        todo!()
    }

    /// Forces the length of the arena to the given value.
    ///
    /// This is a low-level operation that maintains none of the normal invariants of the type.
    ///
    /// # Safety
    ///
    /// * The new length must be less than or equal to `capacity()`
    /// * The elements at `old_len..new_len` must be initialized
    pub unsafe fn set_len(&mut self, len: usize) {
        self.len = len;
    }
}

impl<T> IntoIterator for StableArena<T> {
    type Item = T;

    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        todo!()
    }
}

//TODO: This needs a `#[may_dangle]` attribute on `T`
// See: https://forge.rust-lang.org/libs/maintaining-std.html#is-there-a-manual-drop-implementation
impl<T> Drop for StableArena<T> {
    fn drop(&mut self) {
        // Fast path: ignore if `T` does not need to be dropped
        if !mem::needs_drop::<T>() {
            return;
        }

        self.clear();
    }
}

pub struct Iter<'a, T> {
    _marker: PhantomData<&'a T>, //TODO
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

pub struct IterMut<'a, T> {
    _marker: PhantomData<&'a mut T>, //TODO
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

pub struct IntoIter<T> {
    _marker: PhantomData<T>, //TODO
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::rc::Rc;

    #[test]
    fn arena_push() {
        // Addresses yielded by the arena should remain valid regardless of how many times we push

        // This test is O(n^2), so be careful with this number
        const ALLOCS: usize = 1024;

        let mut addrs = Vec::with_capacity(ALLOCS);

        // The arena allocator will resize multiple times during this test
        let mut arena = StableArena::new();
        for i in 0..ALLOCS {
            addrs.push(arena.alloc(Rc::new(i)));

            // Check that all addresses are still valid
            for (j, addr) in addrs.iter().enumerate() {
                unsafe {
                    assert_eq!(**addr.as_ref(), j);
                }
            }
        }
    }
}

use std::fmt;
use std::slice;
use std::ops::Range;
use std::iter::FusedIterator;
use std::ptr::{self, NonNull};
use std::mem::{self, MaybeUninit};
use std::marker::PhantomData;

/// The precise location of a value in a chunk
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ChunkPos {
    /// The index of the chunk to look in
    pub chunk_index: u32,

    /// The index within the chunk where the item will be
    ///
    /// This must be less than the size of the chunk corresponding to `chunk_index`
    pub item_index: usize,
}

/// Trait for defining how chunks are allocated and items are mapped within them
///
/// # Safety
///
/// Implementations must ensure that indexes returned are never out-of-bounds as long as the input
/// index is not out-of-bounds. Sizes returned must be non-zero.
unsafe trait AllocStrategy {
    /// Returns the length of the chunk with the given index
    ///
    /// The chunk length must be greater than zero
    fn chunk_len(&self, chunk_i: u32) -> usize;

    /// Returns the precise position of an item in the arena based on its index
    fn position_for(&self, index: usize) -> ChunkPos;
}

/// Allocates memory using an exponentially growing page size
#[derive(Debug, Default)]
struct ExponentialAlloc {
    _private: (),
}

impl ExponentialAlloc {
    /// An extra multiplier used to scale the page size
    //TODO: Replace this with const generics
    const MULTIPLIER: usize = 8;
}

unsafe impl AllocStrategy for ExponentialAlloc {
    #[inline(always)]
    fn chunk_len(&self, chunk_i: u32) -> usize {
        // This code only works for an exponent base of 2 since we use left shift to emulate a fast
        // `2.pow(chunk_i)` operation
        Self::MULTIPLIER * (1usize << chunk_i)
    }

    /// Converts a "global" index into the arena to its chunk position
    #[inline(always)]
    fn position_for(&self, index: usize) -> ChunkPos {
        // This code only works for an exponent base of 2 since we use `leading_zeros` to implement
        // a fast integer log2 operation

        //TODO: This can be removed once `usize::BITS` is stabilized
        //  https://github.com/rust-lang/rust/issues/76904
        #[cfg(target_pointer_width = "64")]
        const BITS: u32 = 64;

        // First divide by the multipler because we multiply by it to get the chunk_len
        let divided_index = index / Self::MULTIPLIER;

        // divided_index + 1 ensures that divided_index >= 1
        // The rest of the expression computes log2 of that value
        // See: https://stackoverflow.com/a/11376759/551904
        let chunk_index = BITS - (divided_index + 1).leading_zeros() - 1;

        // The first "global" index in the chunk
        let chunk_first_index = self.chunk_len(chunk_index) - Self::MULTIPLIER;
        // The item index is the offset of this item within the chunk
        let item_index = index - chunk_first_index;

        ChunkPos {chunk_index, item_index}
    }
}

/// A type-erased pointer to an element in the arena
///
/// Ensures that elements can still be accessed performantly while also assigning the correct
/// lifetime to references created from this pointer.
///
/// Needed because converting an index to a chunk index and item index can be expensive. Uses
/// `NonNull` so that `Option<Ptr>` gets the layout optimizations that `Option<NonNull>` gets.
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Ptr(NonNull<()>);

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

    /// The maximum number of entries that can be pushed into the arena without allocating
    capacity: usize,

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
            capacity: 0,
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
        let mut arena = Self::new();

        while arena.capacity() < capacity {
            arena.push_chunk();
        }

        arena
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
        self.capacity
    }

    /// Returns a reference to a value in the arena
    ///
    /// # Safety
    ///
    /// Calling this method with a pointer that is no longer valid is undefined behavior even if the
    /// resulting reference is not used.
    pub unsafe fn get_unchecked(&self, ptr: Ptr) -> &T {
        // Safety: This pointer originated from a `NonNull<T>` so it is safe to cast it back
        //   (Technically it was a `NonNull<MaybeUninit<T>>` but that doesn't make a difference.)
        &*ptr.0.cast().as_ptr()
    }

    /// Returns a mutable reference to a value in the arena
    ///
    /// # Safety
    ///
    /// Calling this method with a pointer that is no longer valid is undefined behavior even if the
    /// resulting reference is not used.
    pub unsafe fn get_unchecked_mut(&mut self, ptr: Ptr) -> &mut T {
        // Safety: This pointer originated from a `NonNull<T>` so it is safe to cast it back
        //   (Technically it was a `NonNull<MaybeUninit<T>>` but that doesn't make a difference.)
        &mut *ptr.0.cast().as_ptr()
    }

    /// Allocates the given value in the arena and returns a stable address to the value
    ///
    /// The returned pointer is guaranteed to be valid as long as no method is called that would
    /// invalidate the pointer (e.g. the `clear` method).
    pub fn alloc(&mut self, value: T) -> Ptr {
        debug_assert!(self.len <= self.capacity);
        // The length can never exceed the capacity
        if self.len == self.capacity {
            // Should only have to push once to get enough capacity for this new value
            self.push_chunk();
        }
        debug_assert!(self.len < self.capacity);

        let index = self.len();

        let ChunkPos {chunk_index, item_index} = self.strategy.position_for(index);
        debug_assert!((chunk_index as usize) < self.chunks.len());
        // Safety: Given that we have definitely reserved enough space for this item above, the
        // chunk index returned for it should be within the array of chunks
        let chunk = unsafe { self.chunks.get_unchecked_mut(chunk_index as usize) };
        // Safety: item index is guaranteed to be a valid index into the chunk
        let mut item_ptr = unsafe { NonNull::new_unchecked(chunk.as_ptr().add(item_index)) };
        unsafe { item_ptr.as_mut().as_mut_ptr().write(value); }

        self.len += 1;

        // Safety: `MaybeUninit<T>` is guaranteed to have the same size, alignment, and ABI as T
        Ptr(unsafe { mem::transmute(item_ptr) })
    }

    /// Returns an iterator over the arena
    pub fn iter(&self) -> Iter<T> {
        Iter::new(self)
    }

    /// Returns an iterator over the arena that allows you to modify each value
    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut::new(self)
    }

    /// Clears the arena, removing all values.
    ///
    /// Note that this method has no effect on the allocated capacity of the arena.
    ///
    /// This invalidates all previous addresses returned from `alloc`.
    pub fn clear(&mut self) {
        // If the items do not need to be dropped or if the collection is empty, we can just reset
        // the length and exit.
        if !mem::needs_drop::<T>() || self.is_empty() {
            self.len = 0;

            return;
        }

        // Go through and drop every chunk
        let mut dropped = 0;
        'droploop:
        for (chunk_i, chunk) in (0..).zip(&mut self.chunks) {
            let chunk_len = self.strategy.chunk_len(chunk_i);
            // Safety: each chunk is initialized from a valid slice of memory of its chunk length
            let chunk = unsafe {
                slice::from_raw_parts_mut(chunk.as_mut(), chunk_len)
            };

            for item in chunk {
                // Stop once we've dropped every element
                if dropped == self.len {
                    // Need to at least break this inner loop, but breaking the outer loop too just
                    // because it doesn't need to run anymore. Usually, we will be at the last chunk
                    // anyway when `dropped == self.len`, but we can still have chunks leftover if
                    // removing elements becomes supported later. No unsafety can happen if further
                    // *chunks* are iterated through. This is just an optimization.
                    break 'droploop;
                }

                //TODO: This can be replaced with `assume_init_drop` once that is stable
                //  See: https://doc.rust-lang.org/std/mem/union.MaybeUninit.html#method.assume_init_drop
                // Safety: All elements at index < self.len are guaranteed to be initalized
                //   The value will never be used after this since we are clearing the arena.
                unsafe { ptr::drop_in_place(item.as_mut_ptr()) };

                dropped += 1;
            }
        }

        debug_assert_eq!(dropped, self.len);

        // All items have been dropped, so reset the length
        self.len = 0;
    }

    /// Reserves capacity for at least `additional` more elements to be inserted in the arena.
    ///
    /// The collection may reserve more space to avoid frequent reallocations. After calling
    /// reserve, capacity will be greater than or equal to `self.len() + additional`. Does nothing
    /// if capacity is already sufficient.
    pub fn reserve(&mut self, additional: usize) {
        let capacity = self.len() + additional;

        while self.capacity() < capacity {
            self.push_chunk();
        }
    }

    /// Shrinks the capacity of the arena as much as possible.
    ///
    /// It will drop down as close as possible to the length but may still be greater.
    pub fn shrink_to_fit(&mut self) {
        let mut chunks_len = self.chunks.len();
        while let Some(chunk) = self.chunks.last_mut() {
            let chunk_i = (chunks_len - 1) as u32;
            let chunk_len = self.strategy.chunk_len(chunk_i);

            // We can only remove chunks that are completely empty
            if self.capacity - chunk_len >= self.len {
                // No need to drop any items in the chunk since it is empty

                // Free the chunk allocation
                // Safety: This process needs to deallocate the exact type the chunk was initially
                // created from in `push_chunk`.
                // Safety: We assert in `push_chunk` that size == capacity
                // Drop the `Vec` right after creating it
                unsafe { Vec::from_raw_parts(chunk.as_mut(), chunk_len, chunk_len); }

                self.chunks.pop();
                chunks_len -= 1;

                self.capacity -= chunk_len;

            } else {
                // We've reached the last non-empty chunk and can no longer remove anything else
                break;
            }
        }

        // Shrink the capacity of the chunks
        self.chunks.shrink_to_fit();
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

    fn push_chunk(&mut self) {
        // The next chunk index is the number of chunks we currently have
        let chunk_i = self.chunks.len() as u32;
        let chunk_len = self.strategy.chunk_len(chunk_i);

        //TODO: Replace this with `Box::new_uninit_slice` when that is stable
        //  See: https://github.com/rust-lang/rust/issues/63291
        // To avoid initializing the memory, we just use `Vec::with_capacity`. This is safe because
        // `MaybeUninit` doesn't need to be initialized.
        let mut chunk: Vec<MaybeUninit<T>> = Vec::with_capacity(chunk_len);
        //TODO: This is used to make removing chunks safe without tracking the capacity explicitly.
        //  It will become unnecessary once we have `Box::new_uninit_slice`. If this assertion ever
        //  fails we will need to change how we drop chunks.
        assert_eq!(chunk.capacity(), chunk_len);

        // Store a pointer to the chunk and then forget it so that it doesn't get dropped
        let chunk_ptr = chunk.as_mut_ptr();
        mem::forget(chunk);

        // Safety: The `Vec` must allocate *some* capacity as long as the chunk length is greater
        //   than 0. As long as there is some capacity, this pointer will be non-null.
        let chunk_ptr = unsafe { NonNull::new_unchecked(chunk_ptr) };

        self.chunks.push(chunk_ptr);
        self.capacity += chunk_len;
    }

    /// Returns the pointer corresponding to the given index
    ///
    /// # Safety
    ///
    /// The index must not be out of bounds
    unsafe fn ptr_at(&self, index: usize) -> Ptr {
        let ChunkPos {chunk_index, item_index} = self.strategy.position_for(index);
        debug_assert!((chunk_index as usize) < self.chunks.len());
        // Safety: Since the index is in bounds, the chunk index returned for it should be within
        // the array of chunks
        let chunk = self.chunks.get_unchecked(chunk_index as usize);
        // Safety: item index is guaranteed to be a valid index into the chunk
        let item_ptr = NonNull::new_unchecked(chunk.as_ptr().add(item_index));

        Ptr(item_ptr.cast())
    }
}

//TODO: This needs a `#[may_dangle]` attribute on `T`
// See: https://forge.rust-lang.org/libs/maintaining-std.html#is-there-a-manual-drop-implementation
impl<T> Drop for StableArena<T> {
    fn drop(&mut self) {
        // Drop all elements that need to be dropped
        self.clear();

        // Free each allocated chunk
        for (chunk_i, chunk) in (0..).zip(&mut self.chunks) {
            let chunk_len = self.strategy.chunk_len(chunk_i);
            // Safety: This process needs to deallocate the exact type the chunk was initially
            // created from in `push_chunk`.
            // Safety: We assert in `push_chunk` that size == capacity
            // Drop the `Vec` right after creating it
            unsafe { Vec::from_raw_parts(chunk.as_mut(), chunk_len, chunk_len); }
        }
    }
}

impl<T> IntoIterator for StableArena<T> {
    type Item = T;

    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        todo!()
    }
}

impl<'a, T> IntoIterator for &'a StableArena<T> {
    type Item = &'a T;

    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut StableArena<T> {
    type Item = &'a mut T;

    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

pub struct IntoIter<T> {
    _marker: PhantomData<T>, //TODO
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn size_hint(&self) -> (usize, Option<usize>) {
        //TODO
        (0, None)
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.next_ptr().map(|(_, item)| item)
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.next_back_ptr().map(|(_, item)| item)
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {}

impl<T> FusedIterator for IntoIter<T> {}

impl<T> ArenaIterator for IntoIter<T> {
    fn next_ptr(&mut self) -> Option<(Ptr, Self::Item)> {
        todo!()
    }
}

impl<T> ArenaDoubleEndedIterator for IntoIter<T> {
    fn next_back_ptr(&mut self) -> Option<(Ptr, Self::Item)> {
        todo!()
    }
}

pub struct Iter<'a, T> {
    arena: &'a StableArena<T>,
    range: Range<usize>,
}

impl<'a, T> Iter<'a, T> {
    fn new(arena: &'a StableArena<T>) -> Self {
        Self {
            arena,
            range: 0..arena.len(),
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.range.size_hint()
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.next_ptr().map(|(_, item)| item)
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.next_back_ptr().map(|(_, item)| item)
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> { }

impl<'a, T> FusedIterator for Iter<'a, T> {}

impl<'a, T> ArenaIterator for Iter<'a, T> {
    fn next_ptr(&mut self) -> Option<(Ptr, Self::Item)> {
        let index = self.range.next()?;

        // Safety: The index is guaranteed to be between 0 and len()
        let ptr = unsafe { self.arena.ptr_at(index) };
        // Safety: The pointer is valid since we just computed it from a valid index
        let item = unsafe { self.arena.get_unchecked(ptr) };

        Some((ptr, item))
    }
}

impl<'a, T> ArenaDoubleEndedIterator for Iter<'a, T> {
    fn next_back_ptr(&mut self) -> Option<(Ptr, Self::Item)> {
        let index = self.range.next_back()?;

        // Safety: The index is guaranteed to be between 0 and len()
        let ptr = unsafe { self.arena.ptr_at(index) };
        // Safety: The pointer is valid since we just computed it from a valid index
        let item = unsafe { self.arena.get_unchecked(ptr) };

        Some((ptr, item))
    }
}

pub struct IterMut<'a, T> {
    arena: &'a mut StableArena<T>,
    range: Range<usize>,
}

impl<'a, T> IterMut<'a, T> {
    fn new(arena: &'a mut StableArena<T>) -> Self {
        Self {
            range: 0..arena.len(),
            arena,
        }
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.range.size_hint()
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.next_ptr().map(|(_, item)| item)
    }
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.next_back_ptr().map(|(_, item)| item)
    }
}

impl<'a, T> ExactSizeIterator for IterMut<'a, T> { }

impl<'a, T> FusedIterator for IterMut<'a, T> {}

impl<'a, T> ArenaIterator for IterMut<'a, T> {
    fn next_ptr(&mut self) -> Option<(Ptr, Self::Item)> {
        let index = self.range.next()?;

        // Safety: The index is guaranteed to be between 0 and len()
        let ptr = unsafe { self.arena.ptr_at(index) };
        // Safety: The pointer is valid since we just computed it from a valid index
        let item = unsafe { &mut *ptr.0.cast().as_ptr() };

        Some((ptr, item))
    }
}

impl<'a, T> ArenaDoubleEndedIterator for IterMut<'a, T> {
    fn next_back_ptr(&mut self) -> Option<(Ptr, Self::Item)> {
        let index = self.range.next_back()?;

        // Safety: The index is guaranteed to be between 0 and len()
        let ptr = unsafe { self.arena.ptr_at(index) };
        // Safety: The pointer is valid since we just computed it from a valid index
        let item = unsafe { &mut *ptr.0.cast().as_ptr() };

        Some((ptr, item))
    }
}

pub trait ArenaIterator: Sized + Iterator {
    /// Returns the next element of this iterator and its corresponding pointer
    fn next_ptr(&mut self) -> Option<(Ptr, Self::Item)>;

    /// Returns an iterator that also yields the corresponding pointer for each element
    fn pointers(self) -> Pointers<Self> {
        Pointers {iter: self}
    }
}

pub trait ArenaDoubleEndedIterator: ArenaIterator {
    /// Returns the next element from the end of this iterator and its corresponding pointer
    fn next_back_ptr(&mut self) -> Option<(Ptr, Self::Item)>;
}

pub struct Pointers<I: ArenaIterator> {
    iter: I,
}

impl<I: ArenaIterator> Iterator for Pointers<I> {
    type Item = (Ptr, I::Item);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next_ptr()
    }
}

impl<I: ArenaDoubleEndedIterator> DoubleEndedIterator for Pointers<I> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back_ptr()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::rc::Rc;

    #[test]
    fn exponential_strategy_indexes() {
        /// The number of chunks to test
        const CHUNKS: u32 = 5;

        let strategy = ExponentialAlloc::default();

        // The ranges of "global" indexes into the arena that each chunk should contain
        let mut ranges = Vec::with_capacity(CHUNKS as usize);
        let mut end = 0;
        for chunk_i in 0..CHUNKS+1 {
            // start at the end of the last range
            let start = end;
            // add the size of the current range to the end
            end += strategy.chunk_len(chunk_i);
            ranges.push((chunk_i, start..end));
        }

        for (expected_chunk_i, index_range) in ranges {
            for (item_index, index) in index_range.enumerate() {
                let pos = strategy.position_for(index);
                assert_eq!(pos.chunk_index, expected_chunk_i);
                assert_eq!(pos.item_index, item_index);
            }
        }
    }

    #[test]
    fn drop_empty_arena() {
        // Using Vec because it implements Drop
        let _empty: StableArena<Vec<i32>> = StableArena::default();

        let _empty2: StableArena<Vec<i32>> = StableArena::with_capacity(1000);
    }

    #[test]
    fn arena_push() {
        // Addresses yielded by the arena should remain valid regardless of how many times we push

        // This test is O(n^2), so be careful with this number
        #[cfg(not(miri))]
        const ALLOCS: usize = 1024;
        #[cfg(miri)]
        const ALLOCS: usize = 32;

        let mut ptrs = Vec::with_capacity(ALLOCS);

        // The arena allocator will resize multiple times during this test
        let mut arena = StableArena::new();
        for i in 0..ALLOCS {
            // Pushing a type that implements drop
            ptrs.push(arena.alloc(Rc::new(i)));

            // Check that all addresses are still valid
            for (j, ptr) in ptrs.iter().enumerate() {
                assert_eq!(unsafe { **arena.get_unchecked(*ptr) }, j);
            }
        }
    }

    #[test]
    fn arena_capacity() {
        // Capacity must start at zero (do not allocate until needed)
        let arena: StableArena<i32> = StableArena::new();
        assert_eq!(arena.capacity(), 0);

        let mut arena: StableArena<String> = StableArena::with_capacity(10);
        assert!(arena.capacity() >= 10);
        let capacity = arena.capacity();

        // reserve zero slots
        arena.reserve(0);
        // capacity should not change
        assert_eq!(arena.capacity(), capacity);

        // reserve space for at least 10 slots
        arena.reserve(10);
        assert!(arena.capacity() >= arena.len() + 10);
        let capacity = arena.capacity();

        // push should not change capacity if capacity is greater than length
        assert!(arena.capacity() > arena.len());

        let mut ptrs = Vec::new();
        for i in 0.. {
            ptrs.push(arena.alloc(i.to_string()));

            if arena.capacity() <= arena.len() {
                break;
            }
        }

        // capacity should still be the same
        assert_eq!(arena.capacity(), capacity);

        // shrink to fit should not affect items
        arena.shrink_to_fit();
        let capacity = arena.capacity();
        for (i, ptr) in ptrs.iter().copied().enumerate() {
            assert_eq!(unsafe { arena.get_unchecked(ptr) }, &i.to_string());
            assert_eq!(arena.capacity(), capacity);
        }

        // reserving a bunch of space and then shrinking it down again should reclaim that space
        arena.reserve(arena.len() * 3);
        assert_ne!(arena.capacity(), capacity);
        arena.shrink_to_fit();
        assert_eq!(arena.capacity(), capacity);

        //TODO: Add back once we have `pop()`
        // pop should not change capacity
        // for _ in ptrs {
        //     arena.pop();
        //     assert_eq!(slab.capacity(), capacity);
        // }

        //TODO: Add back once we have `pop()`
        // shrink_to_fit should bring capacity back down as close to zero as possible
        // assert!(arena.is_empty());
        // arena.shrink_to_fit();
        // assert!(arena.capacity() >= arena.len());
    }
}

//
// Copyright (c) 2025 Nathan Fiedler
//

//! An implementation of resizable arrays as described in the paper **Resizable
//! Arrays in Optimal Time and Space** by Andrej Brodnik et. al., published in
//! 1999.
//!
//! * Online ISBN 978-3-540-48447-9
//! * https://doi.org/10.1137/23M1575792
//!
//! # Memory Usage
//!
//! An empty resizable array is approximately 88 bytes in size, and while
//! holding elements it will have an overhead space cost on the order of O(√N).
//!
//! # Performance
//!
//! Most operations are either constant time, or log2 or sqrt of the collection
//! size. However, the lookup operation involves numerous calculations and as
//! such the overall performance will be worse than `Vec`. The difference will
//! be in substantially reduced memory overhead.
//!
//! # Safety
//!
//! Because this data structure is allocating memory, copying bytes using
//! pointers, and de-allocating memory as needed, there are many `unsafe` blocks
//! throughout the code.

#![allow(dead_code)]
use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};
use std::fmt;
use std::ops::{Index, IndexMut};

/// USIZE_BITS is the number of bits in a usize, which is used to determine a
/// value for `k` for a given zero-based index `i` into the array.
const USIZE_BITS: u32 = (8 * std::mem::size_of::<usize>()) as u32;

/// Maps the highest numbered data block to a given capacity. Computing this
/// would be a challenge given how many steps are involved to go from k to p, b,
/// and e in the locate function.
const BLOCK_SIZES: [(usize, usize); 17] = [
    (1, 1),
    (4, 2),
    (10, 4),
    (22, 8),
    (46, 16),
    (94, 32),
    (190, 64),
    (382, 128),
    (766, 256),
    (1534, 512),
    (3070, 1024),
    (6142, 2048),
    (12286, 4096),
    (24574, 8192),
    (49150, 16384),
    (98302, 32768),
    (131070, 65536),
];

/// Determine the capacity for the data block at index d.
fn datablock_capacity_for_block(d: usize) -> usize {
    for (max, len) in BLOCK_SIZES {
        if d < max {
            return len;
        }
    }
    panic!("overflow, block out of bounds")
}

/// Compute the data block and element offsets (0-based) within the array for
/// the element identified by the zero-based index `i`.
fn locate(i: usize) -> (usize, usize) {
    // Locate, from Algorithm 3 of the Broknik 1999 paper
    //
    // adding one presumably makes the math and logic easier
    let r = i + 1;
    // k is the superblock that contains the data block
    let k = (USIZE_BITS - r.leading_zeros()) - 1;
    // skc is the element capacity of superblock k and also happens to be useful
    // for masking the leading 1-bit in the value for r
    let skc = 1 << k;
    let k2 = k.div_ceil(2);
    let k2s = (1 << k2) - 1;
    // b is the relative offset of the data block within superblock k
    let b = (r ^ skc) >> k2;
    // e is the relative offset of the element within data block b
    let e = r & k2s;
    //
    // The Broknik 1999 paper suggests p = 2^k - 1 (see Algorithm 3, step 3) but
    // that is actually the number of elements prior to superblock k. Instead,
    // we need to sum two geometric series to get the result.
    //
    // The number of data blocks in each superblock form a series like so:
    //
    // 1, 1, 2, 2, 4, 4, 8, 8, 16, 16, 32, 32, ...
    //
    // To compute the sum of these for a given superblock, k, we must find the
    // sum of each half of the repeating terms in the series, one for the
    // odd-numbered and another for the even-numbered, then add the results to
    // get the total. Using k / 2 will round down while k.div_ceil(2) will round
    // up, giving us effectively floor(k/2) and ceil(k/2) without the need for
    // floating point conversion.
    //
    let p = (1 << (k / 2)) - 1 + k2s;
    (p + b, e)
}

/// Compute the number of elements that data blocks in superblock k can hold.
#[inline]
fn datablock_capacity(k: usize) -> usize {
    1 << k.div_ceil(2)
}

/// Compute the number of data blocks that superblock k can hold.
#[inline]
fn superblock_capacity(k: usize) -> usize {
    // the k + 1 makes the math simpler; this works because the capacity of the
    // even-numbered superblocks equals the that of the odd-numbered blocks
    1 << ((k + 1).div_ceil(2) - 1)
}

/// Compute the number of data blocks that appear before superblock k.
#[inline]
fn blocks_before_super(k: usize) -> usize {
    (1 << (k / 2)) + (1 << k.div_ceil(2)) - 2
}

/// Compute the capacity for an array with `s` superblocks and `d` data blocks.
fn array_capacity(s: usize, d: usize) -> usize {
    if s == 0 {
        // array is completely empty, math fails here
        0
    } else {
        let k = s - 1;
        // compute the number of data blocks before superblock k
        let leading_blocks = blocks_before_super(k);
        // compute the element capacity prior to superblock k
        let leading_capacity = (1 << k) - 1;
        let block_capacity = datablock_capacity(k);
        // compute capacity of allocated blocks in this superblock
        (d - leading_blocks) * block_capacity + leading_capacity
    }
}

/// Resizable array in optimal space and time (in theory).
pub struct OptimalArray<T> {
    // holds pointers to data blocks
    index: Vec<*mut T>,
    /// number of elements in the array
    n: usize,
    /// number of superblocks in the array
    s: usize,
    /// number of non-empty data blocks
    d: usize,
    /// number of empty data blocks (either 0 or 1)
    empty: usize,
    /// number of elements in last non-empty data block
    last_db_length: usize,
    /// capacity of the last non-empty data block
    last_db_capacity: usize,
    /// number of data blocks in last non-empty super block
    last_sb_length: usize,
    /// capacity of data blocks the last non-empty super block
    last_sb_capacity: usize,
}

impl<T> OptimalArray<T> {
    /// Return an empty array with zero capacity.
    ///
    /// Note that pre-allocating capacity has no benefit with this data
    /// structure since append operations are always constant time and no
    /// copying is ever performed.
    pub fn new() -> Self {
        Self {
            index: vec![],
            n: 0,
            s: 0,
            d: 0,
            empty: 0,
            last_db_length: 0,
            last_db_capacity: 0,
            last_sb_length: 0,
            last_sb_capacity: 0,
        }
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Panics
    ///
    /// Panics if a new segment is allocated that would exceed `isize::MAX` _bytes_.
    ///
    /// # Time complexity
    ///
    /// Constant time.
    pub fn push(&mut self, value: T) {
        // Grow, from Algorithm 1 of Broknik 1999 paper
        //
        // 1. If the last non-empty data block is full:
        if self.last_db_capacity == self.last_db_length {
            // (a) If the last superblock is full:
            if self.last_sb_capacity == self.last_sb_length {
                // i. Increment s
                self.s += 1;
                // ii. and iii. in the paper seem to assume that the capacity
                // values are not set to zero initially, but that seems
                // inconsistent with the rest of the logic in this algorithm.
                // Instead, we calculate the capacity for both every time.
                self.last_sb_capacity = superblock_capacity(self.s - 1);
                self.last_db_capacity = datablock_capacity(self.s - 1);
                // iv. Set occupancy of last superblock to empty
                self.last_sb_length = 0;
            }
            // (b) If there are no empty data blocks:
            if self.empty == 0 {
                // i. If index block is full, double its size
                // ii. Allocate a new data block, add to index block
                //
                // overflowing the allocator is very unlikely as the item size would
                // have to be very large (the longest block will be 65,536 items)
                let layout =
                    Layout::array::<T>(self.last_db_capacity).expect("unexpected overflow");
                unsafe {
                    let ptr = alloc(layout).cast::<T>();
                    if ptr.is_null() {
                        handle_alloc_error(layout);
                    }
                    self.index.push(ptr);
                }
            } else {
                // reuse the previously allocated empty data block
                self.empty = 0;
            }
            // (c) Increment d and the number of data blocks in last superblock
            self.d += 1;
            self.last_sb_length += 1;
            // (d) Set occupancy of new data block to empty
            self.last_db_length = 0;
        }
        // (store the value at the end of the last data block)
        let (block, slot) = locate(self.n);
        unsafe {
            std::ptr::write(self.index[block].add(slot), value);
        }
        // 2. Increment n and the number of elements occupying last data block
        self.n += 1;
        self.last_db_length += 1;
    }

    /// Appends an element if there is sufficient spare capacity, otherwise an
    /// error is returned with the element.
    ///
    /// # Time complexity
    ///
    /// Constant time.
    pub fn push_within_capacity(&mut self, value: T) -> Result<(), T> {
        if array_capacity(self.s, self.d) <= self.n {
            Err(value)
        } else {
            self.push(value);
            Ok(())
        }
    }

    /// Removes the last element from an array and returns it, or `None` if it
    /// is empty.
    ///
    /// # Time complexity
    ///
    /// Constant time.
    pub fn pop(&mut self) -> Option<T> {
        if self.n > 0 {
            self.shrink();
            let (block, slot) = locate(self.n);
            unsafe { Some((self.index[block].add(slot)).read()) }
        } else {
            None
        }
    }

    /// Removes and returns the last element from a vector if the predicate
    /// returns true, or None if the predicate returns false or the vector is
    /// empty (the predicate will not be called in that case).
    ///
    /// # Time complexity
    ///
    /// Constant time.
    pub fn pop_if(&mut self, predicate: impl FnOnce(&mut T) -> bool) -> Option<T> {
        if self.n == 0 {
            None
        } else if let Some(last) = self.get_mut(self.n - 1) {
            if predicate(last) { self.pop() } else { None }
        } else {
            None
        }
    }

    /// Return the number of elements in the array.
    ///
    /// # Time complexity
    ///
    /// Constant time.
    pub fn len(&self) -> usize {
        self.n
    }

    /// Returns the total number of elements the extensible array can hold
    /// without reallocating.
    ///
    /// # Time complexity
    ///
    /// Constant time.
    pub fn capacity(&self) -> usize {
        array_capacity(self.s, self.d)
    }

    /// Returns true if the array has a length of 0.
    ///
    /// # Time complexity
    ///
    /// Constant time.
    pub fn is_empty(&self) -> bool {
        self.n == 0
    }

    /// Retrieve a reference to the element at the given offset.
    ///
    /// # Time complexity
    ///
    /// Constant time.
    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.n {
            None
        } else {
            let (block, slot) = locate(index);
            unsafe { (self.index[block].add(slot)).as_ref() }
        }
    }

    /// Returns a mutable reference to an element.
    ///
    /// # Time complexity
    ///
    /// Constant time.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index >= self.n {
            None
        } else {
            let (block, slot) = locate(index);
            unsafe { (self.index[block].add(slot)).as_mut() }
        }
    }

    /// Removes an element from the vector and returns it.
    ///
    /// The removed element is replaced by the last element of the vector.
    ///
    /// This does not preserve ordering of the remaining elements.
    ///
    /// # Time complexity
    ///
    /// Constant time.
    pub fn swap_remove(&mut self, index: usize) -> T {
        if index >= self.n {
            panic!(
                "swap_remove index (is {index}) should be < len (is {})",
                self.n
            );
        }
        // retreive the value at index before overwriting
        let (block, slot) = locate(index);
        unsafe {
            let index_ptr = self.index[block].add(slot);
            let value = index_ptr.read();
            // find the pointer of the last element and copy to index pointer
            let (block, slot) = locate(self.n - 1);
            let last_ptr = self.index[block].add(slot);
            std::ptr::copy(last_ptr, index_ptr, 1);
            self.shrink();
            value
        }
    }

    /// Returns an iterator over the array.
    ///
    /// The iterator yields all items from start to end.
    pub fn iter(&self) -> OptArrayIter<'_, T> {
        OptArrayIter {
            array: self,
            index: 0,
        }
    }

    /// Clears the extensible array, removing and dropping all values and
    /// deallocating all previously allocated segments.
    ///
    /// # Time complexity
    ///
    /// O(n) if elements are droppable, otherwise O(sqrt(n))
    pub fn clear(&mut self) {
        use std::ptr::{drop_in_place, slice_from_raw_parts_mut};

        if self.n > 0 {
            if std::mem::needs_drop::<T>() {
                // find the last block that contains values and drop them
                let (last_block, last_slot) = locate(self.n - 1);
                unsafe {
                    // last_slot is pointing at the last element, need to add
                    // one to include it in the slice
                    drop_in_place(slice_from_raw_parts_mut(
                        self.index[last_block],
                        last_slot + 1,
                    ));
                }

                // drop the values in all of the preceding data blocks
                let mut block = 0;
                for k in 0..self.s {
                    let level_limit = blocks_before_super(k + 1);
                    let block_len = datablock_capacity(k);
                    while block < level_limit && block < last_block {
                        unsafe {
                            drop_in_place(slice_from_raw_parts_mut(self.index[block], block_len));
                        }
                        block += 1;
                    }
                }
            }

            self.n = 0;
            self.s = 0;
            self.d = 0;
            self.empty = 0;
            self.last_db_length = 0;
            self.last_db_capacity = 0;
            self.last_sb_length = 0;
            self.last_sb_capacity = 0;
        }

        // deallocate all data blocks using the index as the source of truth
        let mut blocks_dealloced = 0;
        for (block, ptr) in self.index.iter().enumerate() {
            let block_len = datablock_capacity_for_block(block);
            let layout = Layout::array::<T>(block_len).expect("unexpected overflow");
            unsafe {
                dealloc(*ptr as *mut u8, layout);
            }
            blocks_dealloced += 1;
        }
        assert_eq!(
            blocks_dealloced,
            self.index.len(),
            "block deallocation failure"
        );
        self.index.clear();
    }

    /// Decrease the number of elements by one and adjust everything to reflect
    /// the reduced length of the array, possibly deallocating data blocks and
    /// shrinking the index.
    fn shrink(&mut self) {
        // Shrink, from Algorithm 2 of Broknik 1999 paper
        //
        // 1. Decrement n and num elements in last non-empty data block
        self.n -= 1;
        self.last_db_length -= 1;
        // 2. If last data block is empty
        if self.last_db_length == 0 {
            // (a) If there is another empty data block, Deallocate it
            if self.empty == 1 {
                let ptr = self.index.pop().expect("programmer error");
                let block = self.index.len();
                let block_len = datablock_capacity_for_block(block);
                let layout = Layout::array::<T>(block_len).expect("unexpected overflow");
                unsafe {
                    dealloc(ptr as *mut u8, layout);
                }
            }
            // leave this last empty data block in case more pushes occur
            // and we would soon be allocating the same sized block again
            self.empty = 1;
            // (b) If the index block is quarter full, shrink to half
            if self.index.len() * 4 <= self.index.capacity() {
                self.index.shrink_to(self.index.capacity() / 2);
            }
            // (c) Decrement d and num data blocks in last superblock
            self.d -= 1;
            self.last_sb_length -= 1;
            // (d) If last superblock is empty
            if self.last_sb_length == 0 {
                // i. Decrement s
                self.s -= 1;
                // ii. If s is even, halve num data blocks in superblock
                // iii. Else, halve num elements in data block
                if self.s == 0 {
                    self.last_sb_capacity = 0;
                    self.last_db_capacity = 0;
                } else {
                    self.last_sb_capacity = superblock_capacity(self.s - 1);
                    self.last_db_capacity = datablock_capacity(self.s - 1);
                }
                // iv. Set occupancy of last superblock to full
                self.last_sb_length = self.last_sb_capacity;
            }
            // (e) Set occupancy of last data block to full
            self.last_db_length = self.last_db_capacity;
        }
    }
}

impl<T> Default for OptimalArray<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> fmt::Display for OptimalArray<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "OptimalArray(n: {}, s: {}, d: {}, e: {}, dl: {}, dc: {}, sl: {}, sc: {})",
            self.n,
            self.s,
            self.d,
            self.empty,
            self.last_db_length,
            self.last_db_capacity,
            self.last_sb_length,
            self.last_sb_capacity
        )
    }
}

impl<T> Drop for OptimalArray<T> {
    fn drop(&mut self) {
        self.clear();
    }
}

impl<T> Index<usize> for OptimalArray<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        let Some(item) = self.get(index) else {
            panic!("index out of bounds: {}", index);
        };
        item
    }
}

impl<T> IndexMut<usize> for OptimalArray<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        let Some(item) = self.get_mut(index) else {
            panic!("index out of bounds: {}", index);
        };
        item
    }
}

impl<A> FromIterator<A> for OptimalArray<A> {
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self {
        let mut arr: OptimalArray<A> = OptimalArray::new();
        for value in iter {
            arr.push(value)
        }
        arr
    }
}

/// Immutable array iterator.
pub struct OptArrayIter<'a, T> {
    array: &'a OptimalArray<T>,
    index: usize,
}

impl<'a, T> Iterator for OptArrayIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let value = self.array.get(self.index);
        self.index += 1;
        value
    }
}

impl<T> IntoIterator for OptimalArray<T> {
    type Item = T;
    type IntoIter = OptArrayIntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        let mut me = std::mem::ManuallyDrop::new(self);
        let index = std::mem::take(&mut me.index);
        OptArrayIntoIter {
            cursor: 0,
            n: me.n,
            index,
        }
    }
}

/// An iterator that moves out of an optimal array.
pub struct OptArrayIntoIter<T> {
    /// offset into the array
    cursor: usize,
    /// count of elements in array
    n: usize,
    /// data block index
    index: Vec<*mut T>,
}

impl<T> Iterator for OptArrayIntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cursor < self.n {
            let (block, slot) = locate(self.cursor);
            self.cursor += 1;
            unsafe { Some((self.index[block].add(slot)).read()) }
        } else {
            None
        }
    }
}

impl<T> Drop for OptArrayIntoIter<T> {
    fn drop(&mut self) {
        use std::ptr::{drop_in_place, slice_from_raw_parts_mut};

        if std::mem::needs_drop::<T>() {
            let (first_block, first_slot) = locate(self.cursor);
            let (last_block, last_slot) = locate(self.n - 1);
            if first_block == last_block {
                // special-case, remaining values are in only one segment
                if first_slot <= last_slot {
                    unsafe {
                        // last_slot is pointing at the last element, need to
                        // add one to include it in the slice
                        drop_in_place(slice_from_raw_parts_mut(
                            self.index[first_block].add(first_slot),
                            last_slot - first_slot + 1,
                        ));
                    }
                }
            } else {
                // drop the remaining values in the first block
                let block_len = datablock_capacity_for_block(first_block);
                if block_len < self.n {
                    unsafe {
                        drop_in_place(slice_from_raw_parts_mut(
                            self.index[first_block].add(first_slot),
                            block_len - first_slot,
                        ));
                    }
                }

                // drop the values in the last block
                unsafe {
                    drop_in_place(slice_from_raw_parts_mut(
                        self.index[last_block],
                        last_slot + 1,
                    ));
                }

                // drop the values in all of the other blocks
                for block in first_block + 1..last_block {
                    let block_len = datablock_capacity_for_block(block);
                    unsafe {
                        drop_in_place(slice_from_raw_parts_mut(self.index[block], block_len));
                    }
                }
            }
        }

        // deallocate all of the data blocks
        for block in 0..self.index.len() {
            let block_len = datablock_capacity_for_block(block);
            let layout = Layout::array::<T>(block_len).expect("unexpected overflow");
            unsafe {
                dealloc(self.index[block] as *mut u8, layout);
            }
        }

        self.index.clear();
        self.cursor = 0;
        self.n = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_expansion_and_access() {
        let mut sut: OptimalArray<u64> = OptimalArray::new();
        assert_eq!(sut.len(), 0);
        assert!(sut.is_empty());
        for value in 0..63 {
            sut.push(value);
        }
        assert_eq!(sut.len(), 63);
        assert!(!sut.is_empty());
        assert_eq!(sut.get(0), Some(&0));
        assert_eq!(sut.get(1), Some(&1));
        assert_eq!(sut.get(3), Some(&3));
        assert_eq!(sut.get(7), Some(&7));
        assert_eq!(sut.get(15), Some(&15));
        assert_eq!(sut.get(30), Some(&30));
        assert_eq!(sut.get(62), Some(&62));
        let missing = sut.get(101);
        assert!(missing.is_none());
    }

    #[test]
    fn test_push_get_several_strings() {
        let inputs = [
            "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
        ];
        let mut sut: OptimalArray<String> = OptimalArray::new();
        for item in inputs {
            sut.push(item.to_owned());
        }
        assert_eq!(sut.len(), 9);
        for (idx, item) in inputs.iter().enumerate() {
            let maybe = sut.get(idx);
            assert!(maybe.is_some(), "{idx} is none");
            let actual = maybe.unwrap();
            assert_eq!(item, actual);
        }
        let maybe = sut.get(10);
        assert!(maybe.is_none());
        assert_eq!(sut[3], "four");
    }

    #[test]
    fn test_push_get_hundred_ints() {
        let mut sut: OptimalArray<i32> = OptimalArray::new();
        for value in 0..100 {
            sut.push(value);
        }
        assert_eq!(sut.len(), 100);
        for idx in 0..100 {
            let maybe = sut.get(idx);
            assert!(maybe.is_some(), "{idx} is none");
            let actual = maybe.unwrap();
            assert_eq!(idx, *actual as usize);
        }
        assert_eq!(sut[99], 99);
    }

    #[test]
    fn test_len_and_capacity() {
        let mut sut: OptimalArray<u64> = OptimalArray::new();
        assert_eq!(sut.len(), 0);
        assert_eq!(sut.capacity(), 0);
        for value in 0..12 {
            sut.push(value);
        }
        assert_eq!(sut.len(), 12);
        // 1 + 2 + 4 + 8
        assert_eq!(sut.capacity(), 15);
    }

    #[test]
    fn test_push_within_capacity() {
        // empty array has no allocated space
        let mut sut: OptimalArray<u32> = OptimalArray::new();
        assert_eq!(sut.push_within_capacity(101), Err(101));
        sut.push(1);
        sut.push(2);
        assert_eq!(sut.push_within_capacity(3), Ok(()));

        // edge case (second data block is 2 elements long)
        let mut sut: OptimalArray<u32> = OptimalArray::new();
        sut.push(1);
        sut.push(2);
        assert_eq!(sut.push_within_capacity(3), Ok(()));
        assert_eq!(sut.push_within_capacity(101), Err(101));
    }

    #[test]
    fn test_get_mut_index_mut() {
        let mut sut: OptimalArray<String> = OptimalArray::new();
        sut.push(String::from("first"));
        sut.push(String::from("second"));
        sut.push(String::from("third"));
        if let Some(value) = sut.get_mut(1) {
            value.push_str(" place");
        } else {
            panic!("get_mut() returned None")
        }
        assert_eq!(sut[1], "second place");
        sut[2] = "third planet".into();
        assert_eq!(sut[2], "third planet");
    }

    #[test]
    #[should_panic(expected = "index out of bounds:")]
    fn test_index_out_of_bounds() {
        let mut sut: OptimalArray<i32> = OptimalArray::new();
        sut.push(10);
        sut.push(20);
        let _ = sut[2];
    }

    #[test]
    #[should_panic(expected = "index out of bounds:")]
    fn test_index_mut_out_of_bounds() {
        let mut sut: OptimalArray<i32> = OptimalArray::new();
        sut.push(10);
        sut.push(20);
        sut[2] = 30;
    }

    #[test]
    fn test_clear_and_reuse_tiny() {
        // clear an array that allocated only one segment
        let mut sut: OptimalArray<String> = OptimalArray::new();
        sut.push(String::from("one"));
        assert_eq!(sut.len(), 1);
        sut.clear();
        assert_eq!(sut.len(), 0);
        sut.push(String::from("two"));
        assert_eq!(sut.len(), 1);
        // implicitly drop()
    }

    #[test]
    fn test_clear_and_reuse_ints() {
        let mut sut: OptimalArray<i32> = OptimalArray::new();
        for value in 0..512 {
            sut.push(value);
        }
        assert_eq!(sut.len(), 512);
        sut.clear();
        assert_eq!(sut.len(), 0);
        for value in 0..512 {
            sut.push(value);
        }
        for idx in 0..512 {
            let maybe = sut.get(idx);
            assert!(maybe.is_some(), "{idx} is none");
            let actual = maybe.unwrap();
            assert_eq!(idx, *actual as usize);
        }
    }

    #[test]
    fn test_clear_and_reuse_strings() {
        let mut sut: OptimalArray<String> = OptimalArray::new();
        for _ in 0..512 {
            let value = ulid::Ulid::new().to_string();
            sut.push(value);
        }
        assert_eq!(sut.len(), 512);
        sut.clear();
        assert_eq!(sut.len(), 0);
        for _ in 0..512 {
            let value = ulid::Ulid::new().to_string();
            sut.push(value);
        }
        assert_eq!(sut.len(), 512);
        // implicitly drop()
    }

    #[test]
    fn test_push_get_thousands_structs() {
        struct MyData {
            a: u64,
            b: i32,
        }
        let mut sut: OptimalArray<MyData> = OptimalArray::new();
        for value in 0..88_888i32 {
            sut.push(MyData {
                a: value as u64,
                b: value,
            });
        }
        assert_eq!(sut.len(), 88_888);
        for idx in 0..88_888i32 {
            let maybe = sut.get(idx as usize);
            assert!(maybe.is_some(), "{idx} is none");
            let actual = maybe.unwrap();
            assert_eq!(idx as u64, actual.a);
            assert_eq!(idx, actual.b);
        }
    }

    #[test]
    fn test_push_get_many_instances_ints() {
        // test allocating, filling, and then dropping many instances
        for _ in 0..1_000 {
            let mut sut: OptimalArray<usize> = OptimalArray::new();
            for value in 0..10_000 {
                sut.push(value);
            }
            assert_eq!(sut.len(), 10_000);
        }
    }

    #[test]
    fn test_push_get_many_instances_strings() {
        // test allocating, filling, and then dropping many instances
        for _ in 0..1_000 {
            let mut sut: OptimalArray<String> = OptimalArray::new();
            for _ in 0..1_000 {
                let value = ulid::Ulid::new().to_string();
                sut.push(value);
            }
            assert_eq!(sut.len(), 1_000);
        }
    }

    #[test]
    fn test_array_iterator() {
        let inputs = [
            "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
        ];
        let mut sut: OptimalArray<String> = OptimalArray::new();
        for item in inputs {
            sut.push(item.to_owned());
        }
        for (idx, elem) in sut.iter().enumerate() {
            assert_eq!(inputs[idx], elem);
        }
    }

    #[test]
    fn test_push_pop_grow_shrink_empty_block() {
        // test the handling of the extra empty data block when pushing and
        // popping values that cross over a superblock boundary and thereby the
        // extra empty data block is a different size than the newly emptied
        // data block (push enough to reach superblock 6, then pop enough to get
        // to superblock 5, then push again)
        let mut sut: OptimalArray<usize> = OptimalArray::new();
        for value in 0..35 {
            sut.push(value);
        }
        assert_eq!(sut.len(), 35);
        for _ in 0..5 {
            sut.pop();
        }
        assert_eq!(sut.len(), 30);
        for _ in 0..5 {
            sut.pop();
        }
        assert_eq!(sut.len(), 25);
        for value in 25..37 {
            sut.push(value);
        }
        assert_eq!(sut.len(), 37);
        for (idx, elem) in sut.iter().enumerate() {
            assert_eq!(idx, *elem);
        }

        // try to trigger any clear/drop logic
        sut.clear();
    }

    #[test]
    fn test_push_pop_iter() {
        let inputs = [
            "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
        ];
        let mut sut: OptimalArray<String> = OptimalArray::new();
        assert!(sut.pop().is_none());
        assert_eq!(sut.len(), 0);
        assert_eq!(sut.capacity(), 0);
        for item in inputs {
            sut.push(item.to_owned());
        }
        assert_eq!(sut.len(), 9);
        assert_eq!(sut.capacity(), 11);
        for (idx, elem) in sut.iter().enumerate() {
            assert_eq!(inputs[idx], elem);
        }
        let maybe = sut.pop();
        assert!(maybe.is_some());
        let value = maybe.unwrap();
        assert_eq!(value, "nine");
        assert_eq!(sut.len(), 8);
        assert_eq!(sut.capacity(), 11);
        sut.push(String::from("nine"));
        assert_eq!(sut.len(), 9);
        assert_eq!(sut.capacity(), 11);
        for (idx, elem) in sut.iter().enumerate() {
            assert_eq!(inputs[idx], elem);
        }

        // pop everything and add back again
        while !sut.is_empty() {
            sut.pop();
        }
        assert_eq!(sut.len(), 0);
        assert_eq!(sut.capacity(), 0);
        for item in inputs {
            sut.push(item.to_owned());
        }
        assert_eq!(sut.len(), 9);
        assert_eq!(sut.capacity(), 11);
        for (idx, elem) in sut.iter().enumerate() {
            assert_eq!(inputs[idx], elem);
        }
    }

    #[test]
    fn test_pop_if() {
        let mut sut: OptimalArray<u32> = OptimalArray::new();
        assert!(sut.pop_if(|_| panic!("should not be called")).is_none());
        for value in 0..10 {
            sut.push(value);
        }
        assert!(sut.pop_if(|_| false).is_none());
        let maybe = sut.pop_if(|v| *v == 9);
        assert_eq!(maybe.unwrap(), 9);
        assert!(sut.pop_if(|v| *v == 9).is_none());
    }

    #[test]
    fn test_array_fromiterator() {
        let mut inputs: Vec<i32> = Vec::new();
        for value in 0..10_000 {
            inputs.push(value);
        }
        let sut: OptimalArray<i32> = inputs.into_iter().collect();
        assert_eq!(sut.len(), 10_000);
        for idx in 0..10_000i32 {
            let maybe = sut.get(idx as usize);
            assert!(maybe.is_some(), "{idx} is none");
            let actual = maybe.unwrap();
            assert_eq!(idx, *actual);
        }
    }

    #[test]
    fn test_push_get_many_ints() {
        let mut sut: OptimalArray<i32> = OptimalArray::new();
        for value in 0..1_000_000 {
            sut.push(value);
        }
        assert_eq!(sut.len(), 1_000_000);
        for idx in 0..1_000_000 {
            let maybe = sut.get(idx);
            assert!(maybe.is_some(), "{idx} is none");
            let actual = maybe.unwrap();
            assert_eq!(idx, *actual as usize);
        }
        assert_eq!(sut[99_999], 99_999);
    }

    #[test]
    fn test_array_intoiterator() {
        // an array that only requires a single segment
        let inputs = [
            "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
        ];
        let mut sut: OptimalArray<String> = OptimalArray::new();
        for item in inputs {
            sut.push(item.to_owned());
        }
        for (idx, elem) in sut.into_iter().enumerate() {
            assert_eq!(inputs[idx], elem);
        }
        // sut.len(); // error: ownership of sut was moved
    }

    #[test]
    fn test_array_intoiterator_drop_tiny() {
        // an array that only requires a single segment and only some need to be
        // dropped after partially iterating the values
        let inputs = [
            "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
        ];
        let mut sut: OptimalArray<String> = OptimalArray::new();
        for item in inputs {
            sut.push(item.to_owned());
        }
        for (idx, _) in sut.into_iter().enumerate() {
            if idx > 2 {
                break;
            }
        }
        // implicitly drop()
    }

    #[test]
    fn test_array_intoiterator_drop_large() {
        // by adding 512 values and iterating less than 64 times, there will be
        // values in the first segment and some in the last segment, and two
        // segments inbetween that all need to be dropped
        let mut sut: OptimalArray<String> = OptimalArray::new();
        for _ in 0..512 {
            let value = ulid::Ulid::new().to_string();
            sut.push(value);
        }
        for (idx, _) in sut.into_iter().enumerate() {
            if idx >= 30 {
                break;
            }
        }
        // implicitly drop()
    }

    #[test]
    fn test_swap_remove_single_segment() {
        let mut sut: OptimalArray<u32> = OptimalArray::new();
        sut.push(1);
        assert_eq!(sut.len(), 1);
        let one = sut.swap_remove(0);
        assert_eq!(one, 1);
        assert_eq!(sut.len(), 0);
    }

    #[test]
    fn test_swap_remove_multiple_segments() {
        let mut sut: OptimalArray<u32> = OptimalArray::new();
        for value in 0..512 {
            sut.push(value);
        }
        assert_eq!(sut.len(), 512);
        let eighty = sut.swap_remove(80);
        assert_eq!(eighty, 80);
        assert_eq!(sut.pop(), Some(510));
        assert_eq!(sut[80], 511);
    }

    #[test]
    #[should_panic(expected = "swap_remove index (is 0) should be < len (is 0)")]
    fn test_swap_remove_panic_empty() {
        let mut sut: OptimalArray<u32> = OptimalArray::new();
        sut.swap_remove(0);
    }

    #[test]
    #[should_panic(expected = "swap_remove index (is 1) should be < len (is 1)")]
    fn test_swap_remove_panic_range_edge() {
        let mut sut: OptimalArray<u32> = OptimalArray::new();
        sut.push(1);
        sut.swap_remove(1);
    }

    #[test]
    #[should_panic(expected = "swap_remove index (is 2) should be < len (is 1)")]
    fn test_swap_remove_panic_range_exceed() {
        let mut sut: OptimalArray<u32> = OptimalArray::new();
        sut.push(1);
        sut.swap_remove(2);
    }

    #[test]
    fn test_locate() {
        assert_eq!(locate(0), (0, 0));
        assert_eq!(locate(1), (1, 0));
        assert_eq!(locate(2), (1, 1));
        assert_eq!(locate(3), (2, 0));
        assert_eq!(locate(4), (2, 1));
        assert_eq!(locate(5), (3, 0));
        assert_eq!(locate(6), (3, 1));
        assert_eq!(locate(7), (4, 0));
        assert_eq!(locate(8), (4, 1));
        assert_eq!(locate(9), (4, 2));
        assert_eq!(locate(10), (4, 3));
        assert_eq!(locate(12), (5, 1));
        // 14 is the last cell of the last data block of superblock 3
        assert_eq!(locate(14), (5, 3));
        assert_eq!(locate(15), (6, 0));
        assert_eq!(locate(20), (7, 1));
        // 30 is the last cell of the last data block of superblock 4
        assert_eq!(locate(30), (9, 3));
        assert_eq!(locate(33), (10, 2));
        // 62 is the last cell of the last data block of superblock 5
        assert_eq!(locate(62), (13, 7));
        // 126 is last cell of last data block of superblock 6
        assert_eq!(locate(126), (21, 7));
    }

    #[test]
    fn test_datablock_capacity_for_block() {
        assert_eq!(datablock_capacity_for_block(0), 1);
        assert_eq!(datablock_capacity_for_block(1), 2);
        assert_eq!(datablock_capacity_for_block(2), 2);
        assert_eq!(datablock_capacity_for_block(3), 2);
        assert_eq!(datablock_capacity_for_block(4), 4);
        assert_eq!(datablock_capacity_for_block(5), 4);
        assert_eq!(datablock_capacity_for_block(6), 4);
        assert_eq!(datablock_capacity_for_block(7), 4);
        assert_eq!(datablock_capacity_for_block(8), 4);
        assert_eq!(datablock_capacity_for_block(9), 4);
        assert_eq!(datablock_capacity_for_block(10), 8);
        assert_eq!(datablock_capacity_for_block(11), 8);
        assert_eq!(datablock_capacity_for_block(30), 16);
        assert_eq!(datablock_capacity_for_block(80), 32);
        assert_eq!(datablock_capacity_for_block(170), 64);
        assert_eq!(datablock_capacity_for_block(350), 128);
        assert_eq!(datablock_capacity_for_block(707), 256);
        assert_eq!(datablock_capacity_for_block(1400), 512);
        assert_eq!(datablock_capacity_for_block(3000), 1024);
        assert_eq!(datablock_capacity_for_block(6000), 2048);
        assert_eq!(datablock_capacity_for_block(12000), 4096);
        assert_eq!(datablock_capacity_for_block(24000), 8192);
        assert_eq!(datablock_capacity_for_block(49000), 16384);
        assert_eq!(datablock_capacity_for_block(98000), 32768);
        assert_eq!(datablock_capacity_for_block(100001), 65536);
    }

    #[test]
    #[should_panic(expected = "overflow, block out of bounds")]
    fn test_datablock_capacity_for_block_bounds() {
        datablock_capacity_for_block(150_000);
    }

    #[test]
    fn test_datablock_capacity() {
        assert_eq!(datablock_capacity(0), 1);
        assert_eq!(datablock_capacity(1), 2);
        assert_eq!(datablock_capacity(2), 2);
        assert_eq!(datablock_capacity(3), 4);
        assert_eq!(datablock_capacity(4), 4);
        assert_eq!(datablock_capacity(5), 8);
        assert_eq!(datablock_capacity(6), 8);
        assert_eq!(datablock_capacity(7), 16);
        assert_eq!(datablock_capacity(8), 16);
        assert_eq!(datablock_capacity(9), 32);
        assert_eq!(datablock_capacity(10), 32);
    }

    #[test]
    fn test_superblock_capacity() {
        assert_eq!(superblock_capacity(0), 1);
        assert_eq!(superblock_capacity(1), 1);
        assert_eq!(superblock_capacity(2), 2);
        assert_eq!(superblock_capacity(3), 2);
        assert_eq!(superblock_capacity(4), 4);
        assert_eq!(superblock_capacity(5), 4);
        assert_eq!(superblock_capacity(6), 8);
        assert_eq!(superblock_capacity(7), 8);
        assert_eq!(superblock_capacity(8), 16);
        assert_eq!(superblock_capacity(9), 16);
        assert_eq!(superblock_capacity(10), 32);
        assert_eq!(superblock_capacity(11), 32);
    }
}

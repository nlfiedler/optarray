//
// Copyright (c) 2025 Nathan Fiedler
//

#![allow(dead_code)]
use std::alloc::{Layout, alloc, handle_alloc_error};
use std::fmt;
use std::ops::{Index, IndexMut};

/// USIZE_BITS is the number of bits in a usize, which is used to determine a
/// value for `k` for a given zero-based index `i` into the array.
const USIZE_BITS: u32 = (8 * std::mem::size_of::<usize>()) as u32;

/// Compute the data block and element offsets (0-based) within the array for
/// the element identified by the zero-based index `i`.
fn locate(i: usize) -> (usize, usize) {
    // adding one makes the math easier?
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

/// Compute the capacity for an array with `s` superblocks and `d` data blocks.
fn array_capacity(s: usize, d: usize) -> usize {
    if s == 0 {
        0
    } else {
        let k = s - 1;
        // compute the number of data blocks before superblock k
        let leading_db = (1 << (k / 2)) + (1 << k.div_ceil(2)) - 2;
        // compute the element capacity prior to superblock k
        let leading_capacity = (1 << k) - 1;
        let db_capacity = datablock_capacity(k);
        (d - leading_db) * db_capacity + leading_capacity
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
                // have to be very large (the longest segment will be 65,536 items)
                let layout =
                    Layout::array::<T>(self.last_db_capacity).expect("unexpected overflow");
                unsafe {
                    let ptr = alloc(layout).cast::<T>();
                    if ptr.is_null() {
                        handle_alloc_error(layout);
                    }
                    self.index.push(ptr);
                }
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
            // Shrink, from Algorithm 2 of Broknik 1999 paper
            //
            // 1. Decrement n and num elements in last non-empty data block
            self.n -= 1;
            self.last_db_length -= 1;
            // 2. If last data block is empty
            if self.last_db_length == 0 {
                // (a) If there is another empty data block, Deallocate it
                if self.empty == 1 {
                    // the algorithms never explicitly set this flag nor say how
                    // to handle the extra empty block except in this step
                    todo!("where do we find this extra empty block?")
                }
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
                    // ii. If s is even, half num data blocks in superblock
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
            let (block, slot) = locate(self.n);
            unsafe { Some((self.index[block].add(slot)).read()) }
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

    /// Returns an iterator over the array.
    ///
    /// The iterator yields all items from start to end.
    pub fn iter(&self) -> OptArrayIter<'_, T> {
        OptArrayIter {
            array: self,
            index: 0,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_expansion_and_access() {
        let mut sut: OptimalArray<u64> = OptimalArray::new();
        assert_eq!(sut.len(), 0);
        assert!(sut.is_empty());
        println!("sut: {sut}");
        for value in 0..63 {
            sut.push(value);
            println!("sut: {sut}");
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

//
// Copyright (c) 2025 Nathan Fiedler
//

#![allow(dead_code)]
use std::fmt;

// USIZE_BITS is the number of bits in a usize
const USIZE_BITS: u32 = (8 * std::mem::size_of::<usize>()) as u32;

// Compute the data block and element offsets within the array.
fn locate(i: usize) -> (usize, usize) {
    // adding one makes the math easier?
    let r = i + 1;
    // k is the superblock that contains the data block
    let k = (USIZE_BITS - r.leading_zeros()) - 1;
    // tupak is the element capacity of superblock k
    let tupak = 1 << k;
    let k2 = k.div_ceil(2);
    let k2s = (1 << k2) - 1;
    // b is the relative offset of the data block within superblock k
    let b = (r ^ tupak) >> k2;
    // e is the relative offset of the element within data block b
    let e = r & k2s;
    //
    // The Broknik 1999 paper suggests p = 2^k - 1 (see Algorthim 3, step 3) but
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
    // get the total.
    //
    let p = (1 << (k / 2)) - 1 + k2s;
    (p + b, e)
}

// Compute the number of data blocks that superblock k can hold.
#[inline]
fn superblock_capacity(k: usize) -> usize {
    1 << ((k + 1).div_ceil(2) - 1)
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
    /// reallocation and copy is ever performed.
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

    // Increase the capacity of the array.
    fn grow(&mut self) {
        // Grow, from Algorithm 1 of Broknik 1999 paper
        //
        // 1. If the last non-empty data block is full:
        if self.last_db_capacity == self.last_db_length {
            // (a) If the last superblock is full:
            if self.last_sb_capacity == self.last_sb_length {
                // i. Increment s
                self.s += 1;
                // TODO: ii. If s is odd, double number of data blocks
                // TODO: iii. Else, double length of each data block
                // TODO: iv. Set occupancy of last (new) superblock to empty
                self.last_sb_length = 0;
            }
            // (b) If there are no empty data blocks:
            if self.empty == 0 {
                // TODO: i. If index block is full, double its size
                // TODO: ii. Allocate a new data block, add to index block
            }
            // (c) Increment d and the number of data blocks in last superblock
            self.d += 1;
            self.last_sb_length += 1;
            self.last_sb_capacity = superblock_capacity(self.s - 1);
            // (d) Set occupancy of new data block to empty
            self.last_db_length = 0;
        }
        // 2. Increment n and the number of elements occupying last data block
        self.n += 1;
        self.last_db_length += 1;
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

#[cfg(test)]
mod tests {
    use super::*;

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

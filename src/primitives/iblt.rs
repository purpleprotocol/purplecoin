// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT
//
// Port of IBLT by Gavin Andersen to Rust: https://github.com/gavinandresen/IBLT_Cplusplus
// Uses xxh3 instead of mmh3 for better performance.

use bincode::{Decode, Encode};
use std::ops::Sub;
use xxhash_rust::const_xxh3::const_custom_default_secret;
use xxhash_rust::xxh3::xxh3_64_with_secret as xxh3;

const N_HASH: usize = 4;

const N_HASH_SEEDS: [[u8; 192]; 4] = [
    const_custom_default_secret(0),
    const_custom_default_secret(1),
    const_custom_default_secret(2),
    const_custom_default_secret(3),
];

const N_HASHCHECK_SEED: [u8; 192] = const_custom_default_secret(11);

#[derive(Clone, Debug, PartialEq, Encode, Decode)]
pub struct IBLT {
    hash_table: Vec<IBLTHashTableEntry>,
}

impl IBLT {
    #[must_use]
    pub fn new(num_entries: usize) -> Self {
        let mut num_entries = num_entries + num_entries / 2;

        while N_HASH * (num_entries / N_HASH) != num_entries {
            num_entries += 1;
        }

        debug_assert_eq!(num_entries % N_HASH, 0);

        Self {
            hash_table: vec![Default::default(); num_entries],
        }
    }

    /// Returns Some(result) if a result is definitely found or not
    /// found. If not found, result will be empty.
    /// Returns None if overloaded and we don't know whether or
    /// not k is in the table.
    #[must_use]
    pub fn get(&self, k: u64) -> Option<Vec<u8>> {
        let mut p = None;
        let kbytes = k.to_le_bytes();
        loop {
            let this = if let Some(p) = &p { p } else { self };

            let buckets = this.hash_table.len() / N_HASH;
            for i in 0..N_HASH {
                let start = i * buckets;
                let h = xxh3(&kbytes, &N_HASH_SEEDS[i]) as usize;
                let entry = &this.hash_table[start + (h % buckets)];

                if entry.empty() {
                    return Some(vec![]);
                } else if (entry.is_pure()) {
                    if (entry.key_sum == k) {
                        return Some(entry.value_sum.clone());
                    } else {
                        return Some(vec![]);
                    }
                }
            }

            // Don't know if k in the table or not; "peel" the IBLT to try to find it:
            let mut peeled = this.clone();
            let mut erased = 0;
            for i in 0..peeled.hash_table.len() {
                let mut to_delete = None;
                {
                    let entry = &peeled.hash_table[i];
                    if entry.is_pure() {
                        if entry.key_sum == k {
                            return Some(entry.value_sum.clone());
                        }
                        erased += 1;
                        to_delete = Some((-entry.count, entry.key_sum, entry.value_sum.clone()));
                    }
                }

                if let Some((count, key_sum, value_sum)) = to_delete {
                    peeled._insert(count, key_sum, &value_sum);
                }
            }

            // Try again with smaller IBLT
            if erased > 0 {
                p = Some(peeled);
                continue;
            }

            return None;
        }
    }

    pub fn insert(&mut self, k: u64, v: &[u8]) {
        self._insert(1, k, v);
    }

    pub fn erase(&mut self, k: u64, v: &[u8]) {
        self._insert(-1, k, v);
    }

    // Returns (positive, negative) hash sets
    //  positive is all entries that were inserted
    //  negative is all entreis that were erased but never added (or
    //   if the IBLT = A-B, all entries in B that are not in A)
    // Returns Some((positive, negative)) if all entries could be decoded, None otherwise.
    #[must_use]
    pub fn list_entries(&self) -> Option<(Vec<(u64, Vec<u8>)>, Vec<(u64, Vec<u8>)>)> {
        let mut peeled = self.clone();
        let mut erased = 0;
        let mut positive = Vec::new();
        let mut negative = Vec::new();

        loop {
            for i in 0..peeled.hash_table.len() {
                let mut to_delete = None;
                {
                    let entry = &peeled.hash_table[i];

                    if entry.is_pure() {
                        if entry.count == 1 {
                            positive.push((entry.key_sum, entry.value_sum.clone()));
                        } else {
                            negative.push((entry.key_sum, entry.value_sum.clone()));
                        }
                        to_delete = Some((-entry.count, entry.key_sum, entry.value_sum.clone()));
                        erased += 1;
                    }
                }
                if let Some((count, key_sum, value_sum)) = to_delete {
                    peeled._insert(count, key_sum, &value_sum);
                }
            }

            if erased > 0 {
                erased = 0;
            } else {
                break;
            }
        }

        // If any buckets for one of the hash functions is not empty,
        // then we didn't peel them all:
        for i in 0..peeled.hash_table.len() {
            if !peeled.hash_table[i].empty() {
                return None;
            }
        }

        Some((positive, negative))
    }

    #[inline]
    fn _insert(&mut self, plus_or_minus: i32, k: u64, v: &[u8]) {
        let kbytes = k.to_le_bytes();
        let buckets = self.hash_table.len() / N_HASH;

        for i in 0..N_HASH {
            let start_entry = i * buckets;
            let h = xxh3(&kbytes, &N_HASH_SEEDS[i]) as usize;
            let entry = &mut self.hash_table[start_entry + (h % buckets)];
            entry.count += plus_or_minus;
            entry.key_sum ^= k;
            entry.key_check ^= xxh3(v, &N_HASHCHECK_SEED);
            if entry.empty() {
                entry.value_sum.clear();
            } else {
                entry.add_value(v);
            }
        }
    }
}

impl Sub for IBLT {
    type Output = Self;

    fn sub(mut self, mut other: Self) -> Self::Output {
        debug_assert_eq!(self.hash_table.len(), other.hash_table.len());

        for i in 0..self.hash_table.len() {
            let e1 = &mut self.hash_table[i];
            let e2 = &mut other.hash_table[i];
            e1.count -= e2.count;
            e1.key_sum ^= e2.key_sum;
            e1.key_check ^= e2.key_check;
            if e1.empty() {
                e1.value_sum.clear();
            } else {
                e1.add_value(&e2.value_sum);
            }
        }

        self
    }
}

#[derive(Clone, Debug, PartialEq, Encode, Decode, Default)]
struct IBLTHashTableEntry {
    pub count: i32,
    pub key_sum: u64,
    pub key_check: u64,
    pub value_sum: Vec<u8>,
}

impl IBLTHashTableEntry {
    pub fn empty(&self) -> bool {
        self.count == 0 && self.key_sum == 0 && self.key_check == 0
    }

    pub fn is_pure(&self) -> bool {
        if self.count == 1 || self.count == -1 {
            let check = xxh3(&self.key_sum.to_le_bytes(), &N_HASHCHECK_SEED);
            return self.key_check == check;
        }

        false
    }

    #[inline]
    pub fn add_value(&mut self, v: &[u8]) {
        if v.is_empty() {
            return;
        }

        if self.value_sum.len() < v.len() {
            self.value_sum.resize(v.len(), 0);
        }

        for i in 0..v.len() {
            self.value_sum[i] ^= v[i];
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // #[test]
    // fn it_gets_values() {
    //     let mut iblt = IBLT::new(25);
    //     iblt.insert(342, b"fdsf1");
    //     iblt.insert(346, b"jgoi2");
    //     iblt.insert(378, b"jiz54");
    //     iblt.insert(398, b"589fn");
    //     iblt.insert(444, b"test5");
    //     iblt.insert(345654, b"test6");
    //     iblt.insert(5343542, b"test7");
    //     iblt.insert(542, b"test8");
    //     println!("{:?}", iblt);
    //     println!("{:?}", iblt.list_entries());
    //     assert_eq!(iblt.get(342), Some(b"fdsf1".to_vec()));
    //     assert_eq!(iblt.get(346), Some(b"jgoi2".to_vec()));
    //     assert_eq!(iblt.get(378), Some(b"jiz54".to_vec()));
    //     assert_eq!(iblt.get(398), Some(b"589fn".to_vec()));
    //     assert_eq!(iblt.get(345654), Some(b"test6".to_vec()));
    //     assert_eq!(iblt.get(5343542), Some(b"test7".to_vec()));
    //     assert_eq!(iblt.get(542), Some(b"test8".to_vec()));
    // }
}

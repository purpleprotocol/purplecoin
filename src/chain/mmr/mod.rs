// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::mmr::merkle_proof::MMRMerkleProof;
use crate::chain::mmr::util::*;
use crate::primitives::Hash256;
use bincode::Encode;
use rocksdb::Error as RocksDBErr;

/// MMR trait
pub trait MMR<'a, T: Encode, B: MMRBackend<T> + 'a> {
    /// Returns the root hash of the MMR
    fn root(&self) -> Result<Hash256, MMRBackendErr> {
        self.backend().root()
    }

    /// Attempts to append a new leaf to the mmr
    fn append(&'a mut self, leaf: &T) -> Result<(), MMRBackendErr> {
        let mut pos = self.backend().size()?;
        let mut current_hash = hash_leaf_with_pos(leaf, pos, self.hash_key());
        let mut hashes = vec![current_hash];

        let (peak_map, height) = peak_map_height(pos);
        if height != 0 {
            return Err(MMRBackendErr::InvalidMMRSize);
        }

        let mut peak = 1;
        while (peak_map & peak) != 0 {
            let left_sibling = pos + 1 - 2 * peak;
            let left_hash =
                self.backend()
                    .get(left_sibling)?
                    .ok_or(MMRBackendErr::CustomString(
                        "could not fetch left sibling".to_owned(),
                    ))?;
            peak *= 2;
            pos += 1;
            current_hash = hash_children_with_pos((left_hash, current_hash), pos, self.hash_key());
            hashes.push(current_hash);
        }

        self.backend().append(leaf, hashes)?;
        Ok(())
    }

    /// Returns a reference to the underlying MMRBackend
    fn backend(&self) -> &B;

    /// Returns the key passed to the hash function used in constructing the MMR
    fn hash_key(&'a self) -> &'a str {
        self.backend().hash_key()
    }
}

/// Trait for general MMR backend
pub trait MMRBackend<T: Encode> {
    /// Append new leaves to the MMR
    fn append(&self, leaf: &T, hashes: Vec<Hash256>) -> Result<(), MMRBackendErr> {
        // Write leaf data
        self.write_leaf(hashes[0], leaf)?;

        // Write hashes
        let mut pos = self.unpruned_size()?;
        for h in hashes.iter() {
            self.write_hash_at_pos(*h, pos)?;
            pos += 1;
        }

        Ok(())
    }

    /// Retrieve element at pos
    fn get(&self, pos: u64) -> Result<Option<Hash256>, MMRBackendErr>;

    /// Retrieve peak at pos
    fn get_peak(&self, pos: u64) -> Result<Option<Hash256>, MMRBackendErr>;

    /// Retrieve the hash of the element at pos
    fn get_hash(&self, pos: u64) -> Result<Option<Hash256>, MMRBackendErr>;

    /// Returns the leaf data for hash
    fn get_leaf(&self, hash: &Hash256) -> Result<Option<T>, MMRBackendErr>;

    /// Writes the leaf data for hash
    fn write_leaf(&self, hash: Hash256, leaf: &T) -> Result<(), MMRBackendErr>;

    /// Writes the given hash at position
    fn write_hash_at_pos(&self, hash: Hash256, pos: u64) -> Result<(), MMRBackendErr>;

    /// Returns the size of the mmr
    fn size(&self) -> Result<u64, MMRBackendErr>;

    /// Iterator over current (unpruned, unremoved) leaf positions.
	fn leaf_pos_iter(&self) -> Box<dyn Iterator<Item = u64> + '_>;

	/// Iterator over current (unpruned, unremoved) leaf insertion indices.
	fn leaf_idx_iter(&self, from_idx: u64) -> Box<dyn Iterator<Item = u64> + '_>;

    /// Returns the unpruned size of the mmr
    fn unpruned_size(&self) -> Result<u64, MMRBackendErr>;

    /// Number of leaves in the MMR
	fn n_unpruned_leaves(&self) -> u64;

	/// Number of leaves in the MMR up to index
	fn n_unpruned_leaves_to_index(&self, to_index: u64) -> u64;

    /// Returns the key passed to the hash function used in constructing the MMR
    fn hash_key(&self) -> &str;

    /// Returns `true` if the mmr is empty
    fn is_empty(&self) -> Result<bool, MMRBackendErr> {
        Ok(self.unpruned_size()? == 0)
    }

    /// Taken from https://github.com/mimblewimble/grin/blob/master/core/src/core/pmmr/pmmr.rs
    ///
    /// Takes a single peak position and hashes together
    /// all the peaks to the right of this peak (if any).
    /// If this return a hash then this is our peaks sibling.
    /// If none then the sibling of our peak is the peak to the left.
    fn bag_the_rhs(&self, peak_pos0: u64) -> Result<Option<Hash256>, MMRBackendErr> {
        let size = self.unpruned_size()?;
        let rhs = peaks(size).into_iter().filter(|&x| x > peak_pos0);

        let mut res = None;
        for x in rhs.rev() {
            let peak = self.get(x)?;
            if let Some(peak) = peak {
                res = match res {
                    None => Some(peak),
                    Some(rhash) => {
                        Some(hash_children_with_pos((peak, rhash), size, self.hash_key()))
                    }
                }
            }
        }
        Ok(res)
    }

    /// Taken from https://github.com/mimblewimble/grin/blob/master/core/src/core/pmmr/pmmr.rs
    ///
    /// Returns a vec of the peaks of this MMR.
    fn peaks(&self) -> Result<Vec<Hash256>, MMRBackendErr> {
        let mut res = vec![];
        for pi0 in peaks(self.unpruned_size()?).into_iter() {
            let p = self.get_peak(pi0)?;
            if let Some(p) = p {
                res.push(p);
            }
        }

        Ok(res)
    }

    /// Taken from https://github.com/mimblewimble/grin/blob/master/core/src/core/pmmr/pmmr.rs
    ///
    /// Hashes of the peaks excluding `peak_pos`, where the rhs is bagged together
    fn peak_path(&self, peak_pos0: u64) -> Result<Vec<Hash256>, MMRBackendErr> {
        let rhs = self.bag_the_rhs(peak_pos0)?;
        let mut res = vec![];

        for x in peaks(self.unpruned_size()?)
            .into_iter()
            .filter(|&x| x < peak_pos0)
        {
            let x = self.get_peak(x)?;
            if let Some(x) = x {
                res.push(x);
            }
        }
        if let Some(rhs) = rhs {
            res.push(rhs);
        }
        res.reverse();

        Ok(res)
    }

    /// Flush current state to disk
    fn flush(&mut self) -> Result<(), MMRBackendErr>;

    /// Attempts to prune leaves from the MMR
    fn prune(&mut self) -> Result<(), MMRBackendErr>;

    /// Taken from https://github.com/mimblewimble/grin/blob/master/core/src/core/pmmr/pmmr.rs
    ///
    /// Walks all unpruned nodes in the MMR and revalidate all parent hashes
    fn validate(&self) -> Result<(), MMRBackendErr> {
        // iterate on all parent nodes
        for n in 0..self.size()? {
            let height = bintree_postorder_height(n);
            if height > 0 {
                if let Some(hash) = self.get_hash(n)? {
                    let left_pos = n - (1 << height);
                    let right_pos = n - 1;
                    if let Some(left_child_hs) = self.get(left_pos)? {
                        if let Some(right_child_hs) = self.get(right_pos)? {
                            // hash the two child nodes together with parent_pos and compare
                            if hash_children_with_pos(
                                (left_child_hs, right_child_hs),
                                n,
                                self.hash_key(),
                            ) != hash
                            {
                                return Err(MMRBackendErr::InvalidMMRParentHash(n + 1));
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Taken from https://github.com/mimblewimble/grin/blob/master/core/src/core/pmmr/pmmr.rs
    ///
    /// Computes the root of the MMR. Find all the peaks in the current
    /// tree and "bags" them to get a single peak.
    fn root(&self) -> Result<Hash256, MMRBackendErr> {
        if self.is_empty()? {
            return Ok(Hash256::zero());
        }
        let mut res = None;
        let peaks = self.peaks()?;
        let mmr_size = self.size()?;
        for peak in peaks.into_iter().rev() {
            res = match res {
                None => Some(peak),
                Some(rhash) => Some(hash_children_with_pos(
                    (peak, rhash),
                    mmr_size,
                    self.hash_key(),
                )),
            }
        }
        res.ok_or_else(|| MMRBackendErr::CustomString("no root, invalid tree".to_owned()))
    }

    /// Taken from https://github.com/mimblewimble/grin/blob/master/core/src/core/pmmr/pmmr.rs
    ///
    /// Build a Merkle proof for the element at the given position.
    fn merkle_proof(&self, pos0: u64) -> Result<MMRMerkleProof, MMRBackendErr> {
        let size = self.unpruned_size()?;
        #[cfg(debug_assertions)]
        println!("merkle_proof  {pos0}, size {size}");

        // check this pos is actually a leaf in the MMR
        if !is_leaf(pos0) {
            return Err(MMRBackendErr::CustomString(format!(
                "not a leaf at pos {pos0}"
            )));
        }

        // check we actually have a hash in the MMR at this pos
        self.get_hash(pos0)?
            .ok_or_else(|| MMRBackendErr::CustomString(format!("no element at pos {pos0}")))?;

        let family_branch = family_branch(pos0, size);

        let mut path = vec![];

        for x in family_branch.iter() {
            let x = self.get(x.1)?;
            if let Some(x) = x {
                path.push(x);
            }
        }

        let peak_pos = match family_branch.last() {
            Some(&(x, _)) => x,
            None => pos0,
        };

        path.append(&mut self.peak_path(peak_pos)?);

        Ok(MMRMerkleProof {
            mmr_size: size,
            path,
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum MMRBackendErr {
    InvalidMMRSize,
    InvalidMMRParentHash(u64),
    CorruptData,
    CustomString(String),
    RocksDB(RocksDBErr),
}

impl From<RocksDBErr> for MMRBackendErr {
    fn from(error: RocksDBErr) -> Self {
        Self::RocksDB(error)
    }
}

impl From<String> for MMRBackendErr {
    fn from(error: String) -> Self {
        Self::CustomString(error)
    }
}

impl From<&str> for MMRBackendErr {
    fn from(error: &str) -> Self {
        Self::CustomString(error.to_owned())
    }
}

mod leaf_set;
mod merkle_proof;
mod prune_list;
mod util;

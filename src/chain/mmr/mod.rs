// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::mmr::leaf_set::LeafSetRwLockIter;
use crate::chain::mmr::merkle_proof::MMRMerkleProof;
use crate::chain::mmr::util::{
    bintree_postorder_height, family_branch, hash_children_with_pos, hash_leaf_with_pos,
    insertion_to_pmmr_index, is_leaf, n_leaves, peak_map_height, peaks,
};
use crate::primitives::Hash256;
use bincode::Encode;
use rocksdb::Error as RocksDBErr;

/// Trait for general MMR backend
pub trait MMRBackend<T: Encode> {
    /// Push a new leaf to the MMR
    fn push(&self, leaf: &T) -> Result<u64, MMRBackendErr> {
        let leaf_pos = self.unpruned_size()?;
        let mut current_hash = hash_leaf_with_pos(leaf, leaf_pos, self.hash_key());

        let mut hashes = vec![current_hash];
        let mut pos = leaf_pos;

        let (peak_map, height) = peak_map_height(pos);
        if height != 0 {
            return Err(format!("bad mmr size {pos}").into());
        }
        // hash with all immediately preceding peaks, as indicated by peak map
        let mut peak = 1;
        while (peak_map & peak) != 0 {
            let left_sibling = pos + 1 - 2 * peak;
            let left_hash = self
                .get_peak(left_sibling)?
                .ok_or("missing left sibling in tree, should not have been pruned")?;
            peak *= 2;
            pos += 1;
            current_hash = hash_children_with_pos((left_hash, current_hash), pos, self.hash_key());
            hashes.push(current_hash);
        }

        // append all the new nodes and update the MMR index
        self.append(leaf, hashes)?;
        self.set_size(pos + 1)?;
        Ok(leaf_pos)
    }

    /// Append new leaves to the MMR
    fn append(&self, leaf: &T, hashes: Vec<Hash256>) -> Result<(), MMRBackendErr> {
        // Write leaf data
        self.write_leaf(hashes[0], leaf)?;

        // Write hashes
        let mut pos = self.unpruned_size()?;
        for h in &hashes {
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

    /// Sets new mmr size
    fn set_size(&self, size: u64) -> Result<(), MMRBackendErr>;

    /// Writes the leaf data for hash
    fn write_leaf(&self, hash: Hash256, leaf: &T) -> Result<(), MMRBackendErr>;

    /// Writes the given hash at position
    fn write_hash_at_pos(&self, hash: Hash256, pos: u64) -> Result<(), MMRBackendErr>;

    /// Returns the size of the mmr
    fn size(&self) -> Result<u64, MMRBackendErr>;

    /// Iterator over current (unpruned, unremoved) leaf positions.
    #[must_use]
    fn leaf_pos_iter<'a>(iter: &'a LeafSetRwLockIter<'a>) -> Box<dyn Iterator<Item = u64> + '_> {
        Box::new(iter.into_iter().map(|x| x - 1))
    }

    /// Iterator over current (unpruned, unremoved) leaf insertion indices.
    #[must_use]
    fn leaf_idx_iter<'a>(
        iter: &'a LeafSetRwLockIter<'a>,
        from_idx: u64,
    ) -> Box<dyn Iterator<Item = u64> + '_> {
        // pass from_idx in as param
        // convert this to pos
        // iterate, skipping everything prior to this
        // pass in from_idx=0 then we want to convert to pos=1

        let from_pos = 1 + insertion_to_pmmr_index(from_idx);

        Box::new(
            iter.into_iter()
                .skip_while(move |x| *x < from_pos)
                .map(|x| n_leaves(x).saturating_sub(1)),
        )
    }

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
        for pi0 in peaks(self.unpruned_size()?) {
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

        for x in &family_branch {
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

pub mod leaf_set;
pub mod merkle_proof;
pub mod prune_list;
pub mod util;

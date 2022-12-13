// Copyright 2021 The Grin Developers
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! The Grin leaf_set implementation.
//! Compact (roaring) bitmap representing the set of leaf positions
//! that exist and are not currently pruned in the MMR.

use std::sync::Arc;

use crate::chain::backend::disk::*;
use crate::chain::backend::*;
use crate::chain::mmr::prune_list::PruneList;
use crate::chain::mmr::util::*;
use croaring::Bitmap;

/// Compact (roaring) bitmap representing the set of positions of
/// leaves that are currently unpruned in the MMR.
pub struct LeafSet<'a> {
    key: &'a str,
    db: Arc<DB>,
    bitmap: Bitmap,
    bitmap_bak: Bitmap,
}

impl<'a> LeafSet<'a> {
    /// Open the remove log file.
    /// The content of the file will be read in memory for fast checking.
    pub fn open(db: Arc<DB>, key: &'a str) -> Result<Self, String> {
        let bitmap = read_bitmap(db.clone(), key)?.unwrap_or(Bitmap::default());

        if !bitmap.is_empty() {
            #[cfg(debug_assertions)]
            println!(
                "bitmap {} pos ({} bytes)",
                bitmap.cardinality(),
                bitmap.get_serialized_size_in_bytes(),
            );
        }

        Ok(LeafSet {
            key,
            db,
            bitmap_bak: bitmap.clone(),
            bitmap,
        })
    }

    /// Calculate the set of unpruned leaves
    /// up to and including the cutoff_pos.
    /// Only applicable for the output MMR.
    fn unpruned_pre_cutoff(&self, cutoff_pos: u64, prune_list: &PruneList) -> Bitmap {
        (1..=cutoff_pos)
            .filter(|&x| is_leaf(x - 1) && !prune_list.is_pruned(x - 1))
            .map(|x| x as u32)
            .collect()
    }

    /// Calculate the set of pruned positions
    /// up to and including the cutoff_pos.
    /// Uses both the leaf_set and the prune_list to determine prunedness.
    pub fn removed_pre_cutoff(
        &self,
        cutoff_pos: u64,
        rewind_rm_pos: &Bitmap,
        prune_list: &PruneList,
    ) -> Bitmap {
        let mut bitmap = self.bitmap.clone();

        // First remove pos from leaf_set that were
        // added after the point we are rewinding to.
        let to_remove = ((cutoff_pos + 1) as u32)..bitmap.maximum().unwrap_or(0);
        bitmap.remove_range(to_remove);

        // Then add back output pos to the leaf_set
        // that were removed.
        bitmap.or_inplace(&rewind_rm_pos);

        // Invert bitmap for the leaf pos and return the resulting bitmap.
        bitmap
            .flip(1..(cutoff_pos + 1) as u32)
            .and(&self.unpruned_pre_cutoff(cutoff_pos, prune_list))
    }

    /// Rewinds the leaf_set back to a previous state.
    /// Removes all pos after the cutoff.
    /// Adds back all pos in rewind_rm_pos.
    pub fn rewind(&mut self, cutoff_pos: u64, rewind_rm_pos: &Bitmap) {
        // First remove pos from leaf_set that were
        // added after the point we are rewinding to.
        let to_remove = ((cutoff_pos + 1) as u32)..self.bitmap.maximum().unwrap_or(0);
        self.bitmap.remove_range(to_remove);

        // Then add back output pos to the leaf_set
        // that were removed.
        self.bitmap.or_inplace(&rewind_rm_pos);
    }

    /// Append a new position to the leaf_set.
    pub fn add(&mut self, pos0: u64) {
        self.bitmap.add(1 + pos0 as u32);
    }

    /// Remove the provided position from the leaf_set.
    pub fn remove(&mut self, pos0: u64) {
        self.bitmap.remove(1 + pos0 as u32);
    }

    /// Flush the leaf_set to file.
    pub fn flush(&mut self) -> Result<(), String> {
        // First run the optimization step on the bitmap.
        self.bitmap.run_optimize();

        // Write the updated bitmap file to disk.
        write_bitmap(self.db.clone(), self.key, self.bitmap.clone());

        // Make sure our backup in memory is up to date.
        self.bitmap_bak = self.bitmap.clone();

        Ok(())
    }

    /// Discard any pending changes.
    pub fn discard(&mut self) {
        self.bitmap = self.bitmap_bak.clone();
    }

    /// Whether the leaf_set includes the provided position.
    pub fn includes(&self, pos0: u64) -> bool {
        self.bitmap.contains(1 + pos0 as u32)
    }

    /// Number of positions stored in the leaf_set.
    pub fn len(&self) -> usize {
        self.bitmap.cardinality() as usize
    }

    /// Is the leaf_set empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Iterator over positionns in the leaf_set (all leaf positions).
    pub fn iter(&self) -> impl Iterator<Item = u64> + '_ {
        self.bitmap.iter().map(|x| x as u64)
    }
}

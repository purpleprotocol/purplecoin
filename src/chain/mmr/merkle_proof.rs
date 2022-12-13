// Copyright 2021 The Grin Developers
//
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

//! Merkle Proofs

use crate::chain::mmr::util::*;
use crate::primitives::*;
use bincode::{Decode, Encode};

/// Merkle proof errors.
#[derive(Clone, Debug, PartialEq)]
pub enum MMRMerkleProofError {
    /// Merkle proof root hash does not match when attempting to verify.
    RootMismatch,
}

/// A Merkle proof that proves a particular element exists in the MMR.
#[derive(Debug, Eq, PartialEq, Clone, PartialOrd, Ord, Encode, Decode)]
pub struct MMRMerkleProof {
    /// The size of the MMR at the time the proof was created.
    pub mmr_size: u64,
    /// The sibling path from the leaf up to the final sibling hashing to the
    /// root.
    pub path: Vec<Hash256>,
}

impl Default for MMRMerkleProof {
    fn default() -> MMRMerkleProof {
        MMRMerkleProof::empty()
    }
}

impl MMRMerkleProof {
    /// The "empty" Merkle proof.
    pub fn empty() -> MMRMerkleProof {
        MMRMerkleProof {
            mmr_size: 0,
            path: Vec::default(),
        }
    }

    /// Serialize the Merkle proof as a hex string (for api json endpoints)
    pub fn to_hex(&self) -> String {
        let mut buf = crate::codec::encode_to_vec(self).unwrap();
        hex::encode(buf)
    }

    /// Convert hex string representation back to a Merkle proof instance
    pub fn from_hex(hex: &str) -> Result<MMRMerkleProof, String> {
        let bytes = hex::decode(hex).unwrap();
        let res = crate::codec::decode(&bytes[..])
            .map_err(|_| "failed to deserialize a Merkle Proof".to_string())?;
        Ok(res)
    }

    /// Verifies the Merkle proof against the provided
    /// root hash, element and position in the MMR.
    pub fn verify<T: PMMRIndexHashable>(
        &self,
        root: Hash256,
        element: &T,
        node_pos: u64,
        key: &str,
    ) -> Result<(), MMRMerkleProofError> {
        let mut proof = self.clone();
        // calculate the peaks once as these are based on overall MMR size
        // (and will not change)
        let peaks_pos = peaks(self.mmr_size);
        proof.verify_consume(root, element, node_pos, &peaks_pos, key)
    }

    /// Consumes the Merkle proof while verifying it.
    /// The proof can no longer be used by the caller after dong this.
    /// Caller must clone() the proof first.
    fn verify_consume<T: PMMRIndexHashable>(
        &mut self,
        root: Hash256,
        element: &T,
        node_pos0: u64,
        peaks_pos0: &[u64],
        key: &str,
    ) -> Result<(), MMRMerkleProofError> {
        let node_hash = if node_pos0 >= self.mmr_size {
            element.hash_with_index(self.mmr_size, key)
        } else {
            element.hash_with_index(node_pos0, key)
        };

        // handle special case of only a single entry in the MMR
        // (no siblings to hash together)
        if self.path.is_empty() {
            if root == node_hash {
                return Ok(());
            } else {
                return Err(MMRMerkleProofError::RootMismatch);
            }
        }

        let sibling = self.path.remove(0);
        let (parent_pos0, sibling_pos0) = family(node_pos0);

        if let Ok(x) = peaks_pos0.binary_search(&(node_pos0)) {
            let parent = if x == peaks_pos0.len() - 1 {
                (sibling, node_hash)
            } else {
                (node_hash, sibling)
            };
            self.verify(root, &parent, parent_pos0, key)
        } else if parent_pos0 >= self.mmr_size {
            let parent = (sibling, node_hash);
            self.verify(root, &parent, parent_pos0, key)
        } else {
            let parent = if is_left_sibling(sibling_pos0) {
                (sibling, node_hash)
            } else {
                (node_hash, sibling)
            };
            self.verify(root, &parent, parent_pos0, key)
        }
    }
}

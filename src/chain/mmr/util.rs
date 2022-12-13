// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::primitives::*;
use bincode::Encode;
use std::{ops::Range, u64};

pub fn hash_leaf_with_pos<T: Encode>(leaf: &T, pos: u64, key: &str) -> Hash256 {
    let mut buf = crate::codec::encode_to_vec(leaf).unwrap();
    buf.extend_from_slice(&pos.to_le_bytes());
    Hash256::hash_from_slice(&buf, key)
}

pub fn hash_children_with_pos(v: (Hash256, Hash256), pos: u64, key: &str) -> Hash256 {
    v.hash_with_index(pos, key)
}

// The rest of the file is taken from https://github.com/mimblewimble/grin/blob/master/core/src/core/pmmr/pmmr.rs
// and is distributed under the following license:
//
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

/// 64 bits all ones: 0b11111111...1
const ALL_ONES: u64 = u64::MAX;

/// peak bitmap and height of next node in mmr of given size
/// Example: on size 4 returns (0b11, 0) as mmr tree of size 4 is
///    2
///   / \
///  0   1   3
/// with 0b11 indicating the presence of peaks of height 0 and 1,
/// and 0 the height of the next node 4, which is a leaf
/// NOTE:
/// the peak map also encodes the path taken from the root to the added node
/// since the path turns left (resp. right) if-and-only-if
/// a peak at that height is absent (resp. present)
pub fn peak_map_height(mut size: u64) -> (u64, u64) {
    if size == 0 {
        // rust can't shift right by 64
        return (0, 0);
    }
    let mut peak_size = ALL_ONES >> size.leading_zeros();
    let mut peak_map = 0;
    while peak_size != 0 {
        peak_map <<= 1;
        if size >= peak_size {
            size -= peak_size;
            peak_map |= 1;
        }
        peak_size >>= 1;
    }
    (peak_map, size)
}

/// The height of a node in a full binary tree from its postorder traversal
/// index.
pub fn bintree_postorder_height(pos0: u64) -> u64 {
    peak_map_height(pos0).1
}

/// Is this position a leaf in the MMR?
/// We know the positions of all leaves based on the postorder height of an MMR
/// of any size (somewhat unintuitively but this is how the PMMR is "append
/// only").
pub fn is_leaf(pos0: u64) -> bool {
    bintree_postorder_height(pos0) == 0
}

/// Calculates the positions of the parent and sibling of the node at the
/// provided position.
pub fn family(pos0: u64) -> (u64, u64) {
    let (peak_map, height) = peak_map_height(pos0);
    let peak = 1 << height;
    if (peak_map & peak) != 0 {
        (pos0 + 1, pos0 + 1 - 2 * peak)
    } else {
        (pos0 + 2 * peak, pos0 + 2 * peak - 1)
    }
}

/// Gets the position of the rightmost node (i.e. leaf) beneath the provided subtree root.
pub fn bintree_rightmost(pos0: u64) -> u64 {
    pos0 - bintree_postorder_height(pos0)
}

/// Gets the position of the leftmost node (i.e. leaf) beneath the provided subtree root.
pub fn bintree_leftmost(pos0: u64) -> u64 {
    let height = bintree_postorder_height(pos0);
    pos0 + 2 - (2 << height)
}

/// All pos in the subtree beneath the provided root, including root itself.
pub fn bintree_range(pos0: u64) -> Range<u64> {
    let height = bintree_postorder_height(pos0);
    let leftmost = pos0 + 2 - (2 << height);
    leftmost..(pos0 + 1)
}

/// Gets the postorder traversal 0-based index of all peaks in a MMR given its size.
/// Starts with the top peak, which is always on the left
/// side of the range, and navigates toward lower siblings toward the right
/// of the range.
/// For some odd reason, return empty when next node is not a leaf
pub fn peaks(size: u64) -> Vec<u64> {
    let (peak_sizes, height) = peak_sizes_height(size);
    if height == 0 {
        peak_sizes
            .iter()
            .scan(0, |acc, &x| {
                *acc += &x;
                Some(*acc)
            })
            .map(|x| x - 1) // rust doesn't allow starting scan with -1 as u64
            .collect()
    } else {
        vec![]
    }
}

/// sizes of peaks and height of next node in mmr of given size
/// similar to peak_map_height but replacing bitmap by vector of sizes
/// Example: on input 5 returns ([3,1], 1) as mmr state before adding 5 was
///    2
///   / \
///  0   1   3   4
pub fn peak_sizes_height(mut size: u64) -> (Vec<u64>, u64) {
    if size == 0 {
        // rust can't shift right by 64
        return (vec![], 0);
    }
    let mut peak_size = ALL_ONES >> size.leading_zeros();
    let mut peak_sizes = vec![];
    while peak_size != 0 {
        if size >= peak_size {
            peak_sizes.push(peak_size);
            size -= peak_size;
        }
        peak_size >>= 1;
    }
    (peak_sizes, size)
}

/// For a given starting position calculate the parent and sibling positions
/// for the branch/path from that position to the peak of the tree.
/// We will use the sibling positions to generate the "path" of a Merkle proof.
pub fn family_branch(pos0: u64, size: u64) -> Vec<(u64, u64)> {
    // loop going up the tree, from node to parent, as long as we stay inside
    // the tree (as defined by size).
    let (peak_map, height) = peak_map_height(pos0);
    let mut peak = 1 << height;
    let mut branch = vec![];
    let mut current = pos0;
    let mut sibling;
    while current + 1 < size {
        if (peak_map & peak) != 0 {
            current += 1;
            sibling = current - 2 * peak;
        } else {
            current += 2 * peak;
            sibling = current - 1;
        };
        if current >= size {
            break;
        }
        branch.push((current, sibling));
        peak <<= 1;
    }
    branch
}

/// Is the node at this pos the "left" sibling of its parent?
pub fn is_left_sibling(pos0: u64) -> bool {
    let (peak_map, height) = peak_map_height(pos0);
    let peak = 1 << height;
    (peak_map & peak) == 0
}

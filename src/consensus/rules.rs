// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use static_assertions::{const_assert, const_assert_eq};
use std::cmp::{self, Ordering};
use std::ops::RangeInclusive;

/// Money type
pub type Money = i128;

/// Satoshis per coin. We chose to name of the smallest unit in honour of Bitcoin's mysterious creator.
///
/// In order to differentiate between satoshis in Bitcoin and in Purplecoin, we shall refer to satoshis in Purplecoin as
/// `purple satoshis` or `psats` for short.
pub const COIN: Money = 1_000_000_000_000_000_000;

/// Difficulty will be adjusted so that blocks are added in `n` secs
pub const BLOCK_TIME_SECONDS: u64 = 30;

/// New blocks with timestamps that are lesser than `current_time - n` will be rejected. Expressed in seconds
pub const BLOCK_TIMESTAMP_MIN: u64 = 60;

/// New block with timestamps greater than `current_time + n` will be rejected. Expressed in seconds
pub const BLOCK_TIMESTAMP_MAX: u64 = 60;

/// Maximum block size in bytes
pub const MAX_BYTES_PER_BLOCK: u64 = 380_000;

/// Max bytes per transaction
pub const TRANSACTION_LIMIT_SIZE: u64 = 10_000;

/// Max number of opcodes that can be executed per script
pub const SCRIPT_LIMIT_OPCODES: u64 = 2_500;

/// Initial block reward, per shard. The miner reward is equal to `INITIAL_BLOCK_REWARD` * `SHARDS_PER_SECTOR`
pub const INITIAL_BLOCK_REWARD: Money = COIN; // 1 XPU

/// Amount of coins mined in the genesis block
pub const PRE_MINED_COINS: Money = COIN * 227_994_000;

/// Reward is halved after `n` blocks
pub const HALVING_INTERVAL: u64 = 4_200_000;

/// Only `n` halvings will happen, after which the block reward will remain constant
pub const MAX_HALVINGS: u64 = 20;

/// Max blocktime in regards to consensus calculations
pub const MAX_BLOCK_TIME: i64 = 60;

/// Coinbase outputs cannot be spent until `cur_height - output_height > BLOCK_HORIZON`.
///
/// All transactions are considered final after the `BLOCK_HORIZON`
///
/// All unspent outputs we don't care about are pruned after `BLOCK_HORIZON` blocks past the current height
pub const BLOCK_HORIZON: u64 = 8;

/// How long to spend mining for additional runnerups after receiving a runnerup block
pub const FIRST_ROUND_ADDITIONAL_TIME: i64 = 3;

/// Time in seconds to wait for a second round miner to find a block before
/// judging it as a timeout. After the timeout, all miners become eligible to
/// mine in the second round
pub const SECOND_ROUND_TIMEOUT: i64 = 90;

/// Minimum GR difficulty
pub const MIN_DIFF_GR: u32 = 0x010f_ffff;

/// Minimum Random hash `PoW` difficulty
pub const MIN_DIFF_RANDOM_HASH: u32 = 0x020f_ffff;

/// False positive rate for block header bloom filter
pub const BLOCK_HEADER_BLOOM_FP_RATE: f64 = 0.005;

/// Number of accumulators per shard
pub const ACCUMULATOR_MULTIPLIER: usize = 24;

/// Number of shards per sector
pub const SHARDS_PER_SECTOR: usize = 16;

/// Number of sectors
pub const SECTORS: usize = 256 / SHARDS_PER_SECTOR;

/// Money check
#[must_use]
pub fn money_check(amount: Money) -> bool {
    amount >= 0
}

/// Get block reward at height
#[must_use]
pub fn map_height_to_block_reward(height: u64) -> Money {
    let h = cmp::min(
        Money::from(height) / Money::from(HALVING_INTERVAL),
        Money::from(MAX_HALVINGS),
    );
    INITIAL_BLOCK_REWARD >> h
}

/// Calculate new bits based on blocktime and old bits
#[must_use]
pub fn calc_difficulty(bits: u32, blocktime: u64) -> u32 {
    let mut diff = Difficulty::new(bits);
    let diff_change = (BLOCK_TIME_SECONDS as f32 / blocktime as f32).clamp(0.5f32, 2f32);
    diff.scale(diff_change).to_u32()
}

/// Map sector id to a range of chain ids
#[must_use]
pub fn map_sector_id_to_chain_ids(sector_id: u8) -> Option<RangeInclusive<u8>> {
    let sectors = SECTORS as u8;

    if sector_id >= sectors {
        return None;
    }

    let start_i = (sector_id / SHARDS_PER_SECTOR as u8) * SHARDS_PER_SECTOR as u8;

    Some(RangeInclusive::new(
        start_i,
        start_i + SHARDS_PER_SECTOR as u8 - 1,
    ))
}

const_assert!(COIN > 0);
const_assert!(BLOCK_HORIZON >= 6);
const_assert!(BLOCK_HORIZON <= 100);
const_assert!(BLOCK_HORIZON % 2 == 0);
const_assert!(MAX_BYTES_PER_BLOCK >= 380_000);
const_assert!(MAX_BYTES_PER_BLOCK <= 750_000);
const_assert!(BLOCK_HEADER_BLOOM_FP_RATE >= 0.001);
const_assert!(BLOCK_HEADER_BLOOM_FP_RATE <= 0.1);
const_assert!(SHARDS_PER_SECTOR > 1);
const_assert!(256 % SHARDS_PER_SECTOR == 0);
const_assert!(ACCUMULATOR_MULTIPLIER > 0);
const_assert_eq!(HALVING_INTERVAL % 4, 0);
const_assert_eq!(SECOND_ROUND_TIMEOUT, BLOCK_TIME_SECONDS as i64 * 3);
const_assert_eq!(BLOCK_TIMESTAMP_MAX, BLOCK_TIME_SECONDS * 2);
const_assert_eq!(BLOCK_TIMESTAMP_MIN, BLOCK_TIME_SECONDS * 2);

const MAX_ZEROS: u8 = 252;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Difficulty(u32);

impl Difficulty {
    #[must_use]
    pub fn to_u32(&self) -> u32 {
        self.0
    }
    #[must_use]
    pub fn new(d: u32) -> Self {
        Difficulty(d)
    }
    #[must_use]
    pub fn zeros(&self) -> usize {
        (self.0 >> 24) as usize
    }
    #[must_use]
    pub fn postfix(&self) -> u32 {
        self.0 & 0x00ff_ffff
    }
    #[must_use]
    pub fn power(&self) -> u128 {
        (2f32.powf(self.zeros() as f32 * 8f32) * (0x00ff_ffff as f32 / self.postfix() as f32))
            as u128
    }

    #[must_use]
    pub fn scale(&self, f: f32) -> Self {
        let mply = ((u64::from(self.postfix()) << 16) as f32 / f) as u64;
        let offset = (mply.leading_zeros() as usize) / 8;
        let new_postfix = &mply.to_be_bytes()[offset..offset + 3];
        let offset = offset - 3;
        let def = if offset > 0 { MAX_ZEROS } else { 0 };
        Difficulty(u32::from_le_bytes([
            new_postfix[2],
            new_postfix[1],
            new_postfix[0],
            cmp::min(
                (self.zeros() as u8)
                    .checked_add(offset as u8)
                    .unwrap_or(def),
                MAX_ZEROS,
            ),
        ]))
    }
}

impl PartialOrd for Difficulty {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Difficulty {
    fn cmp(&self, other: &Self) -> Ordering {
        let o1: PowOutput = (*self).into();
        let o2: PowOutput = (*other).into();

        for (a, b) in o1.0.iter().zip(o2.0.iter()) {
            if a > b {
                return Ordering::Greater;
            }
            if a < b {
                return Ordering::Less;
            }
        }

        Ordering::Equal
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct PowOutput([u8; 32]);

impl PowOutput {
    #[must_use]
    pub fn new(out: [u8; 32]) -> Self {
        Self(out)
    }
}

impl From<Difficulty> for PowOutput {
    fn from(d: Difficulty) -> Self {
        let mut output = [0u8; 32];
        let zeros = d.zeros();
        let postfix = d.postfix();
        output[zeros..zeros + 3].copy_from_slice(&postfix.to_be_bytes()[1..4]);
        Self(output)
    }
}

impl AsRef<[u8]> for PowOutput {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl PowOutput {
    #[must_use]
    pub fn meets_difficulty(&self, d: Difficulty) -> bool {
        for (a, b) in self.0.iter().zip(PowOutput::from(d).0.iter()) {
            if a > b {
                return false;
            }
            if a < b {
                return true;
            }
        }
        true
    }

    #[must_use]
    pub fn leading_zeros(&self) -> u32 {
        let mut zeros = 0;
        for limb in &self.0 {
            let limb_zeros = limb.leading_zeros();
            zeros += limb_zeros;
            if limb_zeros != 8 {
                break;
            }
        }
        zeros
    }

    #[must_use]
    pub fn inner(&self) -> [u8; 32] {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_money_checks() {
        assert!(!money_check(-1));
        assert!(money_check(0));
        assert!(money_check(1));
    }

    #[test]
    fn it_maps_height_to_block_reward() {
        assert_eq!(map_height_to_block_reward(0), INITIAL_BLOCK_REWARD);
        assert_eq!(map_height_to_block_reward(10), INITIAL_BLOCK_REWARD);
        assert_eq!(
            map_height_to_block_reward(HALVING_INTERVAL - 1),
            INITIAL_BLOCK_REWARD
        );
        assert_eq!(
            map_height_to_block_reward(HALVING_INTERVAL),
            INITIAL_BLOCK_REWARD / 2
        );
        assert_eq!(
            map_height_to_block_reward(HALVING_INTERVAL * (MAX_HALVINGS + 1)),
            map_height_to_block_reward(HALVING_INTERVAL * MAX_HALVINGS)
        );
    }

    #[test]
    fn it_maps_sector_id_to_chain_ids() {
        let sectors = (256 / SHARDS_PER_SECTOR) as u8;
        assert_eq!(map_sector_id_to_chain_ids(sectors), None);
        assert_eq!(map_sector_id_to_chain_ids(sectors + 1), None);
        assert!(map_sector_id_to_chain_ids(sectors - 1).is_some());
        assert_eq!(
            map_sector_id_to_chain_ids(0),
            Some(RangeInclusive::new(0, SHARDS_PER_SECTOR as u8 - 1))
        );
    }
}

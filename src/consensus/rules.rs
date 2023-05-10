// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use static_assertions::*;
use std::cmp;
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

/// Initial block reward, per shard. The miner reward is equal to INITIAL_BLOCK_REWARD * SHARDS_PER_SECTOR
pub const INITIAL_BLOCK_REWARD: Money = COIN; // 1 XPU

/// Amount of coins mined in the genesis block
pub const PRE_MINED_COINS: Money = COIN * 227_994_000;

/// Reward is halved after `n` blocks
pub const HALVING_INTERVAL: u64 = 4_200_000;

/// Only `n` halvings will happen, after which the block reward will remain constant
pub const MAX_HALVINGS: u64 = 20;

/// Max blocktime in regards to consensus calculations
pub const MAX_BLOCK_TIME: i64 = 60;

/// Coinbase outputs cannot be spent in the same epoch they are created in. These are not Green PoW epochs.
///
/// All transactions are considered final after the end of a coinbase epoch.
///
/// All unspent outputs we don't care about are pruned after COINBASE_EPOCH_LEN blocks past the current height
pub const COINBASE_EPOCH_LEN: u64 = 32;

/// RandomX key prefix
pub const RANDOMX_KEY_PREFIX: &str = "purplecoinrandomxhasher";

/// RandomX keys change every n blocks, regardless of PoW algorithm used
pub const RANDOMX_KEY_CHANGE_INTERVAL: u64 = 2048;

/// How long to spend mining for additional runnerups after receiving a runnerup block
pub const FIRST_ROUND_ADDITIONAL_TIME: i64 = 3;

/// Time in seconds to wait for a second round miner to find a block before
/// judging it as a timeout. After the timeout, all miners become eligible to
/// mine in the second round
pub const SECOND_ROUND_TIMEOUT: i64 = 90;

/// Minimum RandomX difficulty
pub const MIN_DIFF_RANDOMX: u32 = 0x010fffff;

/// Minimum Random hash PoW difficulty
pub const MIN_DIFF_RANDOM_HASH: u32 = 0x020fffff;

/// False positive rate for block header bloom filter
pub const BLOCK_HEADER_BLOOM_FP_RATE: f64 = 0.005;

/// Number of accumulators per shard
pub const ACCUMULATOR_MULTIPLIER: usize = 24;

/// Number of shards per sector
pub const SHARDS_PER_SECTOR: usize = 16;

/// Number of sectors
pub const SECTORS: usize = 256 / SHARDS_PER_SECTOR;

/// Money check
pub fn money_check(amount: Money) -> bool {
    amount >= 0
}

/// Get block reward at height
pub fn map_height_to_block_reward(height: u64) -> Money {
    let h = cmp::min(
        height as Money / HALVING_INTERVAL as Money,
        MAX_HALVINGS as Money,
    );
    INITIAL_BLOCK_REWARD >> h
}

/// Get RandomX key at height
pub fn map_height_to_randomx_key(height: u64) -> String {
    format!("{}", height / RANDOMX_KEY_CHANGE_INTERVAL)
}

/// Calculate new bits based on blocktime and old bits
pub fn calc_difficulty(bits: u32, blocktime: u64) -> u32 {
    let mut diff = rust_randomx::Difficulty::new(bits);
    let diff_change = (BLOCK_TIME_SECONDS as f32 / blocktime as f32).clamp(0.5f32, 2f32);
    diff.scale(diff_change).to_u32()
}

/// Map sector id to a range of chain ids
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
const_assert!(COINBASE_EPOCH_LEN >= 20);
const_assert!(COINBASE_EPOCH_LEN <= 100);
const_assert!(MAX_BYTES_PER_BLOCK >= 380_000);
const_assert!(MAX_BYTES_PER_BLOCK <= 750_000);
const_assert!(BLOCK_HEADER_BLOOM_FP_RATE >= 0.001);
const_assert!(BLOCK_HEADER_BLOOM_FP_RATE <= 0.1);
const_assert!(SHARDS_PER_SECTOR > 1);
const_assert!(256 % SHARDS_PER_SECTOR == 0);
const_assert!(ACCUMULATOR_MULTIPLIER > 0);
const_assert_eq!(HALVING_INTERVAL % 4, 0);
const_assert_eq!(RANDOMX_KEY_CHANGE_INTERVAL % 4, 0);
const_assert_eq!(SECOND_ROUND_TIMEOUT, BLOCK_TIME_SECONDS as i64 * 3);
const_assert_eq!(BLOCK_TIMESTAMP_MAX, BLOCK_TIME_SECONDS * 2);
const_assert_eq!(BLOCK_TIMESTAMP_MIN, BLOCK_TIME_SECONDS * 2);

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
    fn it_maps_height_to_randomx_key() {
        assert_eq!(map_height_to_randomx_key(0), "0");
        assert_eq!(
            map_height_to_randomx_key(RANDOMX_KEY_CHANGE_INTERVAL - 1),
            "0"
        );
        assert_eq!(map_height_to_randomx_key(RANDOMX_KEY_CHANGE_INTERVAL), "1");
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

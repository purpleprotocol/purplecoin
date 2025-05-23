// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::ChainConfig;
use crate::consensus::{
    calc_difficulty, map_height_to_block_reward, map_height_to_chain_id_for_reward,
    map_sector_id_to_chain_ids, Difficulty, Money, ACCUMULATOR_MULTIPLIER,
    BLOCK_HEADER_BLOOM_FP_RATE, COIN, MIN_DIFF_GR, MIN_DIFF_RANDOM_HASH, SECOND_ROUND_TIMEOUT,
    SECTORS, SHARDS_PER_SECTOR,
};
use crate::miner::{HashAlgorithm, PowAlgorithm};
use crate::primitives::{
    hash_arb_bytes_gr, Address, AggregatedSignature, BloomFilterHash256, Hash256, Hash256Algo,
    Input, InputFlags, Output, PublicKey, Transaction, TxVerifyErr,
};
use crate::settings::SETTINGS;
use crate::vm::internal::VmTerm;
use crate::vm::{
    ExecutionResult, Script, SigVerificationErr, VerificationStack, VmFlags, VmResult,
};
use accumulator::group::{Codec, Rsa2048};
use accumulator::{Accumulator, ProofOfCorrectness, Witness};
use arrayvec::ArrayVec;
use bincode::{Decode, Encode};
use bloomfilter::Bloom;
use chrono::prelude::*;
use itertools::izip;
use merkletree::merkle::MerkleTree;
use merkletree::store::VecStore;
use rand::prelude::*;
use rust_decimal::Decimal;
use rust_decimal_macros::dec;
use schnorrkel::signing_context;
use schnorrkel::vrf::{VRFInOut, VRFPreOut, VRFProof};
use serde::{Deserialize, Serialize};
use std::cmp;
use std::collections::HashMap;
use std::io::{self, prelude::*, BufReader, Cursor};
use triomphe::Arc;

pub type OutWitnessVec = Vec<(Output, Witness<Rsa2048, Output>)>;

#[cfg(host_family = "windows")]
macro_rules! psep {
    () => {
        r"\"
    };
}

#[cfg(not(host_family = "windows"))]
macro_rules! psep {
    () => {
        r"/"
    };
}

macro_rules! addresses_file_mainnet {
    () => {
        concat!(
            "genesisbalances.mainnet.",
            "sha256_a3dad0bed27f5d2fd8f5e278ff7d46997ffc5df0d43c351b416c6931c3136f34",
            ".",
            "blake3_913b1c3d0e4d2de1c77f6a80907a7d80321486548311c798f7dd3b885ca82036",
            ".txt"
        )
    };
}

macro_rules! addresses_file_testnet {
    () => {
        concat!(
            "genesisbalances.testnet.",
            "sha256_294e7f0ba5654eedd09cb02d8fe272a11549425f58e4cca3967597173fa051d5",
            ".",
            "blake3_d0beb318430812f90291a65355403c50dcc08152e07c48e6e92f53d9f8d70cfa",
            ".txt"
        )
    };
}

/// Sip keys are constructed by hashing the prev hash with keyed blake3
macro_rules! bloom_hash_key {
    () => {
        "purplecoin.bloom.{}"
    };
}

#[must_use]
pub fn pub_addresses_file_mainnet() -> &'static str {
    addresses_file_mainnet!()
}

#[must_use]
pub fn pub_addresses_file_testnet() -> &'static str {
    addresses_file_testnet!()
}

pub(crate) use addresses_file_mainnet;
pub(crate) use addresses_file_testnet;
pub(crate) use psep;

pub const ADDRESSES_RAW_MAINNET: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    psep!(),
    "data",
    psep!(),
    addresses_file_mainnet!()
));
pub const ADDRESSES_RAW_TESTNET: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    psep!(),
    "data",
    psep!(),
    addresses_file_testnet!()
));

#[derive(PartialEq, Eq, Debug, Clone, Serialize, Deserialize)]
/// Header for the `PoW` chain, which acts as the source of truth for shard sectors.
///
/// A shard sector is composed of different shards, which can be processed independently as
/// long as the corresponding `PoW` chain responsible for the sector is also processed.
///
/// The `PoW` chain does not contain any transaction body, but rather the root hash of batches
/// of blocks being appended to shard sectors.
pub struct PowBlockHeader {
    /// Block version
    pub version: u16,

    /// Pow block shard sector id
    pub sector_id: u8,

    /// Block height
    pub height: u64,

    /// Previous block hash
    pub prev_hash: Hash256,

    /// Block root
    pub block_root: Hash256,

    /// Header MMR root of the parent block
    pub prev_root: Hash256,

    /// Proof of Work solution
    pub nonce: u32,

    /// Bits
    pub bits: [u32; 14],

    /// Blocktime mean
    pub bt_mean: [u8; 14],

    /// Difficulty heights
    pub diff_heights: [u8; 14],

    /// Block timestamp
    pub timestamp: i64,

    /// Optional:
    /// If `block_height % 4 == 1 | 3`, this is the list of runnerup block hashes.
    /// This is null if `block_height % 4 == 0 | 2`
    ///
    /// If this block has been mined after the second round timeout
    /// this is equal to a zero hash.
    pub runnerup_hashes: Option<[Hash256; SECTORS - 1]>,

    /// Optional:
    /// If `block_height % 4 == 1 | 3`, this is the prev hash of the runnerup blocks.
    /// This is null if `block_height % 4 == 0 | 2`.
    pub runnerups_prev_hash: Option<Hash256>,

    /// Public key used to produce the VRF
    pub vrf_pkey_bytes: [u8; 32],

    /// VRF output.
    pub vrf_out: [u8; 32],

    /// VRF proof first 32 bytes
    pub vrf_proof_1: [u8; 32],

    /// VRF proof next 32 bytes
    pub vrf_proof_2: [u8; 32],

    /// An extra data field of max 14 bytes
    pub extra_data: Vec<u8>,

    /// Cached block hash
    pub hash: Option<Hash256>,
}

impl PowBlockHeader {
    /// Creates a new block for mining based on previous hash and block set.
    ///
    /// **Does not check the validity of the block set transactions**. Panics
    /// if previous header's hash is not computed.
    pub fn new(
        prev: &PowBlockHeader,
        prev_root: Hash256,
        runnerups: Option<[&PowBlockHeader; SECTORS - 1]>,
        blocks: Vec<BlockHeader>,
        vrf_pkey_bytes: [u8; 32],
        extra_data: Vec<u8>,
        key: &str,
    ) -> Result<Self, BlockVerifyErr> {
        assert!(
            extra_data.len() <= 14,
            "extra data field too large expected max 14 bytes"
        );
        let mt: MerkleTree<Hash256, Hash256Algo, VecStore<Hash256>> =
            MerkleTree::from_data::<Hash256, _>(blocks.iter().map(|b| b.hash().unwrap()).copied())
                .unwrap();
        let block_root = mt.root();
        let timestamp = Utc::now().timestamp();
        let runnerup_hashes = if let Some(runnerups) = runnerups {
            let mut out = [Hash256::zero(); SECTORS - 1];
            let b: Vec<Hash256> = runnerups.iter().map(|r| *r.hash().unwrap()).collect();
            out.copy_from_slice(b.as_slice());
            Some(out)
        } else {
            match prev.round() {
                1 => {
                    let time = prev.timestamp + SECOND_ROUND_TIMEOUT;

                    if timestamp < time {
                        return Err(BlockVerifyErr::InvalidRunnerupTimestamp);
                    }

                    Some([Hash256::zero(); SECTORS - 1])
                }

                2 => None,

                _ => unreachable!(),
            }
        };
        let runnerups_prev_hash = if let Some(runnerups) = runnerups {
            debug_assert_eq!(runnerups[0].prev_hash, prev.prev_hash);
            Some(runnerups[0].prev_hash)
        } else {
            match prev.round() {
                1 => {
                    let time = prev.timestamp + SECOND_ROUND_TIMEOUT;

                    if timestamp < time {
                        return Err(BlockVerifyErr::InvalidRunnerupTimestamp);
                    }

                    Some(prev.prev_hash)
                }

                2 => None,

                _ => unreachable!(),
            }
        };

        let shards_per_sector_minus_one = SHARDS_PER_SECTOR as u8 - 1;

        let mut block = Self {
            version: prev.version,
            sector_id: prev.sector_id,
            height: prev.height + 1,
            prev_hash: *prev.hash().unwrap(),
            nonce: 0,
            block_root,
            prev_root,
            bits: prev.bits,
            bt_mean: prev.bt_mean,
            diff_heights: prev.diff_heights,
            extra_data,
            runnerup_hashes,
            runnerups_prev_hash,
            timestamp,
            vrf_pkey_bytes,
            vrf_out: [0; 32], // Set these as null before the block is being mined
            vrf_proof_1: [0; 32], // Set these as null before the block is being mined
            vrf_proof_2: [0; 32], // Set these as null before the block is being mined
            hash: None,
        };

        debug_assert!(block.timestamp > prev.timestamp);
        let algo = block.map_height_to_algo();
        let (diff_idx, bt) = if block.runnerup_hashes.is_none() {
            (algo.diff_idx_r1(), block.timestamp - prev.timestamp)
        } else if block
            .runnerup_hashes
            .as_ref()
            .unwrap()
            .iter()
            .all(|h| h == &Hash256::zero())
        {
            (
                algo.diff_idx_r1(),
                block.timestamp - (prev.timestamp + SECOND_ROUND_TIMEOUT),
            )
        } else {
            (algo.diff_idx_r2(), block.timestamp - prev.timestamp)
        };

        block.calc_new_bits(prev, diff_idx, bt);
        Ok(block)
    }

    /// Creates the genesis block for the given chain config
    #[must_use]
    pub fn genesis(sector_id: u8, config: &ChainConfig) -> Self {
        let nonce = 0;
        let key = config.get_sector_key(sector_id);
        let mut bits = [MIN_DIFF_RANDOM_HASH; 14];
        bits[0] = MIN_DIFF_GR;
        bits[1] = MIN_DIFF_GR;
        let bt_mean = [30; 14];
        let diff_heights = [0; 14];
        let chain_ids = map_sector_id_to_chain_ids(sector_id).unwrap();

        let mt: MerkleTree<Hash256, Hash256Algo, VecStore<Hash256>> =
            MerkleTree::from_data::<Hash256, Vec<Hash256>>(
                chain_ids
                    .into_iter()
                    .map(|chain_id| {
                        *BlockHeader::genesis_cached(chain_id, config)
                            .hash()
                            .unwrap()
                    })
                    .collect(),
            )
            .unwrap();
        let block_root = mt.root();
        let prev_hash = Hash256::hash_from_slice("The Guardian 22/08/2022 UK inflation will hit 18% in early 2023, says leading bank Citi\n\nABSE\n\nV IX MMXXII", key);

        let mut genesis = Self {
            version: 0,
            sector_id,
            prev_hash,
            block_root,
            nonce,
            height: 1, // Start at height 1 such that the genesis block is the second round of the first green pow epoch
            bits,
            bt_mean,
            diff_heights,
            timestamp: Utc
                .with_ymd_and_hms(2022, 8, 22, 22, 30, 47)
                .unwrap()
                .timestamp(),
            prev_root: Hash256::zero(),
            runnerup_hashes: Some([Hash256::zero(); SECTORS - 1]),
            runnerups_prev_hash: Some(Hash256::zero()),
            vrf_pkey_bytes: [0; 32], // These are null in the genesis block
            vrf_out: [0; 32],        // These are null in the genesis block
            vrf_proof_1: [0; 32],    // These are null in the genesis block
            vrf_proof_2: [0; 32],    // These are null in the genesis block
            extra_data: vec![],
            hash: None,
        };

        genesis.compute_hash();
        genesis
    }

    /// Increment nonce. Returns `None` if the nonce overflows.
    pub fn increment_nonce(&mut self) -> Option<u32> {
        self.nonce = self.nonce.checked_add(1)?;
        Some(self.nonce)
    }

    /// Reset nonce to zero
    pub fn zero_nonce(&mut self) {
        self.nonce = 0;
    }

    /// 2 type of algorithms will be used in sequence, one that
    /// is efficient when CPU mining, and one when ASIC mining.
    ///
    /// ASICs secure against hash marketplace attacks while a
    /// CPU optimised algorithm protects against double-spend
    /// attacks by powerful adversaries.
    #[must_use]
    pub fn map_height_to_algo(&self) -> PowAlgorithm {
        match self.height % 4 {
            0 | 1 => PowAlgorithm::GR,
            2 => PowAlgorithm::RandomHash(HashAlgorithm::deterministic_random(
                self.prev_hash.as_bytes(),
            )),
            3 => PowAlgorithm::RandomHash(HashAlgorithm::deterministic_random(
                self.runnerups_prev_hash.as_ref().unwrap().as_bytes(),
            )),
            _ => unreachable!(),
        }
    }

    /// Returns the block round.
    ///
    /// * Returns `1` if `self.height % 4 == 0 | 2`
    /// * Returns `2` if `self.height % 4 == 1 | 3`
    #[must_use]
    pub fn round(&self) -> u8 {
        match self.height % 4 {
            0 | 2 => 1,
            1 | 3 => 2,
            _ => unreachable!(),
        }
    }

    /// Returns the block's difficulty index
    #[must_use]
    pub fn diff_idx(&self) -> usize {
        let algo = self.map_height_to_algo();

        match self.round() {
            1 => algo.diff_idx_r1(),
            2 => algo.diff_idx_r2(),
            _ => unreachable!(),
        }
    }

    /// Returns block nonce
    #[must_use]
    pub fn nonce(&self) -> u32 {
        self.nonce
    }

    /// Returns bits
    #[must_use]
    pub fn bits(&self, idx: usize) -> u32 {
        self.bits[idx]
    }

    /// Validate header against the previous header. Used for initial header validation.
    pub fn validate(&self, prev: &PowBlockHeader) -> Result<(), BlockVerifyErr> {
        if self.height != prev.height + 1 || prev.height == 0 {
            return Err(BlockVerifyErr::InvalidHeight);
        }

        if &self.prev_hash != prev.hash().unwrap() {
            return Err(BlockVerifyErr::InvalidPrevHash);
        }

        if self.timestamp < prev.timestamp {
            return Err(BlockVerifyErr::InvalidTimestamp);
        }

        if self.sector_id != prev.sector_id {
            return Err(BlockVerifyErr::InvalidSectorID);
        }

        match self.round() {
            1 => {
                if self.runnerup_hashes.is_some() {
                    return Err(BlockVerifyErr::InvalidRunnerupHash);
                }

                if self.runnerups_prev_hash.is_some() {
                    return Err(BlockVerifyErr::InvalidRunnerupPrevHash);
                }

                let algo = self.map_height_to_algo();
                let diff_idx = algo.diff_idx_r1();

                self.validate_diff_fields(prev, diff_idx, self.timestamp - prev.timestamp)?;
            }

            2 => {
                if self.runnerup_hashes.is_none() {
                    return Err(BlockVerifyErr::InvalidRunnerupHash);
                }

                if self.runnerups_prev_hash.is_none() {
                    return Err(BlockVerifyErr::InvalidRunnerupPrevHash);
                }

                if self.runnerups_prev_hash.as_ref().unwrap() != &prev.prev_hash {
                    return Err(BlockVerifyErr::InvalidRunnerupPrevHash);
                }

                // Check and validate blocks after timeout
                if self
                    .runnerup_hashes
                    .as_ref()
                    .unwrap()
                    .iter()
                    .all(|h| h == &Hash256::zero())
                {
                    let time = prev.timestamp + SECOND_ROUND_TIMEOUT;

                    if self.timestamp < time {
                        return Err(BlockVerifyErr::InvalidTimestamp);
                    }

                    let algo = self.map_height_to_algo();
                    let diff_idx = algo.diff_idx_r1();

                    self.validate_diff_fields(prev, diff_idx, self.timestamp - time)?;
                } else {
                    let algo = self.map_height_to_algo();
                    let diff_idx = algo.diff_idx_r2();

                    self.validate_diff_fields(prev, diff_idx, self.timestamp - prev.timestamp)?;
                }
            }

            _ => unreachable!(),
        }

        self.validate_pow()?;
        self.validate_vrf_fields()?;

        Ok(())
    }

    /// Validate difficulties and `PoW`
    ///
    /// In test mode `PoWs` have to be checked separately
    fn validate_diff_fields(
        &self,
        prev: &PowBlockHeader,
        diff_idx: usize,
        blocktime: i64,
    ) -> Result<(), BlockVerifyErr> {
        let bits = self.bits[diff_idx];
        let prev_bits = prev.bits[diff_idx];
        let mean = self.bt_mean[diff_idx];
        let prev_mean = prev.bt_mean[diff_idx];
        let diff_height = self.diff_heights[diff_idx];
        let prev_diff_height = prev.diff_heights[diff_idx];
        let blocktime = cmp::min(blocktime, crate::consensus::MAX_BLOCK_TIME);

        match diff_height {
            0 => {
                if prev_diff_height != 5 {
                    return Err(BlockVerifyErr::InvalidDiffHeight);
                }

                if i64::from(mean) != blocktime {
                    return Err(BlockVerifyErr::InvalidDiffMean);
                }

                let oracle_bits = calc_difficulty(prev_bits, u64::from(prev_mean));

                let min_diff = match diff_idx {
                    0 | 12 => Difficulty::new(MIN_DIFF_GR),
                    _ => Difficulty::new(MIN_DIFF_RANDOM_HASH),
                };

                // Enforce minimum network difficulty
                let oracle_bits = cmp::min(Difficulty::new(oracle_bits), min_diff);

                if oracle_bits.to_u32() != bits {
                    return Err(BlockVerifyErr::InvalidDiff);
                }
            }

            1..=5 => {
                if diff_height != prev_diff_height + 1 {
                    return Err(BlockVerifyErr::InvalidDiffHeight);
                }

                if bits != prev_bits {
                    return Err(BlockVerifyErr::InvalidDiff);
                }

                let oracle_mean =
                    Decimal::from(prev_mean) * dec!(5.0) + Decimal::from(blocktime) / dec!(6.0);
                let oracle_mean: u8 = oracle_mean
                    .floor()
                    .clamp(dec!(0), crate::consensus::MAX_BLOCK_TIME.into())
                    .try_into()
                    .unwrap();

                if oracle_mean != mean {
                    return Err(BlockVerifyErr::InvalidDiffMean);
                }
            }

            _ => {
                return Err(BlockVerifyErr::InvalidDiffHeight);
            }
        }

        // Validate other idxs
        for i in 0..24 {
            if i == diff_idx {
                continue;
            }

            let bits = self.bits[i];
            let prev_bits = prev.bits[i];
            let mean = self.bt_mean[i];
            let prev_mean = prev.bt_mean[i];
            let diff_height = self.diff_heights[i];
            let prev_diff_height = prev.diff_heights[i];

            if bits != prev_bits {
                return Err(BlockVerifyErr::InvalidDiff);
            }

            if mean != prev_mean {
                return Err(BlockVerifyErr::InvalidDiffMean);
            }

            if diff_height != prev_diff_height {
                return Err(BlockVerifyErr::InvalidDiffHeight);
            }
        }

        Ok(())
    }

    /// Validates proof of work solution. Panics if hash is not computed
    pub fn validate_pow(&self) -> Result<(), BlockVerifyErr> {
        let bits = self.bits[self.diff_idx()];

        if !self.hash().unwrap().meets_difficulty(bits) {
            return Err(BlockVerifyErr::InvalidPoW);
        }

        Ok(())
    }

    /// Calculate new bits, `bt_mean` and `diff_heights` values based on the new timestamp
    fn calc_new_bits(&mut self, prev: &Self, diff_idx: usize, bt: i64) {
        debug_assert!(bt >= 0);
        let blocktime = cmp::min(bt, crate::consensus::MAX_BLOCK_TIME) as u8;
        let bits = &mut self.bits[diff_idx];
        let prev_bits = prev.bits[diff_idx];
        let mean = &mut self.bt_mean[diff_idx];
        let prev_mean = prev.bt_mean[diff_idx];
        let diff_height = &mut self.diff_heights[diff_idx];
        let prev_diff_height = prev.diff_heights[diff_idx];
        debug_assert!(prev_diff_height <= 5);

        match prev_diff_height {
            5 => {
                let min_diff = match diff_idx {
                    0 | 12 => Difficulty::new(MIN_DIFF_GR),
                    _ => Difficulty::new(MIN_DIFF_RANDOM_HASH),
                };
                let new_bits = calc_difficulty(prev_bits, u64::from(prev_mean));
                debug_assert!(Difficulty::new(prev_bits) <= min_diff);

                *bits = cmp::min(Difficulty::new(new_bits), min_diff).to_u32();
                *diff_height = 0;
                *mean = blocktime;
            }

            _ => {
                *diff_height += 1;
                *mean = (Decimal::from(prev_mean) * dec!(5.0)
                    + Decimal::from(blocktime) / dec!(6.0))
                .floor()
                .clamp(dec!(0), crate::consensus::MAX_BLOCK_TIME.into())
                .try_into()
                .unwrap();
            }
        }
    }

    /// Serialize to bytes
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        crate::codec::encode_to_vec(self).unwrap()
    }

    /// Returns hash. Must be computed first
    #[must_use]
    pub fn hash(&self) -> Option<&Hash256> {
        self.hash.as_ref()
    }

    /// Validate vrf fields. Also returns the `VRFInOut` to be used for
    /// generation of RNGs.
    pub fn validate_vrf_fields(&self) -> Result<VRFInOut, BlockVerifyErr> {
        let pub_key = PublicKey::from_bytes(&self.vrf_pkey_bytes)
            .map_err(|_| BlockVerifyErr::InvalidVrfFields)?;
        let vrf_out = VRFPreOut(self.vrf_out);
        let mut vrf_proof_buf = [0; 64];
        let mut i = 0;
        while i < 64 {
            if i < 32 {
                vrf_proof_buf[i] = self.vrf_proof_1[i];
            } else {
                vrf_proof_buf[i] = self.vrf_proof_2[i - 32];
            }
            i += 1;
        }
        let vrf_proof =
            VRFProof::from_bytes(&vrf_proof_buf).map_err(|_| BlockVerifyErr::InvalidVrfFields)?;
        let ctx = signing_context(&self.prev_hash.0);
        let transcript = ctx.bytes(&self.hash().unwrap().0);

        let r = pub_key
            .0
            .vrf_verify(transcript, &vrf_out, &vrf_proof)
            .map_err(|_| BlockVerifyErr::InvalidVrfFields)?;

        Ok(r.0)
    }

    /// Compute hash
    pub fn compute_hash(&mut self) {
        // Backup vrf out and proof fields
        let vrf_out_bak = self.vrf_out;
        let vrf_proof_1_bak = self.vrf_proof_1;
        let vrf_proof_2_bak = self.vrf_proof_2;
        // Set vrf out and proof to null for hash computation
        self.vrf_out = [0; 32];
        self.vrf_proof_1 = [0; 32];
        self.vrf_proof_2 = [0; 32];
        // Compute hash
        let encoded = crate::codec::encode_to_vec(self).unwrap();
        let hash = match self.map_height_to_algo() {
            PowAlgorithm::RandomHash(algo) => algo.hash(&encoded),
            PowAlgorithm::GR => Hash256(hash_arb_bytes_gr(&encoded, self.prev_hash.0)),
        };
        // Set back the vrf fields from backups
        self.vrf_out = vrf_out_bak;
        self.vrf_proof_1 = vrf_proof_1_bak;
        self.vrf_proof_2 = vrf_proof_2_bak;
        // Set the hash
        self.hash = Some(hash);
    }
}

#[derive(Eq, Debug, Clone)]
/// Shard block header
pub struct BlockHeader {
    /// Chain id
    pub chain_id: u8,

    /// Block height
    pub height: u64,

    /// Previous block hash
    pub prev_hash: Hash256,

    /// Transactions root
    pub tx_root: Hash256,

    /// Constant sized state accumulator
    pub accumulators: ArrayVec<Accumulator<Rsa2048, Output>, ACCUMULATOR_MULTIPLIER>,

    /// Accumulator proof of correctness
    pub poc: ArrayVec<ProofOfCorrectness<Rsa2048, Output>, ACCUMULATOR_MULTIPLIER>,

    /// Bloom filter containing the following data from the block:
    ///
    /// * All transaction hashes
    /// * All output hashes
    /// * All output addresses
    /// * All script hashes
    /// * All script arguments
    /// * All script outputs
    /// * All colour hashes
    ///
    /// All of the above are first hashed to 256 bits using keyed blake3
    pub block_bloom: BloomFilterHash256,

    /// Cached block hash
    pub hash: Option<Hash256>,
}

impl PartialEq for BlockHeader {
    fn eq(&self, other: &Self) -> bool {
        self.chain_id == other.chain_id
            && self.height == other.height
            && self.tx_root == other.tx_root
            && self.accumulators == other.accumulators
            && self.poc == other.poc
            && self.block_bloom == other.block_bloom
    }
}

impl BlockHeader {
    /// Creates a new block for mining based on previous hash and tx set.
    ///
    /// Checks the validity of the tx set first. Panics if previous header's hash is not computed.
    pub fn new(
        prev_pow: &PowBlockHeader,
        prev: &BlockHeader,
        runnerup: Option<&BlockHeader>,
        data: &BlockData,
        key: &str,
        vrf_in_out: VRFInOut,
    ) -> Result<Self, BlockVerifyErr> {
        let (to_add, to_delete) = data.validate_txs(prev_pow, prev, key, vrf_in_out)?;
        let to_add: Vec<Output> = to_add.iter().map(|(o, _)| o.clone()).collect();

        Self::new_unsafe(
            prev,
            runnerup,
            data,
            to_add.as_slice(),
            to_delete.as_slice(),
            key,
        )
    }

    /// Creates a new block for mining based on previous header, tx set and output set.
    ///
    /// **Does not check the validity of the tx set.** Panics if previous header's hash is not computed.
    pub fn new_unsafe(
        prev: &BlockHeader,
        runnerup: Option<&BlockHeader>,
        data: &BlockData,
        to_add: &[Output],
        to_delete: &[(Output, Witness<Rsa2048, Output>)],
        key: &str,
    ) -> Result<Self, BlockVerifyErr> {
        let mut delete_buckets = vec![vec![]; ACCUMULATOR_MULTIPLIER];
        let mut add_buckets = vec![vec![]; ACCUMULATOR_MULTIPLIER];

        // Group outputs to delete in buckets based on the hashing index
        for (o, w) in to_delete {
            let i = o.acc_idx();
            delete_buckets[i].push((o.clone(), w.clone()));
        }

        // Group outputs to add in buckets based on the hashing index
        for o in to_add {
            let i = o.acc_idx();
            add_buckets[i].push(o.clone());
        }

        let mut accumulators = ArrayVec::new();
        let mut poc = ArrayVec::new();

        for (accumulator, to_delete, to_add) in
            izip!(&prev.accumulators, delete_buckets, add_buckets)
        {
            let (witness_deleted, proof_deleted) = accumulator
                .clone()
                .delete_with_proof(&to_delete)
                .map_err(|_| BlockVerifyErr::InvalidOuts)?;
            let (accumulator, proof_added) = witness_deleted.add_with_proof(&to_add);
            let poc0 = ProofOfCorrectness::new(proof_added, proof_deleted);
            accumulators.push(accumulator);
            poc.push(poc0);
        }

        let mut tx_hashes = vec![];
        let mut bloom_data = vec![];
        let iter = data.txs.iter().map(|tx| tx.hash().unwrap());
        for h in iter {
            tx_hashes.push(*h);
            bloom_data.push(*h);
        }

        let tx_root = match tx_hashes.len() {
            0 => Hash256::zero(),

            len if len % 2 == 1 => {
                tx_hashes.push(tx_hashes[tx_hashes.len() - 1]);
                let mt: MerkleTree<Hash256, Hash256Algo, VecStore<Hash256>> =
                    MerkleTree::from_data::<Hash256, Vec<Hash256>>(tx_hashes).unwrap();
                mt.root()
            }

            _ => {
                let mt: MerkleTree<Hash256, Hash256Algo, VecStore<Hash256>> =
                    MerkleTree::from_data::<Hash256, Vec<Hash256>>(tx_hashes).unwrap();
                mt.root()
            }
        };

        // Write output addresses, colours, and outputs, if present
        bloom_data.extend(to_add.iter().flat_map(|o| {
            let mut buf = vec![];
            buf.push(*o.hash().unwrap());
            if let Some(address) = &o.address {
                buf.push(Hash256::hash_from_slice(address.as_bytes(), key));
            }
            if let Some(address) = &o.coloured_address {
                buf.push(Hash256::hash_from_slice(address.address, key));
                buf.push(Hash256::hash_from_slice(address.colour_hash, key));
            }
            buf.extend(
                o.script_outs
                    .iter()
                    .map(|t| Hash256::hash_from_slice(t.to_bytes(), key)),
            );
            buf.push(Hash256::hash_from_slice(o.script_hash.0, key));
            buf
        }));

        let bloom_seed_hash = Hash256::hash_from_slice(
            prev.hash().unwrap().0,
            &format!(bloom_hash_key!(), prev.chain_id),
        );
        let bloom_seed = &bloom_seed_hash.0;
        let mut block_bloom =
            BloomFilterHash256::new(bloom_data.len(), BLOCK_HEADER_BLOOM_FP_RATE, bloom_seed);

        for d in &bloom_data {
            block_bloom.inner.set(d);
        }

        Ok(Self {
            chain_id: prev.chain_id,
            height: prev.height + 1,
            prev_hash: *prev.hash().unwrap(),
            tx_root,
            accumulators,
            poc,
            block_bloom,
            hash: None,
        })
    }

    fn read_genesis_inputs(chain_id: u8, config: &ChainConfig) -> Vec<Input> {
        let raw = match SETTINGS.node.network_name.as_str() {
            "mainnet" => ADDRESSES_RAW_MAINNET,

            "testnet" | "devnet" => ADDRESSES_RAW_TESTNET,

            other => {
                panic!("Invalid network: {other}")
            }
        };

        let cursor = Cursor::new(raw.as_bytes());
        let reader = BufReader::new(cursor);

        reader
            .lines()
            .map(|line| {
                let split: Vec<_> = line
                    .unwrap()
                    .split('=')
                    .map(|line| {
                        let mut line = line.to_owned();
                        line.retain(|c| !c.is_whitespace());
                        line
                    })
                    .collect();

                let addr = &split[0];
                let amount: Money = split[1].parse().unwrap();

                let address = Address::from_bech32(addr).unwrap();
                let key = config.get_chain_key(chain_id);
                let ss = Script::new_simple_spend();
                let sh = ss.to_script_hash(key);
                let amount = amount * COIN;
                let script_args = vec![
                    VmTerm::Signed128(amount / 256),
                    VmTerm::Hash160(address.0),
                    VmTerm::Hash160(sh.0),
                    VmTerm::Unsigned32(0),
                ];
                let mut input = Input {
                    input_flags: InputFlags::IsCoinbase,
                    script_args,
                    ..Default::default()
                };
                input.compute_hash(key);
                input
            })
            .collect()
    }

    /// Creates the genesis block for the given chain id and chain config
    #[must_use]
    pub fn genesis(chain_id: u8, config: &ChainConfig) -> BlockHeader {
        let inputs = Self::read_genesis_inputs(chain_id, config);
        let key = config.get_chain_key(chain_id);
        let mut out_stack = vec![];
        let mut outs_sum = 0;
        let mut coloured_ins_sums = HashMap::new();
        let mut coloured_outs_sums = HashMap::new();
        let mut ver_stack = VerificationStack::new();
        let mut idx_map = HashMap::new();
        let script = Script::new_coinbase();

        // Compute outputs
        for input in &inputs {
            let in_clone = input.clone();
            let result = script.execute(
                &input.script_args,
                &[],
                &mut out_stack,
                &mut outs_sum,
                &mut coloured_ins_sums,
                &mut coloured_outs_sums,
                &mut idx_map,
                &mut ver_stack,
                [0; 32],
                key,
                SETTINGS.node.network_name.as_str(),
                VmFlags {
                    is_coinbase: true,
                    ..VmFlags::default()
                },
            );

            assert_eq!(
                result,
                VmResult(Ok(ExecutionResult::Ok)),
                "Invalid inputs given to the genesis block"
            );
        }

        // Hash outs with jump_ch to determine accumulator index and then index them accordingly
        let mut acc = vec![];
        for _ in 0..ACCUMULATOR_MULTIPLIER {
            acc.push(vec![]);
        }
        let indexed_outs: Vec<_> = out_stack
            .iter()
            .map(|out| {
                let hash_bytes = &out.hash().unwrap().0[..8];
                let mut hash_bytes_buf = [0; 8];
                hash_bytes_buf.copy_from_slice(hash_bytes);
                let key = u64::from_le_bytes(hash_bytes_buf);
                let idx = jump_consistent_hash::hash(key, ACCUMULATOR_MULTIPLIER) as usize;
                (out.clone(), idx)
            })
            .fold(acc, |mut acc, (out, idx)| {
                acc[idx].push(out);
                acc
            });

        // Compute accumulators and proofs
        let accumulators_and_proofs: Vec<_> = indexed_outs
            .iter()
            .map(|outs| {
                let accumulator = Accumulator::<Rsa2048, Output>::empty();
                let (witness_deleted, proof_deleted) = accumulator.delete_with_proof(&[]).unwrap();
                let (accumulator, proof_added) = witness_deleted.add_with_proof(outs);
                let poc = ProofOfCorrectness::new(proof_added, proof_deleted);
                (accumulator, poc)
            })
            .collect();
        let mut accumulators = ArrayVec::new();
        let mut proofs = ArrayVec::new();

        for (acc, poc) in &accumulators_and_proofs {
            accumulators.push(acc.clone());
            proofs.push(poc.clone());
        }

        let mut tx = Transaction {
            chain_id,
            ins: inputs,
            hash: None,
        };
        tx.compute_hash(key);

        let mt: MerkleTree<Hash256, Hash256Algo, VecStore<Hash256>> =
            MerkleTree::from_data::<Hash256, Vec<Hash256>>(vec![
                *tx.hash().unwrap(),
                *tx.hash().unwrap(),
            ])
            .unwrap();

        let tx_root = mt.root();
        let prev_hash = Hash256::hash_from_slice("The Guardian 22/08/2022 UK inflation will hit 18% in early 2023, says leading bank Citi\n\nABSE\n\nV IX MMXXII", key);
        let bloom_seed_hash =
            Hash256::hash_from_slice(prev_hash.0, &format!(bloom_hash_key!(), chain_id));
        let bloom_seed = &bloom_seed_hash.0;

        let mut bloom_hashes = vec![*tx.hash().unwrap()];
        bloom_hashes.extend(out_stack.iter().map(|o| *o.hash().unwrap()));
        bloom_hashes.extend(
            out_stack
                .iter()
                .map(|o| Hash256::hash_from_slice(o.address.as_ref().unwrap().as_bytes(), key)),
        );

        let mut block_bloom = Bloom::new_for_fp_rate_with_seed(
            bloom_hashes.len(),
            crate::consensus::BLOCK_HEADER_BLOOM_FP_RATE,
            bloom_seed,
        );

        for h in &bloom_hashes {
            block_bloom.set(h);
        }

        let block_bloom = BloomFilterHash256 { inner: block_bloom };

        let mut genesis = Self {
            chain_id,
            prev_hash,
            tx_root,
            accumulators,
            poc: proofs,
            height: 1,
            block_bloom,
            hash: None,
        };

        genesis.compute_hash();
        genesis
    }

    /// Returns cached version of the genesis block if available. Computes it if it doesn't exist.
    #[must_use]
    pub fn genesis_cached(chain_id: u8, chain_config: &ChainConfig) -> Arc<BlockHeader> {
        crate::global::get_cached_genesis(chain_id, chain_config)
    }

    /// Serialize to bytes
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        crate::codec::encode_to_vec(self).unwrap()
    }

    /// Returns hash. Must be computed first
    #[must_use]
    pub fn hash(&self) -> Option<&Hash256> {
        self.hash.as_ref()
    }

    /// Returns the chain id of the block
    #[must_use]
    pub fn chain_id(&self) -> u8 {
        self.chain_id
    }

    /// Compute hash
    pub fn compute_hash(&mut self) {
        let encoded = crate::codec::encode_to_vec(self).unwrap();
        self.hash = Some(Hash256::hash_from_slice(encoded, "shardblockheaderhasher"));
    }

    /// Validate header against the previous header. Used for initial header validation.
    pub fn validate(&self, prev: &BlockHeader) -> Result<(), BlockVerifyErr> {
        if self.height != prev.height + 1 || prev.height == 0 {
            return Err(BlockVerifyErr::InvalidHeight);
        }

        if &self.prev_hash != prev.hash().unwrap() {
            return Err(BlockVerifyErr::InvalidPrevHash);
        }

        if self.chain_id != prev.chain_id {
            return Err(BlockVerifyErr::InvalidChainID);
        }

        Ok(())
    }
}

#[derive(PartialEq, Debug)]
/// Full pow block. Includes Pow header and sector blocks
pub struct PowBlock {
    pub header: PowBlockHeader,
    pub sector_blocks: PowBlockData,
}

impl PowBlock {
    pub fn validate_against_current(
        &self,
        tip: &PowBlockHeader,
        sector_tips: &[Option<BlockHeader>],
        key: &str,
        chain_config: &ChainConfig,
    ) -> Result<Vec<(Block, Vec<Output>)>, BlockVerifyErr> {
        unimplemented!()
    }
}

#[derive(PartialEq, Debug, Encode, Decode)]
/// Full block. Includes header and transactions
pub struct Block {
    pub header: BlockHeader,
    pub body: BlockData,
}

impl Block {
    /// Creates a new block for mining with the given transaction with a coinbase to address
    pub fn new(
        prev_pow: &PowBlockHeader,
        prev: &BlockHeader,
        runnerup: Option<&BlockHeader>,
        coinbase: &Address,
        mut txs: Vec<Transaction>,
        aggregated_signature: Option<AggregatedSignature>,
        key: &str,
        witnesses: &[Witness<Rsa2048, Output>],
        vrf_in_out: VRFInOut,
    ) -> Result<Self, BlockVerifyErr> {
        let extra_nonce: u32 = rand::thread_rng().gen();
        let ss = Script::new_simple_spend();
        let sh = ss.to_script_hash(key);
        let coinbase_height = prev.height + 1;
        let mut input = Input {
            input_flags: InputFlags::IsCoinbase,
            script_args: vec![
                VmTerm::Signed128(map_height_to_block_reward(coinbase_height)),
                VmTerm::Hash160(coinbase.0),
                VmTerm::Hash160(sh.0),
                VmTerm::Unsigned64(coinbase_height),
                VmTerm::Unsigned32(extra_nonce),
            ],
            ..Default::default()
        };
        input.compute_hash(key);

        let mut tx = Transaction {
            chain_id: prev.chain_id,
            ins: vec![input],
            hash: None,
        };
        tx.compute_hash(key);
        txs.push(tx);

        let body = BlockData::new(txs, aggregated_signature);

        Ok(Self {
            header: BlockHeader::new(prev_pow, prev, runnerup, &body, key, vrf_in_out)?,
            body,
        })
    }

    /// Run full header and body validations
    pub fn validate(
        &self,
        prev_pow: &PowBlockHeader,
        prev: &BlockHeader,
        key: &str,
        vrf_in_out: VRFInOut,
    ) -> Result<(OutWitnessVec, OutWitnessVec), BlockVerifyErr> {
        self.header.validate(prev)?;
        self.body
            .validate_against_current(&self.header, prev_pow, prev, key, vrf_in_out)
    }

    /// Run full body validations. Assumes initial header validations passed
    pub fn validate_against_current(
        &self,
        prev_pow: &PowBlockHeader,
        prev: &BlockHeader,
        key: &str,
        vrf_in_out: VRFInOut,
    ) -> Result<(OutWitnessVec, OutWitnessVec), BlockVerifyErr> {
        self.body
            .validate_against_current(&self.header, prev_pow, prev, key, vrf_in_out)
    }

    /// Validates only the body against the previous header
    pub fn validate_body(
        &self,
        prev_pow: &PowBlockHeader,
        prev: &BlockHeader,
        key: &str,
        vrf_in_out: VRFInOut,
    ) -> Result<(OutWitnessVec, OutWitnessVec), BlockVerifyErr> {
        self.body.validate_txs(prev_pow, prev, key, vrf_in_out)
    }
}

#[derive(PartialEq, Debug)]
/// Pow block body
pub struct PowBlockData {
    pub blocks: [Option<Arc<Block>>; SHARDS_PER_SECTOR],
}

#[derive(PartialEq, Debug, Encode, Decode, Default)]
/// Block body. Includes transactions, public keys and aggregated signature
pub struct BlockData {
    pub txs: Vec<Transaction>,
    pub aggregated_signature: Option<AggregatedSignature>,
}

impl BlockData {
    /// Creates new block data from txs, public keys and signature with a coinbase transaction to address
    ///
    /// **Does not check the validity of transactions, public keys or signature**
    #[must_use]
    pub fn new(
        mut txs: Vec<Transaction>,
        aggregated_signature: Option<AggregatedSignature>,
    ) -> Self {
        Self {
            txs,
            aggregated_signature,
        }
    }

    /// Validates the transactions in the body against the previous header
    pub fn validate_txs(
        &self,
        prev_pow: &PowBlockHeader,
        prev: &BlockHeader,
        key: &str,
        vrf_in_out: VRFInOut,
    ) -> Result<(OutWitnessVec, OutWitnessVec), BlockVerifyErr> {
        if self.txs.is_empty() {
            return Ok((vec![], vec![]));
        }

        let block_height = prev.height + 1;
        let block_reward = map_height_to_block_reward(block_height);
        let mut idx_map = HashMap::new();
        let mut coinbase: Option<Input> = None;
        let mut coinbase_count = 0;
        let mut coloured_coinbase_count = 0;
        let mut to_add: Vec<Output> = vec![];
        let mut to_delete: OutWitnessVec = vec![];
        let mut ver_stack = VerificationStack::new();
        let mut public_keys = vec![];
        let mut transcripts = vec![];
        let mut ctx = schnorrkel::signing_context(key.as_bytes());
        let master_seed_bytes: [u8; 32] = vrf_in_out.make_bytes(key.as_bytes());

        for (i, tx) in self.txs.iter().enumerate() {
            let nonce = (i as u64).to_le_bytes();
            let tx_seed_bytes: &[u8] = &[master_seed_bytes.as_slice(), nonce.as_slice()].concat();
            tx.verify_single(
                key,
                block_height,
                prev.chain_id,
                prev_pow.timestamp,
                *prev.hash().unwrap(),
                map_height_to_block_reward(block_height),
                map_height_to_chain_id_for_reward(block_height, prev_pow.sector_id)
                    == prev.chain_id,
                &mut to_add,
                &mut to_delete,
                &mut ver_stack,
                &mut idx_map,
                tx_seed_bytes,
                |_| Ok(()), // TODO: Validate coloured coinbases for idempotency here
            )?;
            for input in &tx.ins {
                // Push public key and input binary format if we have a spending pkey
                if let Some(public_key) = &input.spending_pkey {
                    public_keys.push(public_key.0);
                    transcripts.push(ctx.bytes(&input.to_bytes()));
                }
            }
        }

        // Verify all signatures
        if let Some(signature) = &self.aggregated_signature {
            if transcripts.is_empty() {
                return Err(BlockVerifyErr::InvalidSignature);
            }

            signature
                .0
                .verify(transcripts, public_keys.as_slice(), true)
                .map_err(|_| BlockVerifyErr::SigVerificationErr)?;
        }
        crate::vm::verify_batch(&ver_stack)?;

        let to_add = to_add
            .iter()
            .map(|o| {
                let witness = Witness(Accumulator::<Rsa2048, Output>::empty());
                (
                    o.clone(),
                    witness
                        .compute_subset_witness(&to_add, &[o.clone()])
                        .unwrap(),
                )
            })
            .collect();

        Ok((to_add, to_delete))
    }

    /// Validates the transactions in the body against the previous header and
    /// then validates the current header for validity against the tx set.
    pub fn validate_against_current(
        &self,
        current: &BlockHeader,
        prev_pow: &PowBlockHeader,
        prev: &BlockHeader,
        key: &str,
        vrf_in_out: VRFInOut,
    ) -> Result<(OutWitnessVec, OutWitnessVec), BlockVerifyErr> {
        let (outs, to_delete) = self.validate_txs(prev_pow, prev, key, vrf_in_out)?;

        Ok((outs, to_delete))
    }
}

impl Encode for PowBlockHeader {
    fn encode<E: bincode::enc::Encoder>(
        &self,
        encoder: &mut E,
    ) -> core::result::Result<(), bincode::error::EncodeError> {
        let version = self.version.to_le_bytes();
        let nonce = self.nonce.to_le_bytes();
        bincode::Encode::encode(&version, encoder)?;
        bincode::Encode::encode(&self.sector_id, encoder)?;
        bincode::Encode::encode(&self.height, encoder)?;
        bincode::Encode::encode(&self.prev_hash, encoder)?;
        bincode::Encode::encode(&self.block_root, encoder)?;
        bincode::Encode::encode(&self.prev_root, encoder)?;
        bincode::Encode::encode(&nonce, encoder)?;
        crate::codec::encode_fixed_14_array_u32(&self.bits, encoder)?;
        bincode::Encode::encode(&self.bt_mean, encoder)?;
        bincode::Encode::encode(&self.diff_heights, encoder)?;
        bincode::Encode::encode(&self.timestamp, encoder)?;
        bincode::Encode::encode(&self.vrf_pkey_bytes, encoder)?;
        bincode::Encode::encode(&self.vrf_out, encoder)?;
        bincode::Encode::encode(&self.vrf_proof_1, encoder)?;
        bincode::Encode::encode(&self.vrf_proof_2, encoder)?;
        bincode::Encode::encode(&self.extra_data, encoder)?;

        match self.height % 4 {
            1 | 3 => {
                bincode::Encode::encode(self.runnerup_hashes.as_ref().unwrap(), encoder)?;
                bincode::Encode::encode(self.runnerups_prev_hash.as_ref().unwrap(), encoder)?;
            }

            _ => {}
        }

        Ok(())
    }
}

impl Decode for PowBlockHeader {
    fn decode<D: bincode::de::Decoder>(
        decoder: &mut D,
    ) -> core::result::Result<Self, bincode::error::DecodeError> {
        let version = crate::codec::decode_fixed_u16(decoder)?;
        let sector_id: u8 = bincode::Decode::decode(decoder)?;
        let height = bincode::Decode::decode(decoder)?;
        let prev_hash = bincode::Decode::decode(decoder)?;
        let m = height % 4;
        Ok(Self {
            version,
            height,
            prev_hash,
            sector_id,
            block_root: bincode::Decode::decode(decoder)?,
            prev_root: bincode::Decode::decode(decoder)?,
            nonce: crate::codec::decode_fixed_u32(decoder)?,
            bits: crate::codec::decode_fixed_14_array_u32(decoder)?,
            bt_mean: bincode::Decode::decode(decoder)?,
            diff_heights: bincode::Decode::decode(decoder)?,
            timestamp: bincode::Decode::decode(decoder)?,
            vrf_pkey_bytes: bincode::Decode::decode(decoder)?,
            vrf_out: bincode::Decode::decode(decoder)?,
            vrf_proof_1: bincode::Decode::decode(decoder)?,
            vrf_proof_2: bincode::Decode::decode(decoder)?,
            extra_data: {
                let d: Vec<u8> = bincode::Decode::decode(decoder)?;

                if d.len() > 14 {
                    return Err(bincode::error::DecodeError::OtherString(format!(
                        "invalid extra data, max len is 14, received {}",
                        d.len()
                    )));
                }
                d
            },
            runnerup_hashes: match m {
                1 | 3 => Some(bincode::Decode::decode(decoder)?),
                _ => None,
            },
            runnerups_prev_hash: match m {
                1 | 3 => Some(bincode::Decode::decode(decoder)?),
                _ => None,
            },
            hash: None,
        })
    }
}

impl Encode for BlockHeader {
    fn encode<E: bincode::enc::Encoder>(
        &self,
        encoder: &mut E,
    ) -> core::result::Result<(), bincode::error::EncodeError> {
        bincode::Encode::encode(&self.chain_id, encoder)?;
        bincode::Encode::encode(&self.height, encoder)?;
        bincode::Encode::encode(&self.prev_hash, encoder)?;
        bincode::Encode::encode(&self.tx_root, encoder)?;
        for acc in &self.accumulators {
            bincode::Encode::encode(&acc.to_bytes(), encoder)?;
        }
        for poc in &self.poc {
            bincode::Encode::encode(&poc.to_bytes(), encoder)?;
        }
        bincode::Encode::encode(&self.block_bloom.to_bytes(), encoder)?;

        Ok(())
    }
}

impl Decode for BlockHeader {
    fn decode<D: bincode::de::Decoder>(
        decoder: &mut D,
    ) -> core::result::Result<Self, bincode::error::DecodeError> {
        let chain_id = bincode::Decode::decode(decoder)?;
        let height = bincode::Decode::decode(decoder)?;
        let prev_hash = bincode::Decode::decode(decoder)?;
        Ok(Self {
            chain_id,
            height,
            prev_hash,
            tx_root: bincode::Decode::decode(decoder)?,
            accumulators: {
                let mut buf: ArrayVec<Accumulator<Rsa2048, Output>, ACCUMULATOR_MULTIPLIER> =
                    ArrayVec::new();

                for _ in 0..ACCUMULATOR_MULTIPLIER {
                    let v: Vec<u8> = bincode::Decode::decode(decoder)?;
                    buf.push(
                        Accumulator::from_bytes(&v)
                            .map_err(|e| bincode::error::DecodeError::OtherString(e.to_owned()))?,
                    );
                }

                buf
            },
            poc: {
                let mut buf: ArrayVec<ProofOfCorrectness<Rsa2048, Output>, ACCUMULATOR_MULTIPLIER> =
                    ArrayVec::new();

                for _ in 0..ACCUMULATOR_MULTIPLIER {
                    let v: Vec<u8> = bincode::Decode::decode(decoder)?;
                    buf.push(
                        ProofOfCorrectness::from_bytes(&v)
                            .map_err(|e| bincode::error::DecodeError::OtherString(e.to_owned()))?,
                    );
                }

                buf
            },
            block_bloom: {
                let v: Vec<u8> = bincode::Decode::decode(decoder)?;
                let bloom_seed_hash =
                    Hash256::hash_from_slice(prev_hash.0, &format!(bloom_hash_key!(), chain_id));
                let mut keys = [(0, 0); 2];
                keys[0].0 = slice_to_u64(&bloom_seed_hash.0[..8]);
                keys[0].1 = slice_to_u64(&bloom_seed_hash.0[8..16]);
                keys[1].0 = slice_to_u64(&bloom_seed_hash.0[16..24]);
                keys[1].1 = slice_to_u64(&bloom_seed_hash.0[24..]);

                BloomFilterHash256::from_bytes(&v, keys)
                    .map_err(|e| bincode::error::DecodeError::OtherString(e.to_owned()))?
            },
            hash: None,
        })
    }
}

#[inline]
// Assumes bytes len is 8
fn slice_to_u64(bytes: &[u8]) -> u64 {
    let mut buf = [0; 8];
    buf.copy_from_slice(bytes);
    u64::from_le_bytes(buf)
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum BlockVerifyErr {
    InvalidHeight,
    InvalidPrevHash,
    InvalidTimestamp,
    InvalidSectorID,
    InvalidChainID,
    InvalidRunnerupHash,
    InvalidRunnerupPrevHash,
    InvalidDiffHeight,
    InvalidDiffMean,
    InvalidDiff,
    InvalidPoW,
    InvalidOuts,
    InvalidCoinbase,
    InvalidRunnerupTimestamp,
    InvalidExtraData,
    SigVerificationErr,
    InvalidSignature,
    InvalidScriptExecution,
    InvalidInputFormat,
    InvalidVrfFields,
    Tx(TxVerifyErr),
}

impl From<SigVerificationErr> for BlockVerifyErr {
    fn from(_other: SigVerificationErr) -> Self {
        Self::SigVerificationErr
    }
}

impl From<TxVerifyErr> for BlockVerifyErr {
    fn from(other: TxVerifyErr) -> Self {
        Self::Tx(other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::consensus::*;
    use crate::primitives::*;
    use crate::vm::{StackTrace, VmResult};
    use quickcheck::*;
    use std::collections::{HashMap, HashSet};
    use std::path::PathBuf;

    quickcheck! {
        fn accumulator_encode_decode_prop(xs: Vec<Vec<u8>>) -> bool {
            let accumulator = Accumulator::<Rsa2048, Vec<u8>>::empty();
            let (witness_deleted, proof_deleted) = accumulator.delete_with_proof(&[]).unwrap();
            let (accumulator, proof_added) = witness_deleted.add_with_proof(&xs);
            assert_eq!(accumulator, Accumulator::from_bytes(&accumulator.to_bytes()).unwrap());
            true
        }

        fn poc_encode_decode_prop(xs: Vec<Vec<u8>>) -> bool {
            let accumulator = Accumulator::<Rsa2048, Vec<u8>>::empty();
            let (witness_deleted, proof_deleted) = accumulator.delete_with_proof(&[]).unwrap();
            let (accumulator, proof_added) = witness_deleted.add_with_proof(&xs);
            let poc = ProofOfCorrectness::new(proof_added, proof_deleted);
            let decoded_poc = ProofOfCorrectness::from_bytes(&poc.to_bytes()).unwrap();
            assert_eq!(poc, decoded_poc);
            true
        }
    }

    #[test]
    fn block_header_encode_decode() {
        let config = ChainConfig::new("mainnet");
        let mut genesis = BlockHeader::genesis_cached(255, &config);
        let encoded = crate::codec::encode_to_vec(genesis.as_ref()).unwrap();
        let decoded: BlockHeader = crate::codec::decode(&encoded).unwrap();
        let mut genesis = genesis.as_ref().clone();
        assert_eq!(decoded, genesis);
    }

    #[test]
    fn test_accumulator() {
        let elems = vec!["test1".to_owned(), "test2".to_owned(), "test3".to_owned()];
        let elemsplus1 = vec![
            "test1".to_owned(),
            "test2".to_owned(),
            "test3".to_owned(),
            "test4".to_owned(),
        ];
        let elemsminus1 = vec!["test1".to_owned(), "test2".to_owned()];
        let accumulator1 = Accumulator::<Rsa2048, String>::empty();
        let (witness_deleted, proof_deleted) = accumulator1.clone().delete_with_proof(&[]).unwrap();
        let (accumulator2, proof_added) = witness_deleted.add_with_proof(&elems);
        assert!(accumulator2.verify_membership_batch(&elems, &proof_added));
        assert!(!accumulator2.verify_membership_batch(&elems, &proof_deleted));
        assert!(!accumulator2.verify_membership_batch(&elemsplus1, &proof_added));
        assert!(accumulator2
            .prove_membership(&[("test6".to_owned(), proof_added.witness.clone())])
            .is_err());
        assert!(accumulator1.verify_membership_batch(&[], &proof_deleted));
        assert_eq!(proof_added.witness, proof_deleted.witness);

        for e in &elems {
            let witness = Witness(Accumulator::<Rsa2048, String>::empty());
            let witness = witness
                .compute_subset_witness(&elems, &[e.clone()])
                .unwrap();
            let witness2 = witness
                .clone()
                .compute_subset_witness(&elemsplus1, &[e.clone()])
                .unwrap();

            assert!(accumulator2
                .prove_membership(&[(e.clone(), witness)])
                .is_ok());
            assert!(accumulator2
                .prove_membership(&[(e.clone(), witness2)])
                .is_err());
        }

        for e in &elemsminus1 {
            let witness = Witness(Accumulator::<Rsa2048, String>::empty());
            let witness3 = witness
                .clone()
                .compute_subset_witness(&elemsminus1, &[e.clone()])
                .unwrap();
            let witness4 = witness
                .clone()
                .compute_subset_witness(&[e.clone()], &[e.clone()])
                .unwrap();
            let witness5 = witness.clone().compute_subset_witness(&[], &[]).unwrap();

            assert!(accumulator2
                .prove_membership(&[(e.clone(), witness3)])
                .is_err());
            assert!(accumulator2
                .prove_membership(&[(e.clone(), witness4)])
                .is_err());
            assert!(accumulator2
                .prove_membership(&[(e.clone(), witness5)])
                .is_err());
        }
    }

    #[test]
    fn test_accumulator_bridge() {
        let batch_sizes = vec![50, 50, 50];
        let chain_id = 255;
        let config = ChainConfig::default();
        let address = Address::from_bech32("pu1wyzgxpzedr24l28ku8nsfwd2h4zrsqas69s3mp").unwrap();
        let key = config.get_chain_key(chain_id);
        let ss = Script::new_simple_spend();
        let sh = ss.to_script_hash(key);
        let mut out_stack = vec![];
        let mut outs_sum = 0;
        let mut coloured_ins_sums = HashMap::new();
        let mut coloured_outs_sums = HashMap::new();
        let script_args = vec![
            VmTerm::Signed128(INITIAL_BLOCK_REWARD),
            VmTerm::Hash160(address.0),
            VmTerm::Hash160(sh.0),
            VmTerm::Unsigned32(0),
        ];
        let script = Script::new_coinbase();
        let mut input = Input {
            input_flags: InputFlags::IsCoinbase,
            script_args,
            ..Default::default()
        };
        input.compute_hash(key);

        let addresses: Vec<_> = (0..5).map(|_| Address::random()).collect();

        let mut idx_map = HashMap::new();
        let mut witness_all = Witness(Accumulator::<Rsa2048, Hash256>::empty());
        let mut witness_all2 = Witness(Accumulator::<Rsa2048, Hash256>::empty());
        let mut accumulator = Accumulator::<Rsa2048, Hash256>::empty();
        let mut proof_added = None;
        let mut proof_deleted = None;
        let mut next_to_delete = vec![];
        let mut outs_vec: Vec<(Hash256, Witness<Rsa2048, Hash256>)> = vec![];
        let mut outs_vec2: Vec<(Hash256, Witness<Rsa2048, Hash256>)> = vec![];
        let mut ver_stack = VerificationStack::new();

        for batch_size in &batch_sizes {
            let in_clone = input.clone();
            let r = script.execute(
                &input.script_args,
                &[],
                &mut out_stack,
                &mut outs_sum,
                &mut coloured_ins_sums,
                &mut coloured_outs_sums,
                &mut idx_map,
                &mut ver_stack,
                [0; 32],
                key,
                "",
                VmFlags {
                    is_coinbase: true,
                    ..VmFlags::default()
                },
            );

            assert_eq!(r, VmResult(Ok(ExecutionResult::Ok)));

            let outputs: Vec<Output> = out_stack
                .iter()
                .cycle()
                .take(*batch_size)
                .cloned()
                .fold((0, vec![]), |(mut counter, mut out_buf), mut o| {
                    o.inputs_hash = Hash160(rand::thread_rng().gen());
                    o.hash = None;
                    o.address = Some(addresses[counter % 5].clone());
                    o.compute_hash(key);
                    out_buf.push(o);
                    counter += 1;
                    (counter, out_buf)
                })
                .1;
            let out_hashes: Vec<_> = outputs.iter().map(|o| *o.hash().unwrap()).collect();
            let (witness_deleted, pd) = accumulator
                .clone()
                .delete_with_proof(&next_to_delete)
                .unwrap();
            let (accumulator2, pa) = witness_deleted.add_with_proof(&out_hashes);
            let mut witnesses = pa.witness.compute_individual_witnesses(&out_hashes);
            let half_len = out_hashes.len() >> 1;
            for (e, witness) in &witnesses {
                assert!(accumulator2
                    .prove_membership(&[(*e, witness.clone())])
                    .is_ok());
            }

            let deleted_set: HashSet<_> = next_to_delete.iter().map(|(o, _)| *o).collect();
            let deleted: Vec<_> = next_to_delete.iter().map(|(o, _)| *o).collect();
            let mut untracked_deletions = deleted.clone();
            untracked_deletions.retain(|o| !outs_vec2.iter().map(|(o1, _)| o1).any(|o1| &o1 == &o));
            outs_vec.retain(|(o, _)| !deleted_set.contains(o));
            outs_vec.extend(witnesses.clone());
            outs_vec2.retain(|(o, _)| !deleted_set.contains(o));
            outs_vec2.extend_from_slice(&witnesses[..half_len]);
            let outs: Vec<_> = outs_vec.iter().map(|(o, _)| *o).collect();
            let outs2: Vec<_> = outs_vec2.iter().map(|(o, _)| *o).collect();
            let untracked_additions: Vec<_> =
                witnesses[half_len..].iter().map(|(o, _)| *o).collect();
            let outs3: Vec<_> = witnesses[half_len..].to_vec();
            let mut witness_all3 = Witness(Accumulator::<Rsa2048, Hash256>::empty());
            let mut witness_all4 = Witness(Accumulator::<Rsa2048, Hash256>::empty());

            witness_all = accumulator2
                .clone()
                .update_membership_witness(witness_all.clone(), &outs, &[], &[])
                .unwrap();

            witness_all2 = accumulator2
                .clone()
                .update_membership_witness(
                    witness_all2.clone(),
                    &outs2,
                    &untracked_additions,
                    &untracked_deletions,
                )
                .unwrap();

            witness_all3 = accumulator2
                .clone()
                .update_membership_witness(witness_all3.clone(), &outs, &[], &[])
                .unwrap();

            witness_all4 = witness_all3
                .clone()
                .compute_subset_witness(&outs, &outs2)
                .unwrap();

            outs_vec = witness_all.clone().compute_individual_witnesses(&outs);
            for (o, witness) in &outs_vec {
                assert!(accumulator2
                    .prove_membership(&[(*o, witness.clone())])
                    .is_ok());
            }

            let witnesses2 = witness_all2.clone().compute_individual_witnesses(&outs2);
            for (o, witness) in &witnesses2 {
                assert!(accumulator2
                    .prove_membership(&[(*o, witness.clone())])
                    .is_ok());
            }

            let witnesses3 = witness_all3.clone().compute_individual_witnesses(&outs);
            for (o, witness) in &witnesses3 {
                assert!(accumulator2
                    .prove_membership(&[(*o, witness.clone())])
                    .is_ok());
            }

            let witnesses4 = witness_all4.clone().compute_individual_witnesses(&outs2);
            for (o, witness) in &witnesses4 {
                assert!(accumulator2
                    .prove_membership(&[(*o, witness.clone())])
                    .is_ok());
            }

            assert!(accumulator2.verify_membership_batch(&out_hashes, &pa));
            assert!(!accumulator2.verify_membership_batch(&out_hashes, &pd));
            assert_eq!(pa.witness, pd.witness);
            outs_vec.shuffle(&mut rand::thread_rng());
            next_to_delete = outs_vec.iter().take(*batch_size / 2).cloned().collect();
            accumulator = accumulator2;
            proof_added = Some(pa);
            proof_deleted = Some(pd);
        }
    }

    #[test]
    fn it_doesnt_blow_the_stack_when_processing_a_block_full_of_errors() {
        let batch_sizes = [
            250, 500, 750, 1000, 1500, 2000, 2500, 3500, 4000, 10000, 20000,
        ];
        let chain_id = 255;
        let config = ChainConfig::default();
        let address = Address::from_bech32("pu1wyzgxpzedr24l28ku8nsfwd2h4zrsqas69s3mp").unwrap();
        let key = config.get_chain_key(chain_id);
        let ss = Script::new_simple_spend();
        let sh = ss.to_script_hash(key);
        let mut out_stack = vec![];
        let mut outs_sum = 0;
        let mut coloured_ins_sums = HashMap::new();
        let mut coloured_outs_sums = HashMap::new();
        let mut ver_stack = VerificationStack::new();
        let mut idx_map = HashMap::new();
        let script_args = vec![
            VmTerm::Signed128(INITIAL_BLOCK_REWARD),
            VmTerm::Hash160(address.0),
            VmTerm::Hash160(sh.0),
            VmTerm::Unsigned64(1),
            VmTerm::Unsigned32(0),
        ];
        let mut input = Input {
            script: Script::new_coinbase(),
            input_flags: InputFlags::IsCoinbase,
            script_args,
            ..Default::default()
        };
        input.compute_hash(key);

        for batch_size in &batch_sizes {
            let in_clone = input.clone();
            input.script.execute(
                &input.script_args,
                &[in_clone],
                &mut out_stack,
                &mut outs_sum,
                &mut coloured_ins_sums,
                &mut coloured_outs_sums,
                &mut idx_map,
                &mut ver_stack,
                [0; 32],
                key,
                "",
                VmFlags::default(),
            );

            let outputs: Vec<Output> = out_stack
                .iter()
                .cycle()
                .take(*batch_size * SHARDS_PER_SECTOR)
                .cloned()
                .map(|mut o| {
                    o.inputs_hash = Hash160(rand::thread_rng().gen());
                    o.hash = None;
                    o.compute_hash(key);
                    o
                })
                .collect();
        }
    }
}

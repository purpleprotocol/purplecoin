// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::backend::disk::DB;
use crate::chain::{ChainConfig, SectorConfig, ShardConfig};
use crate::consensus::{SECTORS, SHARDS_PER_SECTOR};
use crate::primitives::{
    Block, BlockData, BlockHeader, BlockVerifyErr, Hash256, Output, PowBlock, PowBlockHeader,
};
use accumulator::group::Rsa2048;
use accumulator::Witness;
use bincode::error::EncodeError as BincodeEncodeErr;
use bincode::{Decode, Encode};
use chrono::prelude::*;
use croaring::Bitmap;
use rocksdb::Error as RocksDBErr;
use rocksdb::{ColumnFamilyDescriptor, LogLevel, Options, TransactionDBOptions};
use std::borrow::Borrow;
use std::cmp;
use std::mem;
use std::path::PathBuf;
use std::str::FromStr;
use streaming_iterator::StreamingIterator;
use triomphe::Arc;

/// Interface to the underlying database for the runtime. When using `RocksDB`,
/// this will delegate to the default Column Family.
pub trait DBInterface {
    fn get<K: AsRef<[u8]>, V: Decode>(&self, key: K) -> Result<Option<V>, DBInterfaceErr>;
    fn put<K: AsRef<[u8]>, V: Encode>(&self, key: K, v: V) -> Result<(), DBInterfaceErr>;
    fn delete<K: AsRef<[u8]>, V: Decode>(&self, k: K) -> Result<(), DBInterfaceErr>;
    fn prefix_iterator<'a, V: bincode::Decode + 'a>(
        &self,
        prefix: Vec<u8>,
        direction: IteratorDirection,
    ) -> Box<dyn StreamingIterator<Item = (Vec<u8>, V)> + 'a>;
}

pub enum IteratorDirection {
    Forward,
    Backward,
}

/// Trait for state backend as used by the `PoW` chain module
pub trait PowChainBackend: Sized + Clone {
    /// Returns a block with the given hash in the canonical chain
    ///
    /// This might return `None` when a header actually exists if header pruning is enabled.
    fn get_canonical_pow_block(
        &self,
        hash: &Hash256,
    ) -> Result<Option<PowBlockHeader>, PowChainBackendErr>;

    /// Returns the block hashes of the tips in the current sector
    fn get_sector_canonical_block_hashes(
        &self,
    ) -> Result<[Option<Hash256>; 64], PowChainBackendErr>;

    /// Returns the blocks of the tips in the current sector
    fn get_sector_canonical_blocks(
        &self,
    ) -> Result<[Option<BlockHeader>; SHARDS_PER_SECTOR], PowChainBackendErr>;

    /// Returns the canonical block header of the shard with the given chain id.
    fn get_shard_canonical_block_header(
        &self,
        chain_id: u8,
    ) -> Result<BlockHeader, PowChainBackendErr>;

    /// Returns the canonical block header of the shard with the given chain id at the given height.
    ///
    /// This function might return `Ok(None)` if a header exists actually exists but pruning is enabled.
    fn get_shard_canonical_block_header_at_height(
        &self,
        chain_id: u8,
        height: u64,
    ) -> Result<Option<BlockHeader>, PowChainBackendErr>;

    /// Retrieves the data of the block with the given hash from the shard with the given chain id.
    ///
    /// This function might return `Ok(None)` if the block data exists actually exists but pruning is enabled.
    fn get_shard_block_data(
        &self,
        chain_id: u8,
        block_hash: &Hash256,
    ) -> Result<Option<BlockData>, PowChainBackendErr>;

    /// Returns the canonical block at heigh if it exists
    ///
    /// This might return `None` when a header actually exists if header pruning is enabled.
    fn get_canonical_pow_block_at_height(
        &self,
        pos: u64,
    ) -> Result<Option<PowBlockHeader>, PowChainBackendErr>;

    /// Returns non canonical blocks at height if they exist
    fn get_non_canonical_blocks_at_height(
        &self,
        h: u64,
    ) -> Result<Vec<PowBlockHeader>, PowChainBackendErr>;

    /// Returns all valid runnerups at height. If the given height is in the past, returns
    /// only the chosen runnerup.
    fn get_runnerups_at_height(&self, h: u64) -> Result<Vec<PowBlockHeader>, PowChainBackendErr>;

    /// Attempts to rewind the chain to the given position. This rewinds all the shards in the sector as well.
    fn rewind(&self, pos: u64) -> Result<(), PowChainBackendErr>;

    /// Attempt to prune headers up to pos
    fn prune_headers(&self, pos: u64) -> Result<(), PowChainBackendErr>;

    /// Returns the chain config
    fn chain_config(&self) -> &ChainConfig;

    /// Returns the min chain id and max chain id in this sector
    fn chain_ids(&self) -> (u8, u8) {
        self.sector_config().chain_ids()
    }

    /// Returns the sector config
    fn sector_config(&self) -> &SectorConfig;

    /// Returns the current height of the chain tip
    fn height(&self) -> Result<u64, PowChainBackendErr>;

    /// Writes a header to the state
    fn write_header(&self, block_header: &PowBlockHeader) -> Result<(), PowChainBackendErr>;

    /// Writes a runnerup header
    fn write_runnerup_header(
        &self,
        block_header: &PowBlockHeader,
    ) -> Result<(), PowChainBackendErr>;

    /// Writes a Pow block and corresponding batch of blocks and their outputs.
    ///
    /// Assumes all validations have passed
    fn write_block_batch(
        &self,
        block: &PowBlock,
        batch: &[(Block, Vec<Output>)],
    ) -> Result<(), PowChainBackendErr>;

    /// Validates a header against the tip of the chain
    fn validate_header(&self, header: &PowBlockHeader) -> Result<(), PowChainBackendErr> {
        let tip = self.tip()?;

        // Fully run block header validations except for the runnerup hash
        header.validate(&tip)?;

        // Validate runnerup hash
        if header.round() == 2 {
            let ruhashes = &header
                .runnerup_hashes
                .ok_or(ShardBackendErr::Block(BlockVerifyErr::InvalidRunnerupHash))?;
            let runnerups = self.get_runnerups_at_height(header.height - 1)?;
            let valid_runnerups_count = runnerups
                .iter()
                .filter(|r| ruhashes.contains(r.hash().unwrap()))
                .count();

            if valid_runnerups_count != SECTORS - 1 {
                return Err(PowChainBackendErr::Block(
                    BlockVerifyErr::InvalidRunnerupHash,
                ));
            }
        }

        Ok(())
    }

    /// Returns the next expected type of data according to the tip
    fn expects(&self) -> Result<BlockType, PowChainBackendErr> {
        let tip = self.tip()?;

        match tip.round() {
            1 => {
                let now = Utc::now().timestamp();

                if now > tip.timestamp + crate::consensus::SECOND_ROUND_TIMEOUT {
                    Ok(BlockType::NormalSecondRound)
                } else {
                    Ok(BlockType::Runnerup)
                }
            }

            2 => Ok(BlockType::Normal),
            _ => unreachable!(),
        }
    }

    /// Attempts to append a blockheader to the latest tip of the chain
    fn append_header(&self, header: &PowBlockHeader) -> Result<(), PowChainBackendErr> {
        self.validate_header(header)?;
        self.write_header(header)
    }

    /// Attempts to append a runnerup block header to the latest tip of the chain
    fn append_runnerup_header(&self, runnerup: &PowBlockHeader) -> Result<(), PowChainBackendErr> {
        let tip = self.tip()?;
        let prev = self
            .get_canonical_pow_block(&tip.prev_hash)?
            .ok_or(ShardBackendErr::CorruptData)?;
        runnerup.validate(&prev)?;
        self.write_runnerup_header(runnerup)
    }

    /// Appends a new pow block
    fn append_pow_block(&self, block: &PowBlock) -> Result<(), PowChainBackendErr> {
        let tip = self.tip()?;
        let sector_tips = self.get_sector_canonical_blocks()?;
        let blocks_with_outs = block.validate_against_current(
            &tip,
            &sector_tips,
            self.sector_config().key(),
            self.chain_config(),
        )?;
        self.write_block_batch(block, &blocks_with_outs)
    }

    /// Returns the sector id of the shard
    fn sector_id(&self) -> u8 {
        self.sector_config().sector_id
    }

    /// Returns the hashing key of the shard
    fn key(&self) -> &str {
        self.sector_config().key()
    }

    /// Returns the genesis header
    fn genesis(&self) -> PowBlockHeader {
        PowBlockHeader::genesis(self.sector_id(), self.chain_config())
    }

    /// Returns the current tip of the chain
    fn tip(&self) -> Result<PowBlockHeader, PowChainBackendErr> {
        match self.height()? {
            0 => unreachable!(),
            1 => Ok(self.genesis()),
            h => self
                .get_canonical_pow_block_at_height(h)?
                .ok_or(PowChainBackendErr::CorruptData),
        }
    }

    /// Override the current sector  config
    fn set_sector_config(&mut self, config: SectorConfig);
}

/// Trait for shard state backend as used by the chain module
pub trait ShardBackend: Sized + Clone {
    /// Returns a block with the given hash in the canonical chain
    ///
    /// This might return `None` when a header actually exists if header pruning is enabled.
    fn get_canonical_block(&self, hash: &Hash256) -> Result<Option<BlockHeader>, ShardBackendErr>;

    /// Returns the data of a block with the given hash
    ///
    /// This might return `None` when a block actually exists if transaction pruning is enabled.
    fn get_block_data(&self, hash: &Hash256) -> Result<Option<BlockData>, ShardBackendErr>;

    /// Returns the canonical block at heigh if it exists
    ///
    /// This might return `None` when a header actually exists if header pruning is enabled.
    fn get_canonical_block_at_height(
        &self,
        pos: u64,
    ) -> Result<Option<BlockHeader>, ShardBackendErr>;

    /// Returns non canonical blocks at height if they exist
    fn get_non_canonical_blocks_at_height(
        &self,
        h: u64,
    ) -> Result<Vec<BlockHeader>, ShardBackendErr>;

    /// Attempts to rewind the chain to the given position
    fn rewind(&self, pos: u64) -> Result<(), ShardBackendErr>;

    /// Attempt to prune headers up to pos
    fn prune_headers(&self, pos: u64) -> Result<(), ShardBackendErr>;

    /// Attempt to prune UTXOs up to pos
    fn prune_utxos(&self, pos: u64) -> Result<(), ShardBackendErr>;

    /// Returns output for the given hash if it exist in the UTXO set.
    ///
    /// This might return `None` when an UTXO actually exists in the set if UTXO pruning is enabled.
    fn utxo(&self, key: &Hash256) -> Option<Output>;

    /// Returns the current height of the chain tip
    fn height(&self) -> Result<u64, ShardBackendErr>;

    /// Returns the chain config
    fn chain_config(&self) -> &ChainConfig;

    /// Returns the shard config
    fn shard_config(&self) -> &ShardConfig;

    /// Writes a header to the state
    fn write_header(&self, block_header: &BlockHeader) -> Result<(), ShardBackendErr>;

    /// Writes block data to the state, assumes validations have passed
    fn write_block_data(
        &self,
        block: &Block,
        outputs: Vec<(Output, Witness<Rsa2048, Output>)>,
    ) -> Result<(), ShardBackendErr>;

    /// Validates a header against the tip of the chain
    fn validate_header(&self, header: &BlockHeader) -> Result<(), ShardBackendErr> {
        let tip = self.tip()?;

        // Fully run block header validations except for the runnerup hash
        header.validate(&tip)?;

        Ok(())
    }

    /// Attempts to append a blockheader to the latest tip of the chain
    fn append_header(&self, header: &BlockHeader) -> Result<(), ShardBackendErr> {
        self.validate_header(header)?;
        self.write_header(header)
    }

    /// Attempts to append a block to the latest tip of the chain. Assumes block header is valid
    fn append_block(&self, block: &Block) -> Result<(), ShardBackendErr> {
        let tip = self.tip()?;
        let (outs, _) = block.validate_against_current(&tip, self.shard_config().key())?;
        self.write_block(block, outs)
    }

    /// Writes the block to the state. Assumes validations have passed
    fn write_block(
        &self,
        block: &Block,
        outputs: Vec<(Output, Witness<Rsa2048, Output>)>,
    ) -> Result<(), ShardBackendErr> {
        self.write_header(&block.header)?;
        self.write_block_data(block, outputs)
    }

    /// Writes a single key and value to the backend storage
    fn write_key_val<T: AsRef<[u8]>>(&self, key: T, val: T) -> Result<(), ShardBackendErr> {
        self.write_key_vals_batch(vec![(key, val)])
    }

    /// Batch write keys and values
    fn write_key_vals_batch<T: AsRef<[u8]>>(
        &self,
        key_vals: Vec<(T, T)>,
    ) -> Result<(), ShardBackendErr>;

    /// Attempts to retrieve a value from the backend with the given key
    fn get_val<T: AsRef<[u8]>>(&self, key: T) -> Result<Option<Vec<u8>>, ShardBackendErr>;

    /// Returns the chain id of the shard
    fn chain_id(&self) -> u8 {
        self.shard_config().chain_id
    }

    /// Returns the hashing key of the shard
    fn key(&self) -> &str {
        self.shard_config().key()
    }

    /// Returns the genesis header
    fn genesis(&self) -> BlockHeader {
        BlockHeader::genesis_cached(self.chain_id(), self.chain_config())
            .as_ref()
            .clone()
    }

    /// Returns the current tip of the chain
    fn tip(&self) -> Result<BlockHeader, ShardBackendErr> {
        match self.height()? {
            0 => unreachable!(),
            1 => Ok(self.genesis()),
            h => self
                .get_canonical_block_at_height(h)?
                .ok_or(ShardBackendErr::CorruptData),
        }
    }

    /// Overrides the current shard config
    fn set_shard_config(&mut self, config: ShardConfig);
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BlockType {
    Normal,
    NormalSecondRound,
    Runnerup,
}

#[derive(Debug)]
pub enum DBInterfaceErr {
    /// Rocksdb error
    RocksDB(RocksDBErr),

    /// Generic error
    Error(&'static str),
}

#[derive(Debug)]
pub enum PowChainBackendErr {
    /// Given position is past the current bounds
    PosOutOfBounds,

    /// Backend data is corrupted
    CorruptData,

    /// Given height is invalid
    InvalidHeight,

    /// Block verify error
    Block(BlockVerifyErr),

    /// Rocksdb error
    RocksDB(RocksDBErr),

    /// Bincode encode error
    BincodeEncode(BincodeEncodeErr),

    /// Shard backend err
    ShardBackendErr(ShardBackendErr),

    /// Generic error
    Error(&'static str),
}

impl From<RocksDBErr> for DBInterfaceErr {
    fn from(other: RocksDBErr) -> Self {
        Self::RocksDB(other)
    }
}

impl From<ShardBackendErr> for PowChainBackendErr {
    fn from(other: ShardBackendErr) -> Self {
        Self::ShardBackendErr(other)
    }
}

impl From<RocksDBErr> for PowChainBackendErr {
    fn from(other: RocksDBErr) -> Self {
        Self::RocksDB(other)
    }
}

impl From<BincodeEncodeErr> for PowChainBackendErr {
    fn from(other: BincodeEncodeErr) -> Self {
        Self::BincodeEncode(other)
    }
}

impl From<BlockVerifyErr> for PowChainBackendErr {
    fn from(other: BlockVerifyErr) -> Self {
        Self::Block(other)
    }
}

#[derive(Debug)]
pub enum ShardBackendErr {
    /// Given position is past the current bounds
    PosOutOfBounds,

    /// Backend data is corrupted
    CorruptData,

    /// Given height is invalid
    InvalidHeight,

    /// Block verify error
    Block(BlockVerifyErr),

    /// Rocksdb error
    RocksDB(RocksDBErr),

    /// Bincode encode error
    BincodeEncode(BincodeEncodeErr),

    /// Generic error
    Error(&'static str),
}

impl From<BlockVerifyErr> for ShardBackendErr {
    fn from(other: BlockVerifyErr) -> Self {
        Self::Block(other)
    }
}

impl From<RocksDBErr> for ShardBackendErr {
    fn from(other: RocksDBErr) -> Self {
        Self::RocksDB(other)
    }
}

impl From<BincodeEncodeErr> for ShardBackendErr {
    fn from(other: BincodeEncodeErr) -> Self {
        Self::BincodeEncode(other)
    }
}

#[must_use]
pub fn create_rocksdb_backend<'a>() -> Arc<DB> {
    #[cfg(not(test))]
    let mut path = PathBuf::from_str(&crate::settings::SETTINGS.node.data_dir).unwrap();

    #[cfg(test)]
    let mut path = {
        use rand::Rng;
        let mut path = std::env::temp_dir();
        path.push(hex::encode(rand::thread_rng().gen::<[u8; 32]>()));
        path.push("Purplecoin");
        path
    };

    path.push(&crate::settings::SETTINGS.node.network_name);
    path.push("data");

    let mut cf_opts = Options::default();
    cf_opts.set_max_write_buffer_number(3);
    let cfs = vec![
        ColumnFamilyDescriptor::new(
            crate::chain::backend::disk::SECTOR_HEADERS_CF,
            cf_opts.clone(),
        ),
        ColumnFamilyDescriptor::new(
            crate::chain::backend::disk::SHARD_HEADERS_CF,
            cf_opts.clone(),
        ),
        ColumnFamilyDescriptor::new(crate::chain::backend::disk::MMR_CF, cf_opts.clone()),
        ColumnFamilyDescriptor::new(
            crate::chain::backend::disk::TRANSACTIONS_CF,
            cf_opts.clone(),
        ),
        ColumnFamilyDescriptor::new(crate::chain::backend::disk::OUTPUTS_CF, cf_opts.clone()),
        ColumnFamilyDescriptor::new(crate::chain::backend::disk::SHARE_CHAIN_CF, cf_opts),
    ];

    let mut db_opts = Options::default();
    db_opts.create_missing_column_families(true);
    db_opts.create_if_missing(true);
    db_opts.set_log_level(LogLevel::Warn);
    db_opts.set_keep_log_file_num(1);
    let db =
        DB::open_cf_descriptors(&db_opts, &TransactionDBOptions::default(), path, cfs).unwrap();
    Arc::new(db)
}

/// Lookup a bitmap from the database using the provided key
pub fn read_bitmap(db: Arc<DB>, key: &str) -> Result<Option<Bitmap>, String> {
    db.get(key)
        .map(|res| res.map(|bytes| Bitmap::deserialize(&bytes)))
        .map_err(|err| format!("could not read bitmap: {err}"))
}

/// Write bitmap to the database using the provided key
pub fn write_bitmap(db: Arc<DB>, key: &str, bitmap: Bitmap) -> Result<(), String> {
    db.put(key, bitmap.serialize())
        .map_err(|err| format!("could not write bitmap: {err}"))
}

#[derive(Debug, Clone, Encode, Decode)]
/// Explicit block with hash for serialization to disk
pub struct PowBlockHeaderWithHash {
    hash: Hash256,
    header: PowBlockHeader,
}

impl From<PowBlockHeader> for PowBlockHeaderWithHash {
    fn from(mut header: PowBlockHeader) -> Self {
        Self {
            hash: header.hash.take().unwrap(),
            header,
        }
    }
}

impl From<PowBlockHeaderWithHash> for PowBlockHeader {
    fn from(header: PowBlockHeaderWithHash) -> Self {
        let mut h = header.header;
        h.hash = Some(header.hash);
        h
    }
}

#[derive(Debug, Clone, Encode, Decode)]
/// Explicit block with hash for serialization to disk
pub struct BlockHeaderWithHash {
    hash: Hash256,
    header: BlockHeader,
}

impl From<BlockHeader> for BlockHeaderWithHash {
    fn from(mut header: BlockHeader) -> Self {
        Self {
            hash: header.hash.take().unwrap(),
            header,
        }
    }
}

impl From<BlockHeaderWithHash> for BlockHeader {
    fn from(header: BlockHeaderWithHash) -> Self {
        let mut h = header.header;
        h.hash = Some(header.hash);
        h
    }
}

pub struct DBPrefixIterator<V: bincode::Decode> {
    direction: IteratorDirection,
    data: Vec<(Vec<u8>, V)>,
    cursor: Option<usize>,
    done: bool,
}

impl<V: bincode::Decode> DBPrefixIterator<V> {
    #[must_use]
    pub fn new(data: Vec<(Vec<u8>, V)>, direction: IteratorDirection) -> Self {
        Self {
            direction,
            data,
            cursor: None,
            done: false,
        }
    }
}

impl<V: bincode::Decode> StreamingIterator for DBPrefixIterator<V> {
    type Item = (Vec<u8>, V);

    fn advance(&mut self) {
        if self.done {
            return;
        }

        if self.data.is_empty() {
            self.done = true;
            return;
        }

        if self.cursor.is_none() {
            match self.direction {
                IteratorDirection::Forward => {
                    self.cursor = Some(0);
                    return;
                }
                IteratorDirection::Backward => {
                    self.cursor = Some(self.data.len());
                }
            }
        }

        match self.direction {
            IteratorDirection::Forward => {
                let cur_cursor = *self.cursor.as_ref().unwrap();
                let next = cur_cursor.checked_add(1).unwrap_or(self.cursor.unwrap());

                if next >= self.data.len() || next == cur_cursor {
                    self.done = true;
                    return;
                }

                *self.cursor.as_mut().unwrap() = next;
            }
            IteratorDirection::Backward => {
                let cur_cursor = *self.cursor.as_ref().unwrap();

                if cur_cursor == 0 {
                    self.done = true;
                    return;
                }

                *self.cursor.as_mut().unwrap() -= 1;
            }
        }
    }

    fn get(&self) -> Option<&Self::Item> {
        if self.done {
            return None;
        }

        self.cursor?;
        self.data.get(self.cursor.unwrap())
    }
}

pub mod disk;
pub mod memory;
pub mod memory_store;

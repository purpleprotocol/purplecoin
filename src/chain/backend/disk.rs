// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::mmr::*;
use crate::chain::*;
use crate::primitives::*;
use accumulator::group::{Codec, Rsa2048};
use accumulator::Witness;
use dashmap::{DashMap as HashMap, DashSet as HashSet};
use rocksdb::Error as RocksDBErr;
use rocksdb::{MultiThreaded, TransactionDB, WriteBatchWithTransaction};
use std::sync::atomic::AtomicU64;
use std::sync::Arc;

pub type DB = TransactionDB<MultiThreaded>;
pub type WriteBatch = WriteBatchWithTransaction<true>;

pub const SECTOR_HEADERS_CF: &str = "sector_headers";
pub const SHARD_HEADERS_CF: &str = "shard_headers";
pub const MMR_CF: &str = "mmr";
pub const TRANSACTIONS_CF: &str = "transactions";
pub const OUTPUTS_CF: &str = "outputs";
pub const SHARE_CHAIN_CF: &str = "sharechain";

#[derive(Clone)]
pub struct DiskBackend<'a> {
    shard_config: Option<ShardConfig<'a>>,
    sector_config: Option<SectorConfig<'a>>,
    chain_config: Arc<ChainConfig>,
    db: Arc<DB>,
    cached_height: Arc<AtomicU64>,
    orphan_pool: Arc<HashSet<Hash256>>,
    block_buf: Arc<HashMap<Hash256, BlockHeader>>,
}

impl<'a> DiskBackend<'a> {
    pub fn new(
        db: Arc<DB>,
        chain_config: Arc<ChainConfig>,
        shard_config: Option<ShardConfig<'a>>,
        sector_config: Option<SectorConfig<'a>>,
    ) -> Result<Self, ShardBackendErr> {
        Ok(Self {
            db,
            chain_config,
            shard_config,
            sector_config,
            cached_height: Arc::new(AtomicU64::new(0)),
            orphan_pool: Arc::new(HashSet::new()),
            block_buf: Arc::new(HashMap::new()),
        })
    }

    pub fn is_shard(&self) -> bool {
        debug_assert!(self.sector_config.is_none());
        self.shard_config.is_some()
    }

    pub fn is_sector(&self) -> bool {
        debug_assert!(self.shard_config.is_none());
        self.sector_config.is_some()
    }

    pub fn get(&self, cf: &str, k: &[u8]) -> Result<Option<Vec<u8>>, RocksDBErr> {
        unimplemented!();
    }

    pub fn put(&self, cf: &str, k: Vec<u8>, v: Vec<u8>) -> Result<Option<Vec<u8>>, RocksDBErr> {
        unimplemented!();
    }
}

impl<'a> PowChainBackend<'a> for DiskBackend<'a> {
    fn get_canonical_pow_block(
        &self,
        hash: &Hash256,
    ) -> Result<Option<PowBlockHeader>, PowChainBackendErr> {
        unimplemented!()
    }

    fn get_sector_canonical_block_hashes(
        &self,
    ) -> Result<[Option<Hash256>; 64], PowChainBackendErr> {
        unimplemented!()
    }

    fn get_sector_canonical_blocks(&self) -> Result<[Option<BlockHeader>; 64], PowChainBackendErr> {
        unimplemented!()
    }

    fn get_shard_canonical_block_header(
        &self,
        chain_id: u8,
    ) -> Result<BlockHeader, PowChainBackendErr> {
        unimplemented!()
    }

    fn get_shard_canonical_block_header_at_height(
        &self,
        chain_id: u8,
        height: u64,
    ) -> Result<Option<BlockHeader>, PowChainBackendErr> {
        unimplemented!()
    }

    fn get_shard_block_data(
        &self,
        chain_id: u8,
        block_hash: &Hash256,
    ) -> Result<Option<BlockData>, PowChainBackendErr> {
        unimplemented!()
    }

    fn get_canonical_pow_block_at_height(
        &self,
        pos: u64,
    ) -> Result<Option<PowBlockHeader>, PowChainBackendErr> {
        unimplemented!()
    }

    fn get_non_canonical_blocks_at_height(
        &self,
        h: u64,
    ) -> Result<Vec<PowBlockHeader>, PowChainBackendErr> {
        unimplemented!()
    }

    fn get_runnerups_at_height(&self, h: u64) -> Result<Vec<PowBlockHeader>, PowChainBackendErr> {
        unimplemented!()
    }

    fn rewind(&self, pos: u64) -> Result<(), PowChainBackendErr> {
        unimplemented!()
    }

    fn prune_headers(&self, pos: u64) -> Result<(), PowChainBackendErr> {
        unimplemented!()
    }

    fn chain_config(&self) -> &ChainConfig {
        self.chain_config.as_ref()
    }

    fn chain_ids(&self) -> (u8, u8) {
        unimplemented!()
    }

    fn sector_config(&self) -> &SectorConfig {
        self.sector_config.as_ref().unwrap()
    }

    fn height(&self) -> Result<u64, PowChainBackendErr> {
        unimplemented!()
    }

    fn write_header(&self, block_header: &PowBlockHeader) -> Result<(), PowChainBackendErr> {
        unimplemented!()
    }

    fn write_block_batch(
        &self,
        block: &PowBlock,
        batch: &[(Block, Vec<Output>)],
    ) -> Result<(), PowChainBackendErr> {
        unimplemented!()
    }

    fn set_sector_config(&mut self, config: SectorConfig<'a>) {
        self.sector_config = Some(config);
    }

    fn write_runnerup_header(
        &self,
        block_header: &PowBlockHeader,
    ) -> Result<(), PowChainBackendErr> {
        let header: PowBlockHeaderWithHash = block_header.clone().into();
        let mut batch = self.db.transaction();
        let headers_cf = self.db.cf_handle(SECTOR_HEADERS_CF).unwrap();
        batch.put_cf(
            &headers_cf,
            header.hash.as_bytes(),
            crate::codec::encode_to_vec(&header)?,
        );
        batch.commit()?;
        Ok(())
    }
}

impl<'a> ShardBackend<'a> for DiskBackend<'a> {
    fn rewind(&self, pos: u64) -> Result<(), ShardBackendErr> {
        if ShardBackend::height(self)? <= pos {
            return Err(ShardBackendErr::InvalidHeight);
        }

        unimplemented!()
    }

    fn write_header(&self, block_header: &BlockHeader) -> Result<(), ShardBackendErr> {
        debug_assert!(block_header.height > 1);
        let headerwh: BlockHeaderWithHash = block_header.clone().into();
        let hbytes = headerwh.header.height.to_le_bytes();
        let mut tx = self.db.transaction();
        let hkey = &["h".as_bytes(), &[block_header.chain_id]].concat();
        let bhkey = &[[block_header.chain_id].as_slice(), &hbytes].concat();
        let headers_cf = self.db.cf_handle(SHARD_HEADERS_CF).unwrap();
        let cur_height = tx
            .get_cf(&headers_cf, hkey)?
            .map(|bytes| {
                let mut v: [u8; 8] = [0; 8];
                v.copy_from_slice(&bytes);
                u64::from_le_bytes(v)
            })
            .unwrap_or(1);

        tx.put_cf(
            &headers_cf,
            headerwh.hash.as_bytes(),
            crate::codec::encode_to_vec(&headerwh)?,
        );

        // Establish new canonical chain
        if headerwh.header.height > cur_height {
            tx.put_cf(&headers_cf, hkey, hbytes);
            tx.put_cf(&headers_cf, bhkey, headerwh.hash.as_bytes());
        }
        tx.commit()?;
        Ok(())
    }

    fn write_block_data(
        &self,
        block: &Block,
        outputs: Vec<(Output, Witness<Rsa2048, Output>)>,
    ) -> Result<(), ShardBackendErr> {
        let mut batch = WriteBatch::default();
        let hash = block.header.hash().unwrap();
        let pubkeys_key = &[b"p", hash.0.as_slice()].concat();
        let sig_key = &[b"s", hash.0.as_slice()].concat();
        let tx_count_key = &[b"t", hash.0.as_slice()].concat();
        let transactions_cf = self.db.cf_handle(TRANSACTIONS_CF).unwrap();
        let outputs_cf = self.db.cf_handle(OUTPUTS_CF).unwrap();
        batch.put_cf(
            &transactions_cf,
            tx_count_key,
            (block.body.txs.len() as u16).to_le_bytes(),
        );

        for (i, tx) in block.body.txs.iter().enumerate() {
            let i = i as u16;
            let tx_idx_key = &[&i.to_le_bytes(), hash.0.as_slice()].concat();
            batch.put_cf(&transactions_cf, tx_idx_key, tx.hash().unwrap().0);
            batch.put_cf(&transactions_cf, tx.hash().unwrap().0, &tx.to_bytes());
        }

        for out in outputs.iter() {
            batch.put_cf(
                &outputs_cf,
                out.0.hash().unwrap().0,
                &crate::codec::encode_to_vec(&(out.0.clone(), out.1.to_bytes())).unwrap(),
            );
        }

        if let Some(sig) = block.body.aggregated_signature.as_ref() {
            batch.put_cf(&transactions_cf, sig_key, sig.to_bytes());
        }

        self.db.write(batch)?;
        Ok(())
    }

    fn get_canonical_block(&self, hash: &Hash256) -> Result<Option<BlockHeader>, ShardBackendErr> {
        unimplemented!()
    }

    fn get_canonical_block_at_height(
        &self,
        h: u64,
    ) -> Result<Option<BlockHeader>, ShardBackendErr> {
        let bhkey = &[[self.shard_config().chain_id].as_slice(), &h.to_le_bytes()].concat();
        let headers_cf = self.db.cf_handle(SHARD_HEADERS_CF).unwrap();
        let hash = self.db.get_cf(&headers_cf, bhkey)?;
        if hash.is_none() {
            return Ok(None);
        }
        let hbytes = self.db.get_cf(&headers_cf, hash.as_ref().unwrap())?;
        if hbytes.is_none() {
            return Ok(None);
        }

        let headerwh: BlockHeaderWithHash =
            crate::codec::decode(&hbytes.unwrap()).map_err(|_| ShardBackendErr::CorruptData)?;
        Ok(Some(headerwh.into()))
    }

    fn get_non_canonical_blocks_at_height(
        &self,
        h: u64,
    ) -> Result<Vec<BlockHeader>, ShardBackendErr> {
        unimplemented!()
    }

    fn get_block_data(&self, hash: &Hash256) -> Result<Option<BlockData>, ShardBackendErr> {
        unimplemented!()
    }

    fn prune_headers(&self, pos: u64) -> Result<(), ShardBackendErr> {
        unimplemented!()
    }

    fn prune_utxos(&self, pos: u64) -> Result<(), ShardBackendErr> {
        unimplemented!()
    }

    // TODO: Cache this
    fn height(&self) -> Result<u64, ShardBackendErr> {
        let key = &["h".as_bytes(), &[self.shard_config().chain_id]].concat();
        let headers_cf = self.db.cf_handle(SHARD_HEADERS_CF).unwrap();
        let tx = self.db.transaction();
        match tx.get_cf(&headers_cf, key) {
            Ok(Some(bheight)) => {
                let bheight = self
                    .db
                    .get_cf(&headers_cf, key)?
                    .ok_or(ShardBackendErr::CorruptData)?;
                let mut out = [0; 8];
                out.copy_from_slice(&bheight);
                Ok(u64::from_le_bytes(out))
            }

            Ok(None) => {
                tx.put_cf(&headers_cf, key, 1_u64.to_le_bytes())?;
                tx.commit()?;
                Ok(1)
            }

            Err(err) => Err(err.into()),
        }
    }

    fn shard_config(&self) -> &ShardConfig {
        self.shard_config.as_ref().unwrap()
    }

    fn chain_config(&self) -> &ChainConfig {
        &self.chain_config
    }

    fn utxo(&self, key: &Hash256) -> Option<Output> {
        unimplemented!()
    }

    fn set_shard_config(&mut self, config: ShardConfig<'a>) {
        self.shard_config = Some(config);
    }

    fn get_val<T: AsRef<[u8]>>(&self, key: T) -> Result<Option<Vec<u8>>, ShardBackendErr> {
        unimplemented!();
    }

    fn write_key_vals_batch<T: AsRef<[u8]>>(
        &self,
        key_vals: Vec<(T, T)>,
    ) -> Result<(), ShardBackendErr> {
        unimplemented!()
    }
}

impl<'a> MMR<'a, Vec<u8>, Self> for DiskBackend<'a> {
    fn backend(&self) -> &DiskBackend<'a> {
        self
    }
}

impl<'a> MMRBackend<Vec<u8>> for DiskBackend<'a> {
    fn get(&self, pos: u64) -> Result<Option<Hash256>, MMRBackendErr> {
        unimplemented!()
    }

    fn get_leaf(&self, hash: &Hash256) -> Result<Option<Vec<u8>>, MMRBackendErr> {
        unimplemented!()
    }

    fn write_leaf(&self, hash: Hash256, leaf: &Vec<u8>) -> Result<(), MMRBackendErr> {
        unimplemented!()
    }

    fn get_peak(&self, pos: u64) -> Result<Option<Hash256>, MMRBackendErr> {
        unimplemented!()
    }

    fn get_hash(&self, pos: u64) -> Result<Option<Hash256>, MMRBackendErr> {
        unimplemented!()
    }

    fn write_hash_at_pos(&self, hash: Hash256, pos: u64) -> Result<(), MMRBackendErr> {
        unimplemented!()
    }

    fn leaf_pos_iter(&self) -> Box<dyn Iterator<Item = u64> + '_> {
        unimplemented!();
    }

    fn leaf_idx_iter(&self, from_idx: u64) -> Box<dyn Iterator<Item = u64> + '_> {
        unimplemented!();
    }

    fn n_unpruned_leaves(&self) -> u64 {
        unimplemented!();
    }

    fn n_unpruned_leaves_to_index(&self, to_index: u64) -> u64 {
        unimplemented!();
    }

    fn unpruned_size(&self) -> Result<u64, MMRBackendErr> {
        let key = &["u".as_bytes(), &[self.sector_config().sector_id]].concat();
        let mmr_cf = self.db.cf_handle(MMR_CF).unwrap();
        let tx = self.db.transaction();
        match tx.get_cf(&mmr_cf, key) {
            Ok(Some(bheight)) => {
                let bheight = self
                    .db
                    .get_cf(&mmr_cf, key)?
                    .ok_or(MMRBackendErr::CorruptData)?;
                let mut out = [0; 8];
                out.copy_from_slice(&bheight);
                Ok(u64::from_le_bytes(out))
            }

            Ok(None) => {
                tx.put_cf(&mmr_cf, key, 1_u64.to_le_bytes())?;
                tx.commit()?;
                Ok(1)
            }

            Err(err) => Err(err.into()),
        }
    }

    fn hash_key(&self) -> &str {
        if self.is_shard() {
            return self.shard_config.as_ref().unwrap().key;
        }

        if self.is_sector() {
            return self.sector_config.as_ref().unwrap().key;
        }

        unreachable!()
    }

    fn size(&self) -> Result<u64, MMRBackendErr> {
        let key = &["s".as_bytes(), &[self.sector_config().sector_id]].concat();
        let mmr_cf = self.db.cf_handle(MMR_CF).unwrap();
        let tx = self.db.transaction();
        match tx.get_cf(&mmr_cf, key) {
            Ok(Some(bheight)) => {
                let bheight = self
                    .db
                    .get_cf(&mmr_cf, key)?
                    .ok_or(MMRBackendErr::CorruptData)?;
                let mut out = [0; 8];
                out.copy_from_slice(&bheight);
                Ok(u64::from_le_bytes(out))
            }

            Ok(None) => {
                tx.put_cf(&mmr_cf, key, 1_u64.to_le_bytes())?;
                tx.commit()?;
                Ok(1)
            }

            Err(err) => Err(err.into()),
        }
    }

    fn flush(&mut self) -> Result<(), MMRBackendErr> {
        unimplemented!()
    }

    fn prune(&mut self) -> Result<(), MMRBackendErr> {
        unimplemented!()
    }
}

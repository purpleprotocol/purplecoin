// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::mmr::{MMRBackend, MMRBackendErr, MMR};
use crate::chain::{
    ChainConfig, PowChainBackend, PowChainBackendErr, SectorConfig, ShardBackend, ShardBackendErr,
    ShardConfig,
};
use crate::primitives::{Block, BlockData, BlockHeader, Hash256, Output, PowBlock, PowBlockHeader};
use accumulator::group::Rsa2048;
use accumulator::Witness;

#[derive(Debug, Clone)]
pub struct MemoryBackend<'a> {
    sector_config: SectorConfig<'a>,
    shard_config: ShardConfig<'a>,
    chain_config: ChainConfig,
}

impl<'a> PowChainBackend<'a> for MemoryBackend<'a> {
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
        &self.chain_config
    }

    fn sector_config(&self) -> &SectorConfig {
        &self.sector_config
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

    fn write_runnerup_header(
        &self,
        block_header: &PowBlockHeader,
    ) -> Result<(), PowChainBackendErr> {
        unimplemented!()
    }

    fn set_sector_config(&mut self, config: SectorConfig<'a>) {
        self.sector_config = config;
    }
}

impl<'a> ShardBackend<'a> for MemoryBackend<'a> {
    fn rewind(&self, pos: u64) -> Result<(), ShardBackendErr> {
        unimplemented!()
    }

    fn write_header(&self, block_header: &BlockHeader) -> Result<(), ShardBackendErr> {
        unimplemented!()
    }

    fn write_block_data(
        &self,
        block: &Block,
        outputs: Vec<(Output, Witness<Rsa2048, Output>)>,
    ) -> Result<(), ShardBackendErr> {
        unimplemented!()
    }

    fn get_canonical_block(&self, hash: &Hash256) -> Result<Option<BlockHeader>, ShardBackendErr> {
        unimplemented!()
    }

    fn get_canonical_block_at_height(
        &self,
        h: u64,
    ) -> Result<Option<BlockHeader>, ShardBackendErr> {
        unimplemented!()
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

    fn height(&self) -> Result<u64, ShardBackendErr> {
        unimplemented!()
    }

    fn shard_config(&self) -> &ShardConfig {
        &self.shard_config
    }

    fn chain_config(&self) -> &ChainConfig {
        &self.chain_config
    }

    fn utxo(&self, key: &Hash256) -> Option<Output> {
        unimplemented!()
    }

    fn set_shard_config(&mut self, config: ShardConfig) {
        unimplemented!()
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

impl<'a> MMR<'a, Vec<u8>, Self> for MemoryBackend<'a> {
    fn backend(&self) -> &MemoryBackend<'a> {
        self
    }
}

impl<'a> MMRBackend<Vec<u8>> for MemoryBackend<'a> {
    fn get(&self, pos: u64) -> Result<Option<Hash256>, MMRBackendErr> {
        unimplemented!()
    }

    fn get_leaf(&self, hash: &Hash256) -> Result<Option<Vec<u8>>, MMRBackendErr> {
        unimplemented!()
    }

    fn write_leaf(&self, hash: Hash256, leaf: &Vec<u8>) -> Result<(), MMRBackendErr> {
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

    fn get_peak(&self, pos: u64) -> Result<Option<Hash256>, MMRBackendErr> {
        unimplemented!()
    }

    fn get_hash(&self, pos: u64) -> Result<Option<Hash256>, MMRBackendErr> {
        unimplemented!()
    }

    fn write_hash_at_pos(&self, hash: Hash256, pos: u64) -> Result<(), MMRBackendErr> {
        unimplemented!()
    }

    fn unpruned_size(&self) -> Result<u64, MMRBackendErr> {
        unimplemented!()
    }

    fn hash_key(&self) -> &str {
        unimplemented!()
    }

    fn size(&self) -> Result<u64, MMRBackendErr> {
        unimplemented!()
    }

    fn flush(&mut self) -> Result<(), MMRBackendErr> {
        unimplemented!()
    }

    fn prune(&mut self) -> Result<(), MMRBackendErr> {
        unimplemented!()
    }
}

// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::mmr::{leaf_set::LeafSet, prune_list::PruneList, MMRBackend, MMRBackendErr};
use crate::chain::{
    backend::DB, ChainConfig, DBInterface, DBPrefixIterator, IteratorDirection, PowChainBackend,
    PowChainBackendErr, SectorConfig, ShardBackend, ShardBackendErr, ShardConfig,
};
use crate::consensus::SHARDS_PER_SECTOR;
use crate::primitives::{Block, BlockData, BlockHeader, Hash256, Output, PowBlock, PowBlockHeader};
use accumulator::group::Rsa2048;
use accumulator::Witness;
use parking_lot::RwLock;
use qp_trie::Trie;
use std::borrow::Borrow;
use std::cmp;
use std::collections::BTreeMap;
use std::str;
use streaming_iterator::StreamingIterator;
use triomphe::Arc;

type DataStore = Trie<Vec<u8>, Vec<u8>>;

#[derive(Debug, Clone, Default)]
pub struct MemoryBackend {
    /// Underlying data store. TODO: This isn't very performant and should
    /// be modelled as column families to reflect RocksDB.
    data: Arc<RwLock<DataStore>>,

    /// Sector config
    sector_config: SectorConfig,

    /// Shard config
    shard_config: ShardConfig,

    /// Chain config
    chain_config: ChainConfig,

    /// MMR size
    mmr_size: u64,
}

impl DBInterface for MemoryBackend {
    fn get<K: AsRef<[u8]>, V: bincode::Decode>(
        &self,
        key: K,
    ) -> Result<Option<V>, super::DBInterfaceErr> {
        unimplemented!()
    }

    fn put<K: AsRef<[u8]>, V: bincode::Encode>(
        &self,
        key: K,
        v: V,
    ) -> Result<(), super::DBInterfaceErr> {
        self.data.write().insert(
            key.as_ref().to_vec(),
            crate::codec::encode_to_vec(&v).unwrap(),
        );
        Ok(())
    }

    fn delete<K: AsRef<[u8]>, V: bincode::Decode>(
        &self,
        k: K,
    ) -> Result<(), super::DBInterfaceErr> {
        unimplemented!()
    }

    fn prefix_iterator<'b, V: bincode::Decode + 'b>(
        &self,
        prefix: Vec<u8>,
        direction: IteratorDirection,
    ) -> Box<dyn StreamingIterator<Item = (Vec<u8>, V)> + 'b> {
        let data = self
            .data
            .read()
            .subtrie(prefix.as_slice())
            .iter()
            .map(|(k, v)| (k.clone(), crate::codec::decode(v).unwrap()))
            .collect::<Vec<(Vec<u8>, V)>>();

        Box::new(DBPrefixIterator::new(data, direction))
    }

    fn db_handle(&self) -> Option<Arc<DB>> {
        None
    }
}

impl PowChainBackend for MemoryBackend {
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

    fn get_sector_canonical_blocks(
        &self,
    ) -> Result<[Option<BlockHeader>; SHARDS_PER_SECTOR], PowChainBackendErr> {
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

    fn set_sector_config(&mut self, config: SectorConfig) {
        self.sector_config = config;
    }

    fn set_prune_list(&mut self, prune_list: Arc<RwLock<PruneList>>) {
        unimplemented!()
    }

    fn set_leaf_set(&mut self, leaf_set: Arc<RwLock<LeafSet>>) {
        unimplemented!()
    }
}

impl ShardBackend for MemoryBackend {
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

    fn tip_pow(&self) -> Result<PowBlockHeader, ShardBackendErr> {
        PowChainBackend::tip(self).map_err(|err| err.into())
    }
}

impl MMRBackend<Vec<u8>> for MemoryBackend {
    fn get(&self, pos: u64) -> Result<Option<Hash256>, MMRBackendErr> {
        unimplemented!()
    }

    fn get_leaf(&self, hash: &Hash256) -> Result<Option<Vec<u8>>, MMRBackendErr> {
        unimplemented!()
    }

    fn write_leaf(&self, hash: Hash256, leaf: &Vec<u8>) -> Result<(), MMRBackendErr> {
        unimplemented!()
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

    fn set_size(&self, size: u64) -> Result<(), MMRBackendErr> {
        unimplemented!();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::boxed::Box;

    #[test]
    fn prefix_iterator_forward() {
        let mut backend = MemoryBackend::default();

        backend.put("random_data1".as_bytes(), "asdf".to_owned());
        backend.put("test.1".as_bytes(), "asdf".to_owned());
        backend.put("random_data2".as_bytes(), "asdf".to_owned());
        backend.put("random_data3".as_bytes(), "asdf".to_owned());
        backend.put("test.2".as_bytes(), "asdf".to_owned());
        backend.put("test.3".as_bytes(), "asdf".to_owned());
        backend.put("random_data4".as_bytes(), "asdf".to_owned());

        let mut result = vec![];
        let mut iter: Box<dyn StreamingIterator<Item = (Vec<u8>, String)>> =
            backend.prefix_iterator("test.".as_bytes().to_vec(), IteratorDirection::Forward);

        while let Some((k, v)) = iter.next() {
            result.push((k.clone(), v.clone()));
        }

        assert_eq!(
            result,
            vec![
                ("test.1".as_bytes().to_vec(), "asdf".to_owned()),
                ("test.2".as_bytes().to_vec(), "asdf".to_owned()),
                ("test.3".as_bytes().to_vec(), "asdf".to_owned()),
            ]
        );
    }

    #[test]
    fn prefix_iterator_backward() {
        let mut backend = MemoryBackend::default();

        backend.put("random_data1".as_bytes(), "asdf".to_owned());
        backend.put("test.1".as_bytes(), "asdf".to_owned());
        backend.put("random_data2".as_bytes(), "asdf".to_owned());
        backend.put("random_data3".as_bytes(), "asdf".to_owned());
        backend.put("test.2".as_bytes(), "asdf".to_owned());
        backend.put("test.3".as_bytes(), "asdf".to_owned());
        backend.put("random_data4".as_bytes(), "asdf".to_owned());

        let mut result = vec![];
        let mut iter: Box<dyn StreamingIterator<Item = (Vec<u8>, String)>> =
            backend.prefix_iterator("test.".as_bytes().to_vec(), IteratorDirection::Backward);

        while let Some((k, v)) = iter.next() {
            result.push((k.clone(), v.clone()));
        }

        assert_eq!(
            result,
            vec![
                ("test.3".as_bytes().to_vec(), "asdf".to_owned()),
                ("test.2".as_bytes().to_vec(), "asdf".to_owned()),
                ("test.1".as_bytes().to_vec(), "asdf".to_owned()),
            ]
        );
    }
}

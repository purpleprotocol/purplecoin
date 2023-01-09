// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::consensus::*;
use std::collections::HashMap;
use std::path::PathBuf;

#[derive(Debug, Clone)]
pub struct ChainConfig {
    network_name: &'static str,
    chain_keys: HashMap<u8, String>,
    sector_keys: HashMap<u8, String>,
}

impl Default for ChainConfig {
    fn default() -> Self {
        Self::new("testnet")
    }
}

impl ChainConfig {
    pub fn new(network_name: &'static str) -> Self {
        let mut chain_keys = HashMap::with_capacity(256);
        let mut sector_keys = HashMap::with_capacity(4);

        for i in 0..=255 {
            chain_keys.insert(i, format!("{network_name}.shard.{i}"));
        }

        let range_e = 256 / SHARDS_PER_SECTOR;

        for i in 0..range_e {
            sector_keys.insert(i as u8, format!("{network_name}.sector.{i}"));
        }

        Self {
            chain_keys,
            sector_keys,
            network_name,
        }
    }

    pub fn network_name(&self) -> &'static str {
        self.network_name
    }

    pub fn get_chain_key(&self, chain_id: u8) -> &str {
        self.chain_keys.get(&chain_id).unwrap()
    }

    pub fn get_sector_key(&self, sector_id: u8) -> &str {
        debug_assert!(sector_id < 4);
        self.sector_keys.get(&sector_id).unwrap()
    }
}

#[derive(Debug, Clone)]
/// Sector wide configuration
pub struct SectorConfig<'a> {
    /// Sector key
    pub key: &'a str,

    /// Sector id
    pub sector_id: u8,

    /// Prune headers
    pub prune_headers: bool,

    /// Prune transactions
    pub prune_transactions: bool,

    /// Prune utxos
    pub prune_utxos: bool,
}

impl<'a> SectorConfig<'a> {
    pub fn new(
        key: &'a str,
        sector_id: u8,
        prune_headers: bool,
        prune_transactions: bool,
        prune_utxos: bool,
    ) -> Self {
        Self {
            key,
            sector_id,
            prune_headers,
            prune_transactions,
            prune_utxos,
        }
    }

    pub fn key(&self) -> &'a str {
        self.key
    }
}

#[derive(Debug, Clone)]
/// Individual shard configuration. Takes precedence to
/// the sector config.
pub struct ShardConfig<'a> {
    /// Shard key
    pub key: &'a str,

    /// Chain id
    pub chain_id: u8,

    /// Prune headers
    pub prune_headers: bool,

    /// Prune transactions
    pub prune_transactions: bool,

    /// Prune utxos
    pub prune_utxos: bool,
}

impl<'a> ShardConfig<'a> {
    pub fn new(
        key: &'a str,
        chain_id: u8,
        prune_headers: bool,
        prune_transactions: bool,
        prune_utxos: bool,
    ) -> Self {
        Self {
            key,
            chain_id,
            prune_headers,
            prune_transactions,
            prune_utxos,
        }
    }

    pub fn key(&self) -> &'a str {
        self.key
    }
}

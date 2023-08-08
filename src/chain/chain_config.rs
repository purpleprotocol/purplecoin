// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::consensus::SHARDS_PER_SECTOR;
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
    #[must_use]
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
            network_name,
            chain_keys,
            sector_keys,
        }
    }

    #[must_use]
    pub fn network_name(&self) -> &'static str {
        self.network_name
    }

    #[must_use]
    pub fn get_chain_key(&self, chain_id: u8) -> &str {
        self.chain_keys.get(&chain_id).unwrap()
    }

    #[must_use]
    pub fn get_sector_key(&self, sector_id: u8) -> &str {
        debug_assert!(sector_id < 4);
        self.sector_keys.get(&sector_id).unwrap()
    }
}

#[derive(Debug, Clone, Default)]
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
    #[must_use]
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

    /// Returns the min chain id and max chain id in this sector
    #[must_use]
    pub fn chain_ids(&self) -> (u8, u8) {
        let sps = SHARDS_PER_SECTOR as u8;
        let ssps = self.sector_id * sps;
        (ssps, ssps + (sps - 1))
    }

    #[must_use]
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
    #[must_use]
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

    #[must_use]
    pub fn key(&self) -> &'a str {
        self.key
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::consensus::*;

    #[test]
    fn sector_config_returns_correct_chain_ids() {
        let mut config = SectorConfig::default();
        let sps = SHARDS_PER_SECTOR as u8;

        assert_eq!((0, sps - 1), config.chain_ids());
        config.sector_id += 1;
        assert_eq!((sps, sps * 2 - 1), config.chain_ids());
        config.sector_id = SECTORS as u8 - 1;
        assert_eq!(
            (config.sector_id * sps, config.sector_id * sps + (sps - 1)),
            config.chain_ids()
        );
    }
}

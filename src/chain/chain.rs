// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::{
    ChainConfig, DBInterface, PowChainBackend, Sector, SectorConfig, Shard, ShardBackend,
    ShardConfig,
};
use crate::node::{Mempool, PinnedMempool};
use parking_lot::RwLock;
use std::collections::HashMap;
use triomphe::Arc;

#[derive(Clone)]
pub struct Chain<B: PowChainBackend + ShardBackend + DBInterface> {
    pub backend: B,
    pub config: ChainConfig,
    pub mempool: PinnedMempool,
    pub sectors: HashMap<u8, Sector<B>>,
    pub chain_states: HashMap<u8, Shard<B>>,
}

impl<B: PowChainBackend + ShardBackend + DBInterface> Chain<B> {
    pub fn new(backend: B, config: &ChainConfig) -> Self {
        let mut chain_states = HashMap::with_capacity(256);
        let mut sectors = HashMap::with_capacity(4);

        for i in 0..=255 {
            let mut backend = backend.clone();
            let scfg = ShardConfig::new(config.get_chain_key(i), i, false, false, false);
            backend.set_shard_config(scfg);
            chain_states.insert(i, Shard::new(backend, i));
        }

        for i in 0..4 {
            let mut backend = backend.clone();
            let scfg = SectorConfig::new(config.get_chain_key(i), i, false, false, false);
            backend.set_sector_config(scfg);
            sectors.insert(i, Sector::new(backend, i));
        }

        Self {
            backend,
            config: config.clone(),
            chain_states,
            mempool: Arc::new(RwLock::new(Mempool::new())),
            sectors,
        }
    }
}

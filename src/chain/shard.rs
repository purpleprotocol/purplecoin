// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::{ChainConfig, PowChainBackend, ShardBackend, ShardBackendErr, ShardConfig};

#[derive(Clone)]
pub struct Shard<B: ShardBackend> {
    pub backend: B,
    pub chain_id: u8,
}

impl<B: ShardBackend> Shard<B> {
    pub fn new(backend: B, chain_id: u8) -> Self {
        Self { backend, chain_id }
    }

    /// Current chain height
    pub fn height(&self) -> Result<u64, ShardBackendErr> {
        self.backend.height()
    }

    pub fn chain_config(&self) -> &ChainConfig {
        self.backend.chain_config()
    }

    pub fn shard_config(&self) -> &ShardConfig {
        self.backend.shard_config()
    }

    pub fn chain_id(&self) -> u8 {
        self.chain_id
    }
}

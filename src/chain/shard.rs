// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::{ChainConfig, PowChainBackend, ShardBackend, ShardBackendErr, ShardConfig};
use std::marker::PhantomData;

#[derive(Clone)]
pub struct Shard<'a, B: ShardBackend<'a>> {
    pub backend: B,
    pub chain_id: u8,
    pub phantom: PhantomData<&'a str>,
}

impl<'a, B: ShardBackend<'a>> Shard<'a, B> {
    pub fn new(backend: B, chain_id: u8) -> Self {
        Self {
            backend,
            chain_id,
            phantom: PhantomData,
        }
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

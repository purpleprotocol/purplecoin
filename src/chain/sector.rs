// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::*;
use std::marker::PhantomData;

pub struct Sector<'a, B: PowChainBackend<'a>> {
    pub backend: B,
    pub sector_id: u8,
    pub phantom: PhantomData<&'a str>,
}

impl<'a, B: PowChainBackend<'a>> Sector<'a, B> {
    pub fn new(backend: B, sector_id: u8) -> Self {
        Self {
            backend,
            sector_id,
            phantom: PhantomData,
        }
    }

    /// Current chain height
    pub fn height(&self) -> Result<u64, PowChainBackendErr> {
        self.backend.height()
    }

    pub fn chain_config(&self) -> &ChainConfig {
        self.backend.chain_config()
    }

    pub fn expects(&self) -> Result<BlockType, PowChainBackendErr> {
        self.backend.expects()
    }
}

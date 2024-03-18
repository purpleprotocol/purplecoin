// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::primitives::BlockHeader;
use bincode::{Decode, Encode};

/// Request peer info from a node after identify protocol handshake
#[derive(Clone, Debug, Encode, Decode, Default)]
pub struct GetShardHeaderRequest {
    pub(crate) chain_id: u8,
    pub(crate) height: u64,
}

impl GetShardHeaderRequest {
    pub fn new(chain_id: u8, height: u64) -> Self {
        Self { chain_id, height }
    }
}

/// Response to a peer info request
#[derive(Clone, Debug, Encode, Decode)]
pub struct GetShardHeaderResponse {
    /// Block header
    pub(crate) headers: Vec<BlockHeader>,
}

impl GetShardHeaderResponse {
    pub fn new(headers: Vec<BlockHeader>) -> Self {
        Self { headers }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
}

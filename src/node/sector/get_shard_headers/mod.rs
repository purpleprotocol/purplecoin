// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use libp2p::request_response::ProtocolName;

#[derive(Clone, Debug)]
pub struct GetShardHeaderRequestProtocol {
    // The protocol version of the peer sending the request.
    pub protocol_version: String,

    // The protocol name of the peer sending the request.
    pub protocol_name: String,
}

impl GetShardHeaderRequestProtocol {
    pub fn new(protocol_version: String, protocol_name: String) -> Self {
        Self {
            protocol_version,
            protocol_name,
        }
    }
}

impl ProtocolName for GetShardHeaderRequestProtocol {
    fn protocol_name(&self) -> &[u8] {
        self.protocol_name.as_bytes()
    }
}

pub use codec::GetShardHeaderRequestCodec;
pub use payload::{GetShardHeaderRequest, GetShardHeaderResponse};

mod codec;
mod payload;

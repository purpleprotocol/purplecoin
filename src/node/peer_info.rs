// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::consensus::{Money, SECTORS};
use bincode::{Decode, Encode};
use libp2p::PeerId;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PeerInfo {
    /// String peer id
    pub(crate) id: String,

    /// Internal parsed peer id
    #[serde(skip)]
    pub(crate) internal_id: Option<PeerId>,

    /// Node startup time
    pub(crate) startup_time: i64,

    /// Minimum fee for relaying a transaction
    pub(crate) min_relay_fee: Money,

    /// Map of sectors we are listening to
    pub(crate) listening_sectors: [bool; SECTORS],
}

impl Encode for PeerInfo {
    fn encode<E: bincode::enc::Encoder>(
        &self,
        encoder: &mut E,
    ) -> core::result::Result<(), bincode::error::EncodeError> {
        bincode::Encode::encode(&self.id, encoder)?;
        bincode::Encode::encode(&self.startup_time, encoder)?;
        bincode::Encode::encode(&self.min_relay_fee, encoder)?;
        bincode::Encode::encode(&self.listening_sectors, encoder)?;

        Ok(())
    }
}

impl Decode for PeerInfo {
    fn decode<D: bincode::de::Decoder>(
        decoder: &mut D,
    ) -> core::result::Result<Self, bincode::error::DecodeError> {
        let id = bincode::Decode::decode(decoder)?;
        let parsed_id_bytes = bs58::decode(&id)
            .into_vec()
            .map_err(|_| bincode::error::DecodeError::OtherString("invalid peer id".to_owned()))?;
        let internal_id = Some(PeerId::from_bytes(&parsed_id_bytes).map_err(|_| {
            bincode::error::DecodeError::OtherString("invalid internal peer id".to_owned())
        })?);

        Ok(Self {
            id,
            internal_id,
            startup_time: bincode::Decode::decode(decoder)?,
            min_relay_fee: bincode::Decode::decode(decoder)?,
            listening_sectors: bincode::Decode::decode(decoder)?,
        })
    }
}

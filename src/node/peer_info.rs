// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::consensus::{Money, SECTORS, SHARDS_PER_SECTOR};
use bincode::{Decode, Encode};
use bitvec::prelude::*;
use libp2p::PeerId;
use serde::{Deserialize, Serialize};
use serde_big_array::BigArray;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
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

    /// Map of shards we are listening to
    #[serde(with = "BigArray")]
    pub(crate) listening_shards: [bool; SHARDS_PER_SECTOR * SECTORS],
}

impl Encode for PeerInfo {
    fn encode<E: bincode::enc::Encoder>(
        &self,
        encoder: &mut E,
    ) -> core::result::Result<(), bincode::error::EncodeError> {
        bincode::Encode::encode(&self.id, encoder)?;
        bincode::Encode::encode(&self.startup_time, encoder)?;
        bincode::Encode::encode(&self.min_relay_fee, encoder)?;

        // Encode listening sectors and listening shards as bitmaps
        // over the wire. Reducing the size of the flags from 272 bytes
        // to 34 bytes.
        let mut sectors_bitvec = bitvec![u8, Lsb0;];
        let mut shards_bitvec = bitvec![u8, Lsb0;];
        sectors_bitvec.extend(self.listening_sectors.iter());
        shards_bitvec.extend(self.listening_shards.iter());
        let sectors_bitmap_buf: [u8; SECTORS / 8] =
            sectors_bitvec.as_raw_slice().try_into().unwrap();
        let shards_bitmap_buf: [u8; SHARDS_PER_SECTOR * SECTORS / 8] =
            shards_bitvec.as_raw_slice().try_into().unwrap();

        bincode::Encode::encode(&sectors_bitmap_buf, encoder)?;
        bincode::Encode::encode(&shards_bitmap_buf, encoder)?;

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
            listening_sectors: {
                let listening_sectors_buf: [u8; SECTORS / 8] = bincode::Decode::decode(decoder)?;
                let bitvec = BitVec::<_, Lsb0>::from_slice(&listening_sectors_buf);
                let mut listening_sectors = [false; SECTORS];

                for (i, val) in bitvec.iter().by_vals().enumerate() {
                    listening_sectors[i] = val;
                }

                listening_sectors
            },
            listening_shards: {
                let listening_shards_buf: [u8; SHARDS_PER_SECTOR * SECTORS / 8] =
                    bincode::Decode::decode(decoder)?;
                let bitvec = BitVec::<_, Lsb0>::from_slice(&listening_shards_buf);
                let mut listening_shards = [false; SHARDS_PER_SECTOR * SECTORS];

                for (i, val) in bitvec.iter().by_vals().enumerate() {
                    listening_shards[i] = val;
                }

                listening_shards
            },
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_encodes_and_decodes() {
        let peer_info = PeerInfo {
            id: "12D3KooWMeMrSkLtuTLBa2KBBiRXZiwzFJV23SX2v1oFcgMexqs9".to_owned(),
            internal_id: None,
            startup_time: 0,
            min_relay_fee: 120,
            listening_sectors: [
                true, false, false, false, false, false, false, false, false, false, false, false,
                false, false, false, false,
            ],
            listening_shards: [true; 256],
        };
        let mut oracle: PeerInfo =
            crate::codec::decode(&crate::codec::encode_to_vec(&peer_info).unwrap()).unwrap();
        oracle.internal_id = None;

        assert_eq!(peer_info, oracle);
    }
}

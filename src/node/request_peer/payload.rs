use crate::node::peer_info::PeerInfo;
use bincode::{Decode, Encode};

/// Request peer info from a node after identify protocol handshake
#[derive(Clone, Debug, Encode, Decode, Default)]
pub struct PeerInfoRequest;

/// Response to a peer info request
#[derive(Clone, Debug, Encode, Decode)]
pub struct PeerInfoResponse {
    /// Peer info requested
    pub(crate) peer_info: PeerInfo,
}

impl PeerInfoResponse {
    pub fn new(peer_info: PeerInfo) -> Self {
        Self { peer_info }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_response() {
        let mut listening_shards = [false; 256];
        listening_shards[0] = true;
        listening_shards[1] = true;
        listening_shards[2] = true;
        listening_shards[3] = true;
        listening_shards[6] = true;
        listening_shards[8] = true;
        listening_shards[247] = true;
        listening_shards[252] = true;
        let peer_info = PeerInfo {
            id: "12D3KooWMeMrSkLtuTLBa2KBBiRXZiwzFJV23SX2v1oFcgMexqs9".to_owned(),
            internal_id: None,
            startup_time: 0,
            min_relay_fee: 120,
            listening_sectors: [
                true, false, false, false, false, false, false, false, false, false, false, false,
                false, false, false, true,
            ],
            listening_shards,
        };
        let new_response = PeerInfoResponse::new(peer_info);
        let mut buf = crate::codec::encode_to_vec(&new_response).unwrap();

        assert_eq!(
            buf,
            [
                52, 49, 50, 68, 51, 75, 111, 111, 87, 77, 101, 77, 114, 83, 107, 76, 116, 117, 84,
                76, 66, 97, 50, 75, 66, 66, 105, 82, 88, 90, 105, 119, 122, 70, 74, 86, 50, 51, 83,
                88, 50, 118, 49, 111, 70, 99, 103, 77, 101, 120, 113, 115, 57, 0, 240, 1, 128, 79,
                1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 128, 16
            ]
        );
    }

    #[test]
    fn test_decode_response() {
        let buf = vec![
            52, 49, 50, 68, 51, 75, 111, 111, 87, 77, 101, 77, 114, 83, 107, 76, 116, 117, 84, 76,
            66, 97, 50, 75, 66, 66, 105, 82, 88, 90, 105, 119, 122, 70, 74, 86, 50, 51, 83, 88, 50,
            118, 49, 111, 70, 99, 103, 77, 101, 120, 113, 115, 57, 0, 240, 1, 128, 79, 1, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 16,
        ];
        let decoded: PeerInfoResponse = crate::codec::decode(&buf).unwrap();

        assert_eq!(
            decoded.peer_info.id,
            "12D3KooWMeMrSkLtuTLBa2KBBiRXZiwzFJV23SX2v1oFcgMexqs9".to_owned()
        );
        assert_eq!(decoded.peer_info.startup_time, 0);
        assert_eq!(decoded.peer_info.min_relay_fee, 120);
    }
}

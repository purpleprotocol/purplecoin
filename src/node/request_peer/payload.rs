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
    use bincode;

    #[test]
    fn test_encode_request() {
        let new_request = PeerInfoRequest::default();
        let mut buf = [0u8; 8];
        bincode::encode_into_slice(&new_request, &mut buf, bincode::config::standard()).unwrap();

        assert_eq!(buf, [0u8; 8]);
    }

    #[test]
    fn test_decode_request() {
        let buf = [0u8; 8];
        let (_, _): (PeerInfoRequest, usize) =
            bincode::decode_from_slice(&buf, bincode::config::standard()).unwrap();
    }

    #[test]
    fn test_encode_response() {
        let peer_info = PeerInfo {
            id: "12D3KooWMeMrSkLtuTLBa2KBBiRXZiwzFJV23SX2v1oFcgMexqs9".to_owned(),
            internal_id: None,
            startup_time: 0,
            min_relay_fee: 120,
            listening_sectors: [
                true, false, false, false, false, false, false, false, false, false, false, false,
                false, false, false, false,
            ],
        };
        let new_response = PeerInfoResponse::new(peer_info);
        let mut buf = [0u8; 256];
        bincode::encode_into_slice(&new_response, &mut buf, bincode::config::standard()).unwrap();

        assert_eq!(
            buf,
            [
                52, 49, 50, 68, 51, 75, 111, 111, 87, 77, 101, 77, 114, 83, 107, 76, 116, 117, 84,
                76, 66, 97, 50, 75, 66, 66, 105, 82, 88, 90, 105, 119, 122, 70, 74, 86, 50, 51, 83,
                88, 50, 118, 49, 111, 70, 99, 103, 77, 101, 120, 113, 115, 57, 0, 240, 16, 1, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0
            ]
        );
    }

    #[test]
    fn test_decode_response() {
        let buf = [
            52, 49, 50, 68, 51, 75, 111, 111, 87, 77, 101, 77, 114, 83, 107, 76, 116, 117, 84, 76,
            66, 97, 50, 75, 66, 66, 105, 82, 88, 90, 105, 119, 122, 70, 74, 86, 50, 51, 83, 88, 50,
            118, 49, 111, 70, 99, 103, 77, 101, 120, 113, 115, 57, 0, 240, 16, 1, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ];
        let (decoded, _): (PeerInfoResponse, usize) =
            bincode::decode_from_slice(&buf, bincode::config::standard()).unwrap();

        assert_eq!(
            decoded.peer_info.id,
            "12D3KooWMeMrSkLtuTLBa2KBBiRXZiwzFJV23SX2v1oFcgMexqs9".to_owned()
        );
        assert_eq!(decoded.peer_info.startup_time, 0);
        assert_eq!(decoded.peer_info.min_relay_fee, 120);
    }
}

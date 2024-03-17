use libp2p::request_response::ProtocolName;

/// The protocol request struct.
/// Contains the protocol version of the peer sending the request.
#[derive(Clone, Debug)]
pub struct PeerInfoRequestProtocol {
    // The protocol version of the peer sending the request.
    pub protocol_version: String,

    // The protocol name of the peer sending the request.
    pub protocol_name: String,
}

impl PeerInfoRequestProtocol {
    pub fn new(protocol_version: String, protocol_name: String) -> Self {
        Self {
            protocol_version,
            protocol_name,
        }
    }
}

impl ProtocolName for PeerInfoRequestProtocol {
    fn protocol_name(&self) -> &[u8] {
        self.protocol_name.as_bytes()
    }
}

pub use codec::PeerInfoRequestCodec;
pub use payload::{PeerInfoRequest, PeerInfoResponse};

mod codec;
mod payload;

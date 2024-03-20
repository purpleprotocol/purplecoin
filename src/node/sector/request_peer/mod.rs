/// The protocol request struct.
/// Contains the protocol version of the peer sending the request.
#[derive(Clone, Debug)]
pub struct PeerInfoRequestProtocol {
    // The protocol name and version of the peer sending the request.
    pub protocol_name_and_version: String,
}

impl PeerInfoRequestProtocol {
    pub fn new(protocol_name_and_version: String) -> Self {
        Self {
            protocol_name_and_version,
        }
    }
}

impl AsRef<str> for PeerInfoRequestProtocol {
    fn as_ref(&self) -> &str {
        self.protocol_name_and_version.as_str()
    }
}

pub use codec::PeerInfoRequestCodec;
pub use payload::{PeerInfoRequest, PeerInfoResponse};

mod codec;
mod payload;

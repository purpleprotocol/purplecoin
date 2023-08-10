// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use libp2p::gossipsub;
use libp2p::identity::{Keypair, PublicKey};
use libp2p::request_response::ProtocolSupport;
use libp2p::swarm::NetworkBehaviour;
use libp2p::{
    identify,
    kad::{self, store},
    ping,
};
use libp2p::{request_response, PeerId};
use tarpc::tokio_util::time::delay_queue::Key;

use crate::node::request_peer::{
    PeerInfoRequest, PeerInfoRequestCodec, PeerInfoRequestProtocol, PeerInfoResponse,
};

#[derive(NetworkBehaviour)]
#[behaviour(out_event = "SectorEvent")]
pub struct SectorBehaviour {
    identify: identify::Behaviour,
    ping: ping::Behaviour,
    pub gossipsub: gossipsub::Behaviour,
    pub kademlia: kad::Kademlia<store::MemoryStore>,
    pub peer_request: request_response::Behaviour<PeerInfoRequestCodec>,
}

impl SectorBehaviour {
    fn build_identify_behaviour(local_key: &PublicKey) -> identify::Behaviour {
        let identify_config = identify::Config::new("purplecoin/0.1.0".into(), local_key.clone());
        identify::Behaviour::new(identify_config)
    }

    fn build_ping_behaviour() -> ping::Behaviour {
        let ping_config = ping::Config::default();
        ping::Behaviour::new(ping_config)
    }

    fn build_kad_behaviour(peer_id: &PeerId) -> kad::Kademlia<store::MemoryStore> {
        let store = store::MemoryStore::new(*peer_id);
        let kad_config = kad::KademliaConfig::default();
        kad::Kademlia::with_config(*peer_id, store, kad_config)
    }

    fn build_gossip_behaviour(local_key: &Keypair) -> gossipsub::Behaviour {
        let message_authenticity = gossipsub::MessageAuthenticity::Signed(local_key.clone());
        let gossipsub_config = gossipsub::Config::default();
        gossipsub::Behaviour::new(message_authenticity, gossipsub_config).unwrap()
    }

    fn build_peer_request_behaviour() -> request_response::Behaviour<PeerInfoRequestCodec> {
        let peer_request_codec = PeerInfoRequestCodec;
        let peer_request_protocol = vec![(
            PeerInfoRequestProtocol::new("0.1.0".to_string(), "/purplecoin/peer_info/".to_string()),
            ProtocolSupport::Full,
        )];
        request_response::Behaviour::new(
            peer_request_codec,
            peer_request_protocol,
            request_response::Config::default(),
        )
    }

    pub fn new(local_key: &Keypair, local_pbk: &PublicKey) -> Self {
        let identify_behavior = SectorBehaviour::build_identify_behaviour(local_pbk);
        let ping_behavior = SectorBehaviour::build_ping_behaviour();
        let kademlia_behavior = SectorBehaviour::build_kad_behaviour(&local_pbk.into());
        let gossip_behaviour = SectorBehaviour::build_gossip_behaviour(local_key);
        let peer_request_behaviour = SectorBehaviour::build_peer_request_behaviour();

        Self {
            identify: identify_behavior,
            ping: ping_behavior,
            kademlia: kademlia_behavior,
            peer_request: peer_request_behaviour,
            gossipsub: gossip_behaviour,
        }
    }
}

pub enum SectorEvent {
    Identify(identify::Event),
    Ping(ping::Event),
    Kademlia(kad::KademliaEvent),
    PeerRequest(request_response::Event<PeerInfoRequest, PeerInfoResponse>),
    Gossip(gossipsub::Event),
}

impl From<identify::Event> for SectorEvent {
    fn from(other: identify::Event) -> Self {
        Self::Identify(other)
    }
}

impl From<ping::Event> for SectorEvent {
    fn from(other: ping::Event) -> Self {
        Self::Ping(other)
    }
}

impl From<kad::KademliaEvent> for SectorEvent {
    fn from(other: kad::KademliaEvent) -> Self {
        Self::Kademlia(other)
    }
}

impl From<request_response::Event<PeerInfoRequest, PeerInfoResponse>> for SectorEvent {
    fn from(other: request_response::Event<PeerInfoRequest, PeerInfoResponse>) -> Self {
        Self::PeerRequest(other)
    }
}

impl From<gossipsub::Event> for SectorEvent {
    fn from(other: gossipsub::Event) -> Self {
        Self::Gossip(other)
    }
}

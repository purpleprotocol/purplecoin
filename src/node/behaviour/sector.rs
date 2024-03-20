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
    mdns, ping, relay,
};
use libp2p::{request_response, PeerId};
use std::fmt;
use tarpc::tokio_util::time::delay_queue::Key;

use crate::node::sector::request_peer::{
    PeerInfoRequest, PeerInfoRequestCodec, PeerInfoRequestProtocol, PeerInfoResponse,
};

#[derive(NetworkBehaviour)]
#[behaviour(out_event = "SectorEvent")]
pub struct SectorBehaviour {
    relay_client: relay::client::Behaviour,
    identify: identify::Behaviour,
    ping: ping::Behaviour,
    mdns: mdns::tokio::Behaviour,
    pub gossipsub: gossipsub::Behaviour,
    pub kademlia: kad::Behaviour<kad::store::MemoryStore>,
    pub peer_request: request_response::Behaviour<PeerInfoRequestCodec>,
}

impl SectorBehaviour {
    fn build_identify_behaviour(local_key: &PublicKey) -> identify::Behaviour {
        let identify_config = identify::Config::new(
            format!("xpu/{}", env!("CARGO_PKG_VERSION")),
            local_key.clone(),
        );
        identify::Behaviour::new(identify_config)
    }

    fn build_ping_behaviour() -> ping::Behaviour {
        let ping_config = ping::Config::default();
        ping::Behaviour::new(ping_config)
    }

    fn build_mdns_behaviour(peer_id: PeerId) -> mdns::tokio::Behaviour {
        mdns::tokio::Behaviour::new(mdns::Config::default(), peer_id).expect("mdns error")
    }

    fn build_kad_behaviour(peer_id: PeerId) -> kad::Behaviour<kad::store::MemoryStore> {
        let store = store::MemoryStore::new(peer_id);
        let kad_config = kad::Config::default();
        kad::Behaviour::with_config(peer_id, store, kad_config)
    }

    fn build_gossip_behaviour(local_key: &Keypair) -> gossipsub::Behaviour {
        let message_authenticity = gossipsub::MessageAuthenticity::Signed(local_key.clone());
        let gossipsub_config = gossipsub::Config::default();
        gossipsub::Behaviour::new(message_authenticity, gossipsub_config).expect("gossipsub error")
    }

    fn build_peer_request_behaviour() -> request_response::Behaviour<PeerInfoRequestCodec> {
        let peer_request_codec = PeerInfoRequestCodec;
        let peer_request_protocol = vec![(
            PeerInfoRequestProtocol::new("/xpu/peer_info/0.1".to_string()),
            ProtocolSupport::Full,
        )];
        request_response::Behaviour::with_codec(
            peer_request_codec,
            peer_request_protocol,
            request_response::Config::default(),
        )
    }

    pub fn new(
        relay_client: relay::client::Behaviour,
        local_key: &Keypair,
        local_pbk: &PublicKey,
    ) -> Self {
        let identify = Self::build_identify_behaviour(local_pbk);
        let ping = Self::build_ping_behaviour();
        let mdns = Self::build_mdns_behaviour(local_pbk.into());
        let kademlia = Self::build_kad_behaviour(local_pbk.into());
        let gossipsub = Self::build_gossip_behaviour(local_key);
        let peer_request = Self::build_peer_request_behaviour();

        Self {
            relay_client,
            identify,
            ping,
            mdns,
            gossipsub,
            kademlia,
            peer_request,
        }
    }
}

#[derive(Debug)]
pub enum SectorEvent {
    Identify(identify::Event),
    Ping(ping::Event),
    Mdns(mdns::Event),
    Kademlia(kad::Event),
    RelayClient(relay::client::Event),
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

impl From<mdns::Event> for SectorEvent {
    fn from(other: mdns::Event) -> Self {
        Self::Mdns(other)
    }
}

impl From<kad::Event> for SectorEvent {
    fn from(other: kad::Event) -> Self {
        Self::Kademlia(other)
    }
}

impl From<relay::client::Event> for SectorEvent {
    fn from(other: relay::client::Event) -> Self {
        Self::RelayClient(other)
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

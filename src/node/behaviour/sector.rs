// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use libp2p::PeerId;
use libp2p::identity::PublicKey;
use libp2p::swarm::NetworkBehaviour;
use libp2p::{identify, ping, kad::{self, store}};

#[derive(NetworkBehaviour)]
#[behaviour(out_event = "SectorEvent")]
pub struct SectorBehaviour {
    identify: identify::Behaviour,
    ping: ping::Behaviour,
    pub kademlia: kad::Kademlia<store::MemoryStore>,
}

impl SectorBehaviour {
    pub fn new(local_pbk: &PublicKey) -> Self {
        let identify_config = identify::Config::new("purplecoin/0.1.0".into(), local_pbk.clone());
        let identify_behavior = identify::Behaviour::new(identify_config);
        let ping_config = ping::Config::default();
        let ping_behavior = ping::Behaviour::new(ping_config);
        let peer_id = PeerId::from(local_pbk.clone());
        let kademlia_store = store::MemoryStore::new(peer_id.clone());
        let kademlia_behavior = kad::Kademlia::new(peer_id, kademlia_store);

        Self {
            identify: identify_behavior,
            ping: ping_behavior,
            kademlia: kademlia_behavior,
        }
    }
}


pub enum SectorEvent {
    Identify(identify::Event),
    Ping(ping::Event),
    Kademlia(kad::KademliaEvent),
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
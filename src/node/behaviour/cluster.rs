// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use libp2p::identity::PublicKey;
use libp2p::swarm::NetworkBehaviour;
use libp2p::{identify, ping};

#[derive(NetworkBehaviour)]
#[behaviour(out_event = "ClusterEvent")]
pub struct ClusterBehaviour {
    identify: identify::Behaviour,
    ping: ping::Behaviour,
}

impl ClusterBehaviour {
    pub fn new(local_pbk: &PublicKey) -> Self {
        let identify_config = identify::Config::new("purplecoin/0.1.0".into(), local_pbk.clone());
        let identify_behavior = identify::Behaviour::new(identify_config);
        let ping_config = ping::Config::default();
        let ping_behavior = ping::Behaviour::new(ping_config);

        Self {
            identify: identify_behavior,
            ping: ping_behavior,
        }
    }
}

pub enum ClusterEvent {
    Identify(identify::Event),
    Ping(ping::Event),
}

impl From<identify::Event> for ClusterEvent {
    fn from(other: identify::Event) -> Self {
        Self::Identify(other)
    }
}

impl From<ping::Event> for ClusterEvent {
    fn from(other: ping::Event) -> Self {
        Self::Ping(other)
    }
}

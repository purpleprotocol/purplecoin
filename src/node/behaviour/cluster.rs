// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use libp2p::{identify, ping, NetworkBehaviour};

#[derive(NetworkBehaviour)]
#[behaviour(out_event = "ClusterEvent")]
pub struct ClusterBehaviour {
    identify: identify::Identify,
    ping: ping::Behaviour,
}

pub enum ClusterEvent {
    Identify(identify::IdentifyEvent),
    Ping(ping::Event),
}

impl From<identify::IdentifyEvent> for ClusterEvent {
    fn from(other: identify::IdentifyEvent) -> Self {
        Self::Identify(other)
    }
}

impl From<ping::Event> for ClusterEvent {
    fn from(other: ping::Event) -> Self {
        Self::Ping(other)
    }
}

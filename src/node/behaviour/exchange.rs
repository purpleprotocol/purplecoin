// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use libp2p::swarm::NetworkBehaviour;
use libp2p::{identify, ping};

#[derive(NetworkBehaviour)]
#[behaviour(out_event = "ExchangeEvent")]
pub struct ExchangeBehaviour {
    identify: identify::Behaviour,
    ping: ping::Behaviour,
}

pub enum ExchangeEvent {
    Identify(identify::Event),
    Ping(ping::Event),
}

impl From<identify::Event> for ExchangeEvent {
    fn from(other: identify::Event) -> Self {
        Self::Identify(other)
    }
}

impl From<ping::Event> for ExchangeEvent {
    fn from(other: ping::Event) -> Self {
        Self::Ping(other)
    }
}

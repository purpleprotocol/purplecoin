// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::backend::disk::DiskBackend;
use crate::chain::*;
use crate::node::behaviour::*;
use crate::node::peer_info::PeerInfo;
use futures::*;
use libp2p::{
    core::upgrade,
    floodsub::{self, Floodsub, FloodsubEvent},
    identity,
    mdns::MdnsEvent,
    mplex, noise, ping,
    swarm::{SwarmBuilder, SwarmEvent},
    tcp, Multiaddr, NetworkBehaviour, PeerId, Swarm, Transport,
};
pub use mempool::*;
use parking_lot::RwLock;
pub use rpc::*;
use std::collections::HashMap;
use triomphe::Arc;

/// Read-only reference to the node
pub struct Node<'a, B: PowChainBackend<'a> + ShardBackend<'a>> {
    chain: Chain<'a, B>,
    peer_info: PeerInfo,
    peer_info_table: HashMap<PeerId, PeerInfo>,
    sector_swarm: Swarm<SectorBehaviour>,
    exchange_swarm: Swarm<ExchangeBehaviour>,
    cluster_swarm: Swarm<ClusterBehaviour>,
    chain_config: Arc<ChainConfig>,
    shards: Arc<HashMap<u8, Option<Arc<Shard<'a, DiskBackend<'a>>>>>>,
}

impl<'a, B: PowChainBackend<'a> + ShardBackend<'a>> Node<'a, B> {
    pub async fn run(mut self) {
        loop {
            tokio::select! {
                sector_event = self.sector_swarm.next() => unimplemented!(),
                exchange_event = self.exchange_swarm.next() => unimplemented!(),
                cluster_event = self.cluster_swarm.next() => unimplemented!(),
            }
        }
    }
}

mod behaviour;
mod mempool;
mod peer_info;
mod rpc;

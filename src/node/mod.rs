// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
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
    identity::{self, ed25519::SecretKey, Keypair}, ping, identify,
    swarm::{SwarmBuilder, SwarmEvent},
    Multiaddr, PeerId, Swarm, Transport, tcp, noise, mplex,
};
pub use mempool::*;
use parking_lot::RwLock;
pub use rpc::*;
use log::*;
use std::collections::HashMap;
use triomphe::Arc;

/// Read-only reference to the node
pub struct Node<'a, B: PowChainBackend<'a> + ShardBackend<'a>> {
    chain: Chain<'a, B>,
    peer_info: PeerInfo,
    peer_info_table: Arc<HashMap<PeerId, PeerInfo>>,
    sector_swarm: Swarm<SectorBehaviour>,
    exchange_swarm: Swarm<ExchangeBehaviour>,
    cluster_swarm: Swarm<ClusterBehaviour>,
    chain_config: Arc<ChainConfig>,
    shards: Arc<HashMap<u8, Option<Arc<Shard<'a, DiskBackend<'a>>>>>>,
}


impl<'a, B: PowChainBackend<'a> + ShardBackend<'a>> Node<'a, B> {

    pub fn new(
        chain: Chain<'a, B>,
        chain_config: Arc<ChainConfig>,
    ) -> Self {
        // TODO: Add secret key bytes to settings
        let local_pk = Keypair::generate_ed25519();
        let local_pbk = local_pk.public();
        let local_peer_id = PeerId::from(local_pbk.clone());

        // Sector swarm
        let sector_behaviour = SectorBehaviour::new(&local_pbk);
        let swarm_transport = tcp::tokio::Transport::new(tcp::Config::default())
            .upgrade(upgrade::Version::V1)
            .authenticate(noise::Config::new(&local_pk).unwrap())
            .multiplex(mplex::MplexConfig::default())
            .boxed();
        let mut sector_swarm = SwarmBuilder::with_tokio_executor(swarm_transport, sector_behaviour, local_peer_id).build();

        sector_swarm.listen_on("/ip4/0.0.0.0/tcp/8080".parse().unwrap()).unwrap();

        // Exchange swarm
        let exchange_behaviour = ExchangeBehaviour::new(&local_pbk);
        let exchange_transport = tcp::tokio::Transport::new(tcp::Config::default())
            .upgrade(upgrade::Version::V1)
            .authenticate(noise::Config::new(&local_pk).unwrap())
            .multiplex(mplex::MplexConfig::default())
            .boxed();
        let exchange_swarm = SwarmBuilder::with_tokio_executor(exchange_transport, exchange_behaviour, local_peer_id).build();

        // Cluster swarm
        let cluster_behaviour = ClusterBehaviour::new(&local_pbk);
        let cluster_transport = tcp::tokio::Transport::new(tcp::Config::default())
            .upgrade(upgrade::Version::V1)
            .authenticate(noise::Config::new(&local_pk).unwrap())
            .multiplex(mplex::MplexConfig::default())
            .boxed();
        let cluster_swarm = SwarmBuilder::with_tokio_executor(cluster_transport, cluster_behaviour, local_peer_id).build();

        let peer_info = PeerInfo {
            id: local_peer_id.to_string(),
            internal_id: Some(local_peer_id),
            startup_time: 0,  // TODO: Add correct startup time
            min_relay_fee: 0, // TODO: Add correct min relay fee
            listening_sectors: [true; 16],  // TODO: Add correct listening sectors
        };

        Self {
            chain,
            peer_info,
            peer_info_table: Arc::new(HashMap::new()),
            sector_swarm,
            exchange_swarm,
            cluster_swarm,
            chain_config,
            shards: Arc::new(HashMap::new()),  // TODO: Initiate correct shards
        }
    }


    pub async fn run(mut self) {
        loop {
            tokio::select! {
                sector_event = self.sector_swarm.select_next_some() => match sector_event {
                    SwarmEvent::NewListenAddr { address, .. } => { info!("Node listing on {}", address); }
                    SwarmEvent::Behaviour(SectorEvent::Identify(event)) => match event {
                        identify::Event::Received { peer_id, info, .. } => {
                            info!("Received identify event from {}", peer_id);
                            for addr in info.listen_addrs {
                                self.sector_swarm.behaviour_mut().kademlia.add_address(&peer_id, addr);
                            }
                        }
                        _ => ()
                    }
                    _ => ()
                },
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

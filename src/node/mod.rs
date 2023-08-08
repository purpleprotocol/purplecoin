// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::{Chain, ChainConfig, PowChainBackend, Shard, ShardBackend};
use crate::node::behaviour::{ClusterBehaviour, ExchangeBehaviour, SectorBehaviour, SectorEvent};
use crate::node::peer_info::PeerInfo;
use crate::settings::SETTINGS;
use crate::{chain::backend::disk::DiskBackend, node::request_peer::PeerInfoResponse};
use blake3::Hash;
use futures::*;
use libp2p::yamux;
use libp2p::{
    core::upgrade,
    identify,
    identity::{self, ed25519::SecretKey, Keypair},
    noise, ping, request_response,
    swarm::{SwarmBuilder, SwarmEvent},
    tcp, Multiaddr, PeerId, Swarm, Transport,
};
use log::*;
pub use mempool::*;
use parking_lot::RwLock;
pub use rpc::*;
use std::collections::HashMap;
use std::sync::Mutex;
use triomphe::Arc;

use self::request_peer::PeerInfoRequest;

type PeerInfoTable = HashMap<PeerId, PeerInfo>;

/// Read-only reference to the node
pub struct Node<'a, B: PowChainBackend<'a> + ShardBackend<'a>> {
    chain: Chain<'a, B>,
    peer_info: PeerInfo,
    peer_info_table: Arc<Mutex<PeerInfoTable>>,
    sector_swarm: Swarm<SectorBehaviour>,
    exchange_swarm: Swarm<ExchangeBehaviour>,
    cluster_swarm: Swarm<ClusterBehaviour>,
    chain_config: Arc<ChainConfig>,
    shards: Arc<HashMap<u8, Option<Arc<Shard<'a, DiskBackend<'a>>>>>>,
}

impl<'a, B: PowChainBackend<'a> + ShardBackend<'a>> Node<'a, B> {
    pub fn new(chain: Chain<'a, B>, chain_config: Arc<ChainConfig>) -> Self {
        // TODO: Add secret key bytes to settings
        let local_pk = Keypair::generate_ed25519();
        let local_pbk = local_pk.public();
        let local_peer_id = PeerId::from(local_pbk.clone());

        // Sector swarm
        let sector_behaviour = SectorBehaviour::new(&local_pk, &local_pbk);
        let swarm_transport = tcp::tokio::Transport::new(tcp::Config::default())
            .upgrade(upgrade::Version::V1)
            .authenticate(noise::Config::new(&local_pk).unwrap())
            .multiplex(yamux::Config::default())
            .boxed();
        let mut sector_swarm =
            SwarmBuilder::with_tokio_executor(swarm_transport, sector_behaviour, local_peer_id)
                .build();

        // TODO: Add listener address to settings
        let addrs = format!("/ip4/0.0.0.0/tcp/{}", SETTINGS.network.listen_port_testnet);
        sector_swarm.listen_on(addrs.parse().unwrap()).unwrap();

        // Exchange swarm
        let exchange_behaviour = ExchangeBehaviour::new(&local_pbk);
        let exchange_transport = tcp::tokio::Transport::new(tcp::Config::default())
            .upgrade(upgrade::Version::V1)
            .authenticate(noise::Config::new(&local_pk).unwrap())
            .multiplex(yamux::Config::default())
            .boxed();
        let exchange_swarm = SwarmBuilder::with_tokio_executor(
            exchange_transport,
            exchange_behaviour,
            local_peer_id,
        )
        .build();

        // Cluster swarm
        let cluster_behaviour = ClusterBehaviour::new(&local_pbk);
        let cluster_transport = tcp::tokio::Transport::new(tcp::Config::default())
            .upgrade(upgrade::Version::V1)
            .authenticate(noise::Config::new(&local_pk).unwrap())
            .multiplex(yamux::Config::default())
            .boxed();
        let cluster_swarm =
            SwarmBuilder::with_tokio_executor(cluster_transport, cluster_behaviour, local_peer_id)
                .build();

        let peer_info = PeerInfo {
            id: local_peer_id.to_string(),
            internal_id: Some(local_peer_id),
            startup_time: 0,               // TODO: Add correct startup time
            min_relay_fee: 0,              // TODO: Add correct min relay fee
            listening_sectors: [true; 16], // TODO: Add correct listening sectors
        };

        Self {
            chain,
            peer_info,
            peer_info_table: Arc::new(Mutex::new(HashMap::new())),
            sector_swarm,
            exchange_swarm,
            cluster_swarm,
            chain_config,
            shards: Arc::new(HashMap::new()), // TODO: Initiate correct shards
        }
    }

    pub fn bootstrap(&mut self) {
        let peer_id = match &SETTINGS.network.bootstrap_node_peer_id {
            Some(peer_id) => peer_id,
            None => {
                error!("No bootstrap node peer id provided");
                return;
            }
        };

        let addr = match &SETTINGS.network.bootstrap_node_address {
            Some(addr) => addr,
            None => {
                error!("No bootstrap node address provided");
                return;
            }
        };
        self.sector_swarm
            .behaviour_mut()
            .kademlia
            .add_address(&peer_id.parse().unwrap(), addr.parse().unwrap());
    }

    pub async fn run(&mut self) {
        info!("Peer id: {}", self.peer_info.id);
        loop {
            tokio::select! {
                sector_event = self.sector_swarm.select_next_some() => match sector_event {
                    SwarmEvent::NewListenAddr { address, .. } => {
                        info!("Node listing on {}", address);
                    }
                    SwarmEvent::Behaviour(SectorEvent::Identify(event)) =>  match event {
                        identify::Event::Received { peer_id, info, .. } => {
                            info!("Received identify info from {}:{}", peer_id, info.protocol_version);
                            let sector_behaviour = self.sector_swarm.behaviour_mut();
                            for addr in info.listen_addrs {
                                sector_behaviour.kademlia.add_address(&peer_id, addr);
                            }
                            let peer_table_lock = self.peer_info_table.lock().unwrap();
                            if !peer_table_lock.contains_key(&peer_id) {
                                let peer_info_request = PeerInfoRequest::default();
                                sector_behaviour.peer_request.send_request(&peer_id, peer_info_request);
                            }
                        }
                        _ => (),
                    },
                    SwarmEvent::Behaviour(SectorEvent::PeerRequest(event)) => match event {
                        request_response::Event::Message { peer, message } => {
                            match message {
                                request_response::Message::Response { response, .. } => {
                                    let peer_info = response.peer_info;
                                    let mut peer_table_lock = self.peer_info_table.lock().unwrap();
                                    peer_table_lock.insert(peer, peer_info).unwrap();
                                },
                                request_response::Message::Request { request, channel, .. } => {
                                    let sector_behaviour = self.sector_swarm.behaviour_mut();
                                    let response = PeerInfoResponse::new(self.peer_info.clone());
                                    match sector_behaviour.peer_request.send_response(channel, response) {
                                        Ok(_) => (),
                                        Err(err) => error!("Failed to send peer info response: {:?}", err),
                                    };
                                }
                            }
                        }
                        _ => (),
                    }
                    _ => (),
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
mod request_peer;
mod rpc;

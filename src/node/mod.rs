// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use self::request_peer::PeerInfoRequest;
use crate::chain::{
    Chain, ChainConfig, DBInterface, IteratorDirection, PowChainBackend, Shard, ShardBackend,
};
use crate::consensus::{SECTORS, SHARDS_PER_SECTOR};
use crate::node::behaviour::{ClusterBehaviour, ExchangeBehaviour, SectorBehaviour, SectorEvent};
use crate::node::peer_info::PeerInfo;
use crate::settings::SETTINGS;
use crate::{chain::backend::disk::DiskBackend, node::request_peer::PeerInfoResponse};
use async_channel::{unbounded, Receiver, Sender};
use blake3::Hash;
use fancy_regex::Regex;
use futures::{FutureExt, StreamExt};
use libp2p::yamux;
use libp2p::{
    core::upgrade,
    identify,
    identity::{self, ed25519::SecretKey, Keypair},
    kad, mdns, noise, ping, request_response,
    swarm::{SwarmBuilder, SwarmEvent},
    tcp, Multiaddr, PeerId, Swarm, Transport,
};
use log::{debug, error, info};
pub use mempool::*;
use parking_lot::{RwLock, RwLockUpgradableReadGuard};
pub use rpc::*;
use std::collections::HashMap;
use std::str;
use std::string::ToString;
use std::sync::atomic::Ordering;
use tokio::time::{sleep, Duration};
use triomphe::Arc;
use trust_dns_resolver::error::ResolveResult;
use trust_dns_resolver::Resolver;
use trust_dns_resolver::{
    config::{ResolverConfig, ResolverOpts},
    lookup::TxtLookup,
};

type PeerInfoTable = HashMap<PeerId, PeerInfo>;

/// The node identity is stored in the database under this key
const IDENTITY_KEY: &str = "node_keypair";

/// Bootstrap interval
const BOOTSTRAP_INTERVAL: u64 = 60;

pub static mut NODE_INFO: Option<Arc<RwLock<PeerInfo>>> = None;
pub static mut PEER_INFO_TABLE: Option<Arc<RwLock<PeerInfoTable>>> = None;

/// Read-only reference to the node
pub struct Node<B: PowChainBackend + ShardBackend + DBInterface> {
    chain: Chain<B>,
    node_info: Arc<RwLock<PeerInfo>>,
    peer_info_table: Arc<RwLock<PeerInfoTable>>,
    sector_swarm: Swarm<SectorBehaviour>,
    exchange_swarm: Swarm<ExchangeBehaviour>,
    cluster_swarm: Swarm<ClusterBehaviour>,
}

impl<B: PowChainBackend + ShardBackend + DBInterface> Node<B> {
    pub fn new(chain: Chain<B>) -> Self {
        // Try to fetch existing identity from the database
        // and create one if it doesn't exist.
        let id = match chain
            .backend
            .get::<_, Vec<u8>>(IDENTITY_KEY.as_bytes())
            .expect("db error")
        {
            Some(mut keypair_bytes) =>
            {
                #[allow(deprecated)]
                Keypair::Ed25519(
                    identity::ed25519::Keypair::try_from_bytes(&mut keypair_bytes)
                        .expect("db corruption"),
                )
            }
            None => {
                let id: Keypair = Keypair::generate_ed25519();

                // Write generated keypair to database
                let keypair = id.clone().try_into_ed25519().unwrap();
                let id_bytes = keypair.to_bytes().to_vec();
                chain
                    .backend
                    .put(IDENTITY_KEY.as_bytes(), id_bytes)
                    .expect("db error");

                id
            }
        };
        let local_pbk = id.public();
        let local_peer_id = PeerId::from(local_pbk.clone());

        // Sector swarm
        let sector_behaviour = SectorBehaviour::new(&id, &local_pbk);
        let swarm_transport = tcp::tokio::Transport::new(tcp::Config::default())
            .upgrade(upgrade::Version::V1)
            .authenticate(noise::Config::new(&id).unwrap())
            .multiplex(yamux::Config::default())
            .boxed();
        let mut sector_swarm =
            SwarmBuilder::with_tokio_executor(swarm_transport, sector_behaviour, local_peer_id)
                .build();

        let listen_port = match SETTINGS.node.network_name.as_str() {
            "mainnet" => SETTINGS.network.listen_port_mainnet,
            "testnet" => SETTINGS.network.listen_port_testnet,
            "devnet" => SETTINGS.network.listen_port_devnet,
            network => panic!("invalid network name: {network}"),
        };

        let addrs = format!("/ip4/{}/tcp/{}", SETTINGS.network.listen_addr, listen_port);
        sector_swarm
            .listen_on(addrs.parse().expect("Could not parse listener address"))
            .expect("Invalid listener address");

        // Exchange swarm
        let exchange_behaviour = ExchangeBehaviour::new(&local_pbk);
        let exchange_transport = tcp::tokio::Transport::new(tcp::Config::default())
            .upgrade(upgrade::Version::V1)
            .authenticate(noise::Config::new(&id).unwrap())
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
            .authenticate(noise::Config::new(&id).unwrap())
            .multiplex(yamux::Config::default())
            .boxed();
        let cluster_swarm =
            SwarmBuilder::with_tokio_executor(cluster_transport, cluster_behaviour, local_peer_id)
                .build();

        let (listening_sectors, listening_shards) = match (
            SETTINGS.node.sectors_listening.as_ref(),
            SETTINGS.node.shards_listening.as_ref(),
        ) {
            (Some(listening_sectors), Some(listening_shards)) => {
                let mut r1 = [false; SECTORS];
                let mut r2 = [false; SECTORS * SHARDS_PER_SECTOR];

                for id in listening_sectors {
                    r1[*id as usize] = true;
                }

                for id in listening_shards {
                    r2[*id as usize] = true;
                }

                (r1, r2)
            }

            (Some(listening_sectors), None) => {
                let mut r1 = [false; SECTORS];
                let mut r2 = [false; SECTORS * SHARDS_PER_SECTOR];

                for id in listening_sectors {
                    r1[*id as usize] = true;

                    let start_id = *id * SECTORS as u8;
                    for i in start_id..(start_id + SECTORS as u8) {
                        r2[i as usize] = true;
                    }
                }

                (r1, r2)
            }

            _ => ([true; SECTORS], [true; SECTORS * SHARDS_PER_SECTOR]),
        };

        let node_info = Arc::new(RwLock::new(PeerInfo {
            id: local_peer_id.to_string(),
            internal_id: Some(local_peer_id),
            startup_time: crate::global::STARTUP_TIME.load(Ordering::Relaxed),
            min_relay_fee: 0, // TODO: Add correct min relay fee
            listening_sectors,
            listening_shards,
        }));
        let peer_info_table = Arc::new(RwLock::new(HashMap::new()));

        // This is fine since we only write once.
        unsafe {
            NODE_INFO = Some(node_info.clone());
            PEER_INFO_TABLE = Some(peer_info_table.clone());
        }

        Self {
            chain,
            node_info,
            peer_info_table,
            sector_swarm,
            exchange_swarm,
            cluster_swarm,
        }
    }

    pub async fn bootstrap_then_run(&mut self) -> anyhow::Result<()> {
        let (bootstrap_s, bootstrap_r) = unbounded();
        let backend = self.chain.backend.clone();
        let peer_info_table = self.peer_info_table.clone();

        tokio::select! {
            _ = Self::bootstrap(backend, peer_info_table, bootstrap_s) => {}
            _ = self.run(bootstrap_r) => {}
        }

        Ok(())
    }

    pub async fn bootstrap(
        backend: B,
        peer_info_table: Arc<RwLock<PeerInfoTable>>,
        sender: Sender<(PeerId, Multiaddr)>,
    ) {
        loop {
            let num_peers = peer_info_table.read().len();

            // Stop bootstrapping if we have enough peers
            if num_peers > SETTINGS.network.desired_peers as usize {
                sleep(Duration::from_secs(BOOTSTRAP_INTERVAL)).await;
                continue;
            }
            info!("Bootstrapping...");

            let mut required = SETTINGS.network.desired_peers as usize - num_peers;
            let fqdn_regx =
                Regex::new(r"(?=^.{4,253}$)(^((?!-)[a-zA-Z0-9-]{1,63}(?<!-)\.)+[a-zA-Z]{2,63}$)")
                    .unwrap();
            let seeds = match SETTINGS.node.network_name.as_str() {
                "mainnet" => SETTINGS.network.seeds_mainnet.as_slice(),
                "testnet" => SETTINGS.network.seeds_testnet.as_slice(),
                "devnet" => SETTINGS.network.seeds_devnet.as_slice(),
                network => panic!("invalid network name: {network}"),
            };

            let mut peer_ids_and_addrs: Vec<(String, String)> = vec![];

            // First check the database
            {
                let mut db_iter = backend.prefix_iterator::<Vec<String>>(
                    "peer.".as_bytes().to_vec(),
                    IteratorDirection::Forward,
                );

                // TODO: Skip unresponsive peers and ones we are already connected to
                while let Some((k, v)) = db_iter.next() {
                    if required == 0 {
                        break;
                    }

                    let k = unsafe { str::from_utf8_unchecked(k.as_slice()) }.to_owned();
                    let addr = k.split('.').nth(1).unwrap().to_owned();
                    let v = v[0].clone();

                    peer_ids_and_addrs.push((addr, v));
                    required -= 1;
                }
            }

            // Resolve seed nodes if we don't have enough peers
            if peer_ids_and_addrs.len() < SETTINGS.network.desired_peers as usize {
                for s in seeds {
                    let mut to_parse = vec![];
                    if fqdn_regx
                        .is_match(s.as_str())
                        .expect("could not parse dns seed")
                    {
                        // Resolve DNS seed
                        let dns_seeds =
                            resolve_txt_record(s.as_str()).expect("could not resolve dns seed");
                        to_parse.extend(dns_seeds);
                    } else {
                        to_parse.push(s.clone());
                    }

                    for s in to_parse {
                        // Parse peer id and address. Written in settings as `<peer_id>:<address>`
                        let split: Vec<_> = s.split(':').collect();
                        assert!(split.len() == 2, "invalid peer address: {s}");
                        peer_ids_and_addrs.push((split[0].to_string(), split[1].to_string()));
                    }
                }
            }

            for (id, addr) in &peer_ids_and_addrs {
                sender
                    .send((
                        id.parse().expect("invalid peer id"),
                        addr.parse().expect("invalid peer address"),
                    ))
                    .await
                    .expect("channel error");
            }

            if peer_ids_and_addrs.is_empty() {
                info!("Found 0 bootstrap nodes.");
            } else {
                info!(
                    "Found {} bootstrap nodes. Connecting...",
                    peer_ids_and_addrs.len()
                );
            }
            sleep(Duration::from_secs(BOOTSTRAP_INTERVAL)).await;
        }
    }

    pub async fn run(&mut self, bootstrap_r: Receiver<(PeerId, Multiaddr)>) {
        info!("Our node id: {}", self.node_info.read().id);
        loop {
            tokio::select! {
                res = bootstrap_r.recv() => {
                    let (id, addr) = res.expect("channel closed");
                    self.sector_swarm.behaviour_mut().kademlia.add_address(
                        &id,
                        addr.clone(),
                    );
                    self.try_connect_sector(&id, addr);
                }
                sector_event = self.sector_swarm.select_next_some() => match sector_event {
                    SwarmEvent::NewListenAddr { address, .. } => {
                        info!("Node listening on {}", address);
                    }
                    SwarmEvent::Behaviour(SectorEvent::Identify(event)) =>  match event {
                        identify::Event::Received { peer_id, info, .. } => {
                            info!("Received identify info from {}:{}", peer_id, info.protocol_version);
                            let sector_behaviour = self.sector_swarm.behaviour_mut();
                            for addr in info.listen_addrs {
                                sector_behaviour.kademlia.add_address(&peer_id, addr);
                            }
                            let peer_table_lock = self.peer_info_table.read();
                            if !peer_table_lock.contains_key(&peer_id) {
                                let peer_info_request = PeerInfoRequest;
                                sector_behaviour.peer_request.send_request(&peer_id, peer_info_request);
                            }
                        }
                        event => {
                            debug!("Received identify event: {:?}", event);
                        }
                    }
                    SwarmEvent::Behaviour(SectorEvent::PeerRequest(event)) => match event {
                        request_response::Event::Message { peer, message } => {
                            match message {
                                request_response::Message::Response { response, .. } => {
                                    let peer_info = response.peer_info;
                                    let mut peer_table_lock = self.peer_info_table.write();
                                    peer_table_lock.insert(peer, peer_info);
                                },
                                request_response::Message::Request { request, channel, .. } => {
                                    let sector_behaviour = self.sector_swarm.behaviour_mut();
                                    let response = PeerInfoResponse::new(self.node_info.read().clone());
                                    match sector_behaviour.peer_request.send_response(channel, response) {
                                        Ok(_) => (),
                                        Err(err) => error!("Failed to send peer info response: {:?}", err),
                                    };
                                }
                            }
                        }
                        event => {
                            debug!("Received Peer Request event: {:?}", event);
                        }
                    }
                    SwarmEvent::Behaviour(SectorEvent::Mdns(event)) => match event {
                        mdns::Event::Discovered(peers) => {
                            info!("Found {} peers through mdns", peers.len());

                            // Write peers to the database if they don't exist
                            for (peer_id, addr) in peers {
                                let peer_key = format!("peer.{}", peer_id.to_base58());

                                if self.chain.backend.get::<_, String>(&peer_key).unwrap_or(None).is_none() {
                                    info!("Found new peer {} at {}", peer_id.to_base58(), addr);
                                    self.chain.backend.put(peer_key, vec![addr.to_string()]).unwrap_or(());
                                    {
                                        let sector_behaviour = self.sector_swarm.behaviour_mut();
                                        sector_behaviour.kademlia.add_address(&peer_id, addr.clone());
                                    }
                                    self.try_connect_sector(&peer_id, addr);
                                }
                            }
                        }

                        mdns::Event::Expired(_) => ()
                    }
                    SwarmEvent::Behaviour(SectorEvent::Kademlia(event)) => match event {
                        kad::KademliaEvent::RoutingUpdated { peer, is_new_peer, addresses, .. } => {
                            let peer_b58 =  peer.to_base58();
                            info!("Received RoutingUpdated event for peer {} with addresses: {:?}", peer_b58, addresses);
                            let peer_key = format!("peer.{}", peer_b58);

                            if !is_new_peer || self.chain.backend.get::<_, String>(&peer_key).unwrap_or(None).is_none() {
                                let addresses_strings = addresses.iter().map(ToString::to_string).collect::<Vec<_>>();

                                if is_new_peer {
                                    info!("Found new peer {} with addresses {:?}", peer_b58, addresses_strings);
                                } else {
                                    info!("Got new addresses for peer {}: {:?}", peer_b58, addresses_strings);
                                }

                                self.chain.backend.put(peer_key, addresses_strings).unwrap_or(());
                                let sector_behaviour = self.sector_swarm.behaviour_mut();

                                for addr in addresses.iter() {
                                    sector_behaviour.kademlia.add_address(&peer, addr.clone());
                                }
                            }
                        }
                        event => {
                            debug!("Received kademlia event: {:?}", event);
                        }
                    }
                    SwarmEvent::ConnectionEstablished { peer_id, endpoint, .. } => {
                        info!("Connected to peer {} at {}", peer_id.to_base58(), endpoint.get_remote_address());
                    }
                    SwarmEvent::ConnectionClosed { peer_id, endpoint, .. } => {
                        info!("Disconnected from peer {} at {}", peer_id.to_base58(), endpoint.get_remote_address());
                        let peer_table = self.peer_info_table.upgradable_read();

                        // Delete peer from the peer table
                        if peer_table.contains_key(&peer_id) {
                            let mut peer_table = RwLockUpgradableReadGuard::upgrade(peer_table);
                            peer_table.remove(&peer_id);
                        }
                    }
                    event => {
                        debug!("Received event: {:?}", event);
                    },
                },
                exchange_event = self.exchange_swarm.next() => unimplemented!(),
                cluster_event = self.cluster_swarm.next() => unimplemented!(),
            }
        }
    }

    fn try_connect_sector(&mut self, peer_id: &PeerId, addr: Multiaddr) {
        let num_peers = self.peer_info_table.read().len();

        if num_peers > SETTINGS.network.desired_peers as usize
            || self.sector_swarm.is_connected(peer_id)
        {
            return;
        }

        self.sector_swarm.dial(addr);
    }
}

fn resolve_txt_record(fqdn: &str) -> Option<Vec<String>> {
    let resolver = Resolver::new(ResolverConfig::default(), ResolverOpts::default()).unwrap();
    let txt_response = resolver.txt_lookup(fqdn);
    txt_response
        .ok()
        .map(|txt| txt.iter().map(ToString::to_string).collect())
}

mod behaviour;
mod mempool;
mod peer_info;
mod request_peer;
mod rpc;

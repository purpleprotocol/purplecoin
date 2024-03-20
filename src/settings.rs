// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::consensus::SECTORS;
use config::{Config, ConfigError, File};
use lazy_static::lazy_static;
use log::error;
use rand::Rng;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::env;
use std::fs::{metadata, File as FsFile};
use std::hash::Hash;
use std::io::{self, Write};
use struct_field_names_as_array::FieldNamesAsArray;

lazy_static! {
    pub static ref SETTINGS: Settings = Settings::new().unwrap();
}

#[derive(Debug, Serialize, Deserialize, Default, FieldNamesAsArray)]
pub struct Settings {
    /// Network settings.
    pub network: Network,

    /// Node settings.
    pub node: Node,

    /// Miner settings.
    pub miner: Miner,

    /// Cluster deployment settings.
    pub cluster: Cluster,
}

impl Settings {
    pub fn new() -> Result<Self, ConfigError> {
        let mut config_path = dirs::config_dir().unwrap();
        config_path.push("Purplecoin");
        config_path.push("config.toml");
        let default_settings = Settings::default();
        match metadata(config_path.clone()) {
            // Create default configuration
            Err(_) => {
                let settings_str = toml::ser::to_string_pretty(&default_settings).unwrap();

                // Create configuration file
                match FsFile::create(config_path.clone()) {
                    Ok(mut file) => {
                        file.write_all(settings_str.as_bytes()).unwrap_or(());
                    }
                    Err(err) => {
                        // If this fails, do nothing and fall back to envionment variables
                        error!("Failed to create configuration! Reason: {:#?}", err);
                    }
                }
            }
            _ => {} // Do nothing
        }

        let prefix = "purplecoin";
        let env_source: Vec<_> = std::env::vars().collect();
        let mut s = Config::builder().add_source(
            File::with_name(&config_path.into_os_string().into_string().unwrap()).required(false),
        );

        // Set defaults
        let defaults: HashMap<String, HashMap<String, DynamicConfVal>> =
            serde_yaml::from_value(serde_yaml::to_value(&default_settings).unwrap()).unwrap();
        for (k1, inner) in &defaults {
            for (k2, v) in inner {
                match v {
                    DynamicConfVal::String(v) => {
                        s = s.set_default(format!("{k1}.{k2}"), v.as_str())?;
                    }

                    DynamicConfVal::Bool(v) => {
                        s = s.set_default(format!("{k1}.{k2}"), v.to_string())?;
                    }

                    DynamicConfVal::U16(v) => {
                        s = s.set_default(format!("{k1}.{k2}"), v.to_string())?;
                    }

                    DynamicConfVal::Sequence(v) => {
                        s = s.set_default(format!("{k1}.{k2}"), v.clone())?;
                    }

                    DynamicConfVal::Option(v) => {
                        if let Some(v) = v {
                            s = s.set_default(format!("{k1}.{k2}"), v.as_str())?;
                        }
                    }

                    DynamicConfVal::OptionSequence(v) => {
                        if let Some(v) = v {
                            s = s.set_default(format!("{k1}.{k2}"), v.clone())?;
                        }
                    }

                    DynamicConfVal::OptionSequenceByte(v) => {
                        if let Some(v) = v {
                            s = s.set_default(format!("{k1}.{k2}"), v.clone())?;
                        }
                    }
                }
            }
        }

        // Make sure to list these in order
        let settings_modules: Vec<_> = vec![
            Network::FIELD_NAMES_AS_ARRAY,
            Node::FIELD_NAMES_AS_ARRAY,
            Miner::FIELD_NAMES_AS_ARRAY,
            Cluster::FIELD_NAMES_AS_ARRAY,
        ];

        // Gather all possible settings keys
        let possible_keys: HashMap<String, &str> = Settings::FIELD_NAMES_AS_ARRAY
            .iter()
            .enumerate()
            .flat_map(|(i, field)| {
                settings_modules[i].iter().map(|nested| {
                    (
                        format!(
                            "{}_{}_{}",
                            prefix,
                            field.to_owned(),
                            nested.split('_').collect::<Vec<_>>().join("")
                        ),
                        *nested,
                    )
                })
            })
            .collect();

        // Parse env vars manually and set overrides if they exist as the
        // config package `Environment` module seems to behave poorly.
        for (k, v) in &env_source {
            let k = k.to_lowercase();

            if let Some(k_postfix) = possible_keys.get(&k) {
                let mut k: Vec<_> = k.split('_').filter(|x| x != &prefix).collect();
                *k.last_mut().unwrap() = k_postfix;
                let k = k.join(".");

                // Filter empty values
                if v.as_str() == "" {
                    continue;
                }

                s = s.set_override(k, v.as_str())?;
            }
        }

        s.build()?.try_deserialize()
    }

    /// Validates the settings. Panics if settings are invalid.
    pub fn validate(&self) {
        self.network.validate();
        self.node.validate();
        self.miner.validate();
        self.cluster.validate();
    }
}

#[derive(Debug, Serialize, Deserialize, FieldNamesAsArray)]
pub struct Network {
    /// Node listen address.
    #[serde(alias = "listenaddr")]
    pub listen_addr: String,

    /// Which protocols to listen on. Possible values: tcp, quic, and uds.
    #[serde(alias = "useprotocols")]
    pub use_protocols: Vec<String>,

    /// Desired number of peers. 8 by default.
    #[serde(alias = "desiredpeers")]
    pub desired_peers: u16,

    /// Node listen port on mainnet.
    #[serde(alias = "listenportmainnet")]
    pub listen_port_mainnet: u16,

    /// Node listen port on mainnet.
    #[serde(alias = "listenporttestnet")]
    pub listen_port_testnet: u16,

    /// Node listen port on devnet.
    #[serde(alias = "listenportdevnet")]
    pub listen_port_devnet: u16,

    /// Enable RPC.
    #[serde(alias = "rpcenabled")]
    pub rpc_enabled: bool,

    /// RPC listen port on mainnet.
    #[serde(alias = "rpclistenportmainnet")]
    pub rpc_listen_port_mainnet: u16,

    /// RPC listen port on testnet.
    #[serde(alias = "rpclistenporttestnet")]
    pub rpc_listen_port_testnet: u16,

    /// RPC listen port on devnet.
    #[serde(alias = "rpclistenportdevnet")]
    pub rpc_listen_port_devnet: u16,

    /// RPC username.
    #[serde(alias = "rpcusername")]
    pub rpc_username: String,

    /// RPC password.
    #[serde(alias = "rpcpassword")]
    pub rpc_password: String,

    /// DNS seeds for mainnet.
    #[serde(alias = "seedsmainnet")]
    pub seeds_mainnet: Vec<String>,

    /// DNS seeds for testnet.
    #[serde(alias = "seedstestnet")]
    pub seeds_testnet: Vec<String>,

    /// DNS seeds for devnet.
    #[serde(alias = "seedsdevnet")]
    pub seeds_devnet: Vec<String>,
}

impl Default for Network {
    fn default() -> Self {
        Self {
            listen_addr: "0.0.0.0".to_owned(),
            listen_port_mainnet: 8098,
            listen_port_testnet: 8031,
            listen_port_devnet: 8021,
            use_protocols: vec!["tcp".to_owned(), "quic".to_owned()],
            desired_peers: 8,
            rpc_enabled: true,
            rpc_listen_port_mainnet: 8067,
            rpc_listen_port_testnet: 8037,
            rpc_listen_port_devnet: 8027,
            rpc_username: "purplecoin".to_owned(),
            rpc_password: "purplecoin".to_owned(),
            seeds_mainnet: vec!["bootstrap.mainnet.purplecoin.io.".to_owned()],
            seeds_testnet: vec!["bootstrap.testnet.purplecoin.io.".to_owned()],
            seeds_devnet: vec![],
        }
    }
}

impl Network {
    fn validate(&self) {
        assert!(
            self.desired_peers > 0,
            "invalid settings: desiredpeers must be greater than 0"
        );
        assert!(
            !self.use_protocols.is_empty(),
            "invalid settings: no value provided for useprotocols. Possible values: quic, tcp."
        );
        assert!(
            !self
                .use_protocols
                .iter()
                .any(|p| p.as_str() != "quic" && p.as_str() != "tcp"),
            "invalid settings: useprotocols is invalid, possible values: quic, tcp."
        );
        assert!(
            has_unique_elements(&self.use_protocols),
            "invalid settings: useprotocols contains duplicate entries"
        );
    }
}

#[derive(Debug, Serialize, Deserialize, FieldNamesAsArray)]
pub struct Node {
    /// The network name the node is listening on.
    #[serde(alias = "networkname")]
    pub network_name: String,

    /// Sector ids we are listening to. None if we listen to all.
    #[serde(alias = "sectorslistening")]
    pub sectors_listening: Option<HashSet<u8>>,

    /// Shard ids we are listening to. None if we listen to all
    /// shards contained in the sectors we are listening to.
    #[serde(alias = "shardslistening")]
    pub shards_listening: Option<HashSet<u8>>,

    /// Number of transaction verification threads.
    ///
    /// Default is 0 which means the number of cores of the system
    #[serde(alias = "verifierthreads")]
    pub verifier_threads: u16,

    /// Number of threads used for network communication and the RPC interface.
    ///
    /// Default is 0 which means the number of cores of the system
    #[serde(alias = "networkthreads")]
    pub network_threads: u16,

    /// Running in archival mode saves all block headers, transaction and UTXOs.
    #[serde(alias = "archivalmode")]
    pub archival_mode: bool,

    /// If not running in archival mode, we can specify to prune headers.
    /// This implicitly prunes transactions and UTXOs as well.
    #[serde(alias = "pruneheaders")]
    pub prune_headers: bool,

    /// If not running in archival mode, we can specify to prune transactions.
    #[serde(alias = "prunetransactions")]
    pub prune_transactions: bool,

    /// If not running in archival mode, we can specify to prune UTXOs.
    #[serde(alias = "pruneutxos")]
    pub prune_utxos: bool,

    /// Node data directory
    #[serde(alias = "datadir")]
    pub data_dir: String,

    /// If specified, we won't be storing anything to disk. This requires full pruning.
    #[serde(alias = "memoryonly")]
    pub memory_only: bool,

    /// Size in megabytes of the mempool
    #[serde(alias = "mempoolsize")]
    pub mempool_size: u16,

    /// Enable the DHT public bridge.
    #[serde(alias = "enabledhtbridge")]
    pub dht_bridge_enabled: bool,

    /// How many megabytes to allocate to the DHT public bridge.
    #[serde(alias = "dhtbridgestoragemb")]
    pub dht_bridge_storage_mb: u16,

    /// Ignoring any prune settings, UTXOs for the given addresses will be saved.
    #[serde(alias = "saveutxosaddresses")]
    pub save_utxos_addresses: Option<Vec<String>>,

    /// Ignoring any prune settings, UTXOs for the given assets will be saved.
    #[serde(alias = "saveutxosassets")]
    pub save_utxos_assets: Option<Vec<String>>,

    /// Enable or disable bridge public queries
    #[serde(alias = "bridgepublicqueries")]
    pub bridge_public_queries: bool,

    /// Enable bridge queries via http
    #[serde(alias = "bridgehttpqueries")]
    pub bridge_http_queries: bool,

    /// Bridge http listen port
    #[serde(alias = "bridgehttplistenport")]
    pub bridge_http_listen_port: u16,

    /// If present, Authenticate bridge http queries with the following sha256 hmac key
    #[serde(alias = "bridgehttphmackey")]
    pub bridge_http_hmac_key: Option<String>,
}

impl Default for Node {
    fn default() -> Self {
        let mut path = dirs::config_dir().unwrap();
        path.push("Purplecoin");

        Self {
            network_name: "devnet".to_owned(), // Use devnet as default for now
            verifier_threads: 0,
            network_threads: 0,
            sectors_listening: None,
            shards_listening: None,
            archival_mode: true, // Leave this on for now
            prune_headers: false,
            prune_transactions: false,
            prune_utxos: false,
            data_dir: path.into_os_string().into_string().unwrap(),
            memory_only: false,
            mempool_size: 1024,
            dht_bridge_enabled: true,
            dht_bridge_storage_mb: 1024,
            save_utxos_addresses: None,
            save_utxos_assets: None,
            bridge_public_queries: false,
            bridge_http_queries: false,
            bridge_http_listen_port: 8080,
            bridge_http_hmac_key: None,
        }
    }
}

impl Node {
    fn validate(&self) {
        // Validate sector ids
        if let Some(sectors_listening) = &self.sectors_listening {
            for id in sectors_listening {
                assert!(
                    *id < SECTORS as u8,
                    "Invalid sector id: {}. Min value: 0, Max value: {}",
                    id,
                    SECTORS - 1
                );
            }
        }

        // Validate shard ids
        if let (Some(sectors_listening), Some(shards_listening)) =
            (&self.sectors_listening, &self.shards_listening)
        {
            // Create a vector of start and end intervals
            let mut intervals = vec![];
            let mut valid = HashSet::new();

            for id in sectors_listening {
                intervals.push((
                    *id * SECTORS as u8,
                    *id * SECTORS as u8 + (SECTORS as u8 - 1),
                ));
            }

            for id in shards_listening {
                for (id_start, id_end) in &intervals {
                    if id >= id_start && id <= id_end {
                        valid.insert(*id);
                    }
                }
            }

            // We have invalid ids. Sort them and print them
            if valid.len() != shards_listening.len() {
                let mut invalid: Vec<_> = valid
                    .symmetric_difference(shards_listening)
                    .copied()
                    .collect();
                invalid.sort_unstable();
                assert!(
                    false,
                    "The following shard ids are not being listened to by any sectors: {invalid:?}"
                );
            }
        }

        // Validate network name
        assert!(!(self.network_name.as_str() != "mainnet" && self.network_name.as_str() != "testnet" && self.network_name.as_str() != "devnet"), "invalid settings: networkname is invalid, possible values: mainnet, testnet, or devnet.");
    }
}

#[derive(Debug, Serialize, Deserialize, Default, FieldNamesAsArray)]
pub struct Miner {
    /// Only mine the given sectors.
    #[serde(alias = "onlysectors")]
    pub only_sectors: Option<Vec<u8>>,

    /// Only mine the given algos.
    #[serde(alias = "onlyalgos")]
    pub only_algos: Option<Vec<String>>,

    /// Send coinbase UTXOs to the given address.
    #[serde(alias = "coinbaseaddress")]
    pub coinbase_address: Option<String>,

    /// Number of miner threads
    ///
    /// Default is 0 which means the number of cores of the system
    #[serde(alias = "minerthreads")]
    pub miner_threads: u16,
}

impl Miner {
    fn validate(&self) {}
}

#[derive(Debug, Serialize, Deserialize, FieldNamesAsArray)]
pub struct Cluster {
    /// Enable cluster deployment.
    #[serde(alias = "clusterenabled")]
    pub cluster_enabled: bool,

    /// Enable cluster discovery.
    #[serde(alias = "clusterdiscovery")]
    pub cluster_discovery: bool,

    /// Cluster discovery port.
    #[serde(alias = "clusterdiscoveryport")]
    pub cluster_discovery_port: u16,

    /// Cluster discovery service listen address.
    #[serde(alias = "clusterdiscoverylistenaddr")]
    pub cluster_discovery_listen_addr: String,

    /// Cluster cookie. Should be unique and larger than 32 characters.
    #[serde(alias = "clustercookie")]
    pub cluster_cookie: String,

    /// Shard state can be split in virtual nodes in cluster mode. Only
    /// UTXOs and transactions are split between virtual nodes.
    ///
    /// Default is 1.
    #[serde(alias = "vnodespershard")]
    pub vnodes_per_shard: u16,

    /// Replication factor per virtual node.
    ///
    /// Default is 1.
    #[serde(alias = "vnodesreplicationfactor")]
    pub vnodes_replication_factor: u16,

    /// When replication factor is bigger than 1, enabling this will
    /// block until writes have been performed on all replicas. Turning
    /// the system into CP according to the CAP theorem.
    ///
    /// When not enabled, only a majority is required. With this setting,
    /// the system is AP according to the CAP theorem.
    ///
    /// Default is false.
    #[serde(alias = "blockwrites")]
    pub block_writes: bool,

    /// Replication mode.
    ///
    /// Can either be `simple` or `datacenter`
    ///
    /// In simple mode, the replication factor is applied per cluster. While
    /// in datacenter mode, the replication factor applies per datacenter and
    /// all data is replicated across all datacenters.
    #[serde(alias = "replicationmode")]
    pub replication_mode: String,

    /// The datacenter name where this node belongs. Only taken into consideration
    /// when `replication_mode = 'datacenter'`
    #[serde(alias = "replicationdatacenter")]
    pub replication_datacenter: String,

    /// Explicit cluster ips.
    #[serde(alias = "clusterips")]
    pub cluster_ips: Option<Vec<String>>,
}

impl Default for Cluster {
    fn default() -> Self {
        let mut cluster_cookie_list = Vec::new();
        cluster_cookie_list.push(hex::encode(rand::thread_rng().gen::<[u8; 32]>()));
        cluster_cookie_list.push(hex::encode(rand::thread_rng().gen::<[u8; 32]>()));
        Self {
            cluster_enabled: false,
            cluster_discovery: false,
            cluster_discovery_port: 3034,
            cluster_discovery_listen_addr: "127.0.0.1".to_owned(),
            cluster_cookie: cluster_cookie_list.join(""),
            vnodes_per_shard: 1,
            vnodes_replication_factor: 1,
            replication_mode: "simple".to_owned(),
            replication_datacenter: "example-dc".to_owned(),
            block_writes: true,
            cluster_ips: None,
        }
    }
}

impl Cluster {
    fn validate(&self) {}
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
enum DynamicConfVal {
    String(String),
    Sequence(Vec<String>),
    Option(Option<String>),
    OptionSequence(Option<Vec<String>>),
    OptionSequenceByte(Option<Vec<u8>>),
    Bool(bool),
    U16(u16),
}

fn has_unique_elements<T>(iter: T) -> bool
where
    T: IntoIterator,
    T::Item: Eq + Hash,
{
    let mut uniq = HashSet::new();
    iter.into_iter().all(move |x| uniq.insert(x))
}

#[cfg(test)]
mod tests {
    use super::*;
    use fluent_asserter::prelude::*;

    #[test]
    fn it_validates_sector_ids() {
        let mut settings = Settings::default();
        settings.node.sectors_listening = Some(
            [0_u8, 1_u8, 2_u8, 3_u8, 4_u8, 7_u8, 15_u8]
                .iter()
                .copied()
                .collect(),
        );
        settings.validate();
    }

    #[test]
    fn it_fails_validation_on_invalid_sector_id() {
        let mut settings = Settings::default();
        settings.node.sectors_listening = Some(
            [0_u8, 1_u8, 2_u8, 3_u8, 4_u8, 7_u8, 15_u8, 16_u8]
                .iter()
                .copied()
                .collect(),
        );
        let panicking_action = move || settings.validate();
        assert_that_code!(panicking_action)
            .panics()
            .with_message("Invalid sector id: 16. Min value: 0, Max value: 15");
    }

    #[test]
    fn it_validates_shard_id() {
        let mut settings = Settings::default();
        settings.node.sectors_listening = Some([0_u8, 15_u8].iter().copied().collect());
        settings.node.shards_listening = Some(
            [0_u8, 1_u8, 5_u8, 246_u8, 250_u8, 255_u8]
                .iter()
                .copied()
                .collect(),
        );
        settings.validate();
    }

    #[test]
    fn it_fails_validation_on_invalid_shard_id() {
        let mut settings = Settings::default();
        settings.node.sectors_listening = Some([1_u8].iter().copied().collect());
        settings.node.shards_listening = Some(
            [
                0_u8, 1_u8, 5_u8, 16_u8, 19_u8, 25_u8, 246_u8, 250_u8, 255_u8,
            ]
            .iter()
            .copied()
            .collect(),
        );
        let panicking_action = move || settings.validate();
        assert_that_code!(panicking_action)
            .panics()
            .with_message("The following shard ids are not being listened to by any sectors: [0, 1, 5, 246, 250, 255]");
    }
}

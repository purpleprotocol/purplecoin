// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use config::{Config, ConfigError, File};
use lazy_static::*;
use log::*;
use rand::Rng;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::env;
use std::fs::{metadata, File as FsFile};
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
        for (k, v) in env_source.iter() {
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
}

#[derive(Debug, Serialize, Deserialize, FieldNamesAsArray)]
pub struct Network {
    /// Node listen address.
    #[serde(alias = "listenaddr")]
    pub listen_addr: String,

    /// Node listen port on mainnet.
    #[serde(alias = "listenportmainnet")]
    pub listen_port_mainnet: u16,

    /// Node listen port on mainnet.
    #[serde(alias = "listenporttestnet")]
    pub listen_port_testnet: u16,

    /// Enable RPC.
    #[serde(alias = "rpcenabled")]
    pub rpc_enabled: bool,

    /// RPC listen port on mainnet.
    #[serde(alias = "rpclistenportmainnet")]
    pub rpc_listen_port_mainnet: u16,

    /// RPC listen port on testnet.
    #[serde(alias = "rpclistenporttestnet")]
    pub rpc_listen_port_testnet: u16,

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
}

impl Default for Network {
    fn default() -> Self {
        Self {
            listen_addr: "*".to_owned(),
            listen_port_mainnet: 8098,
            listen_port_testnet: 8031,
            rpc_enabled: true,
            rpc_listen_port_mainnet: 8067,
            rpc_listen_port_testnet: 8037,
            rpc_username: "purplecoin".to_owned(),
            rpc_password: "purplecoin".to_owned(),
            seeds_mainnet: vec!["bootstrap.mainnet.purplecoin.io".to_owned()],
            seeds_testnet: vec!["bootstrap.testnet.purplecoin.io".to_owned()],
        }
    }
}

#[derive(Debug, Serialize, Deserialize, FieldNamesAsArray)]
pub struct Node {
    /// The network name the node is listening on.
    #[serde(alias = "networkname")]
    pub network_name: String,

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

    /// Turn on RandomX fast mode. Uses 1024 mb of shared memory per instance.
    #[serde(alias = "randomxfastmode")]
    pub randomx_fast_mode: bool,

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
            network_name: "testnet".to_owned(), // Use testnet as default for now
            verifier_threads: 0,
            network_threads: 0,
            archival_mode: true, // Leave this on for now
            prune_headers: false,
            randomx_fast_mode: false,
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

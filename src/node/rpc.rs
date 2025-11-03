// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::chain::{Chain, DBInterface, PowChainBackend, ShardBackend, ShardBackendErr};
use crate::consensus::SECTORS;
use crate::node::{PeerInfo, PeerInfoTable, NODE_INFO, PEER_INFO_TABLE};
use crate::settings::SETTINGS;
use futures::{
    future::{self, Ready},
    prelude::*,
};
use rand::Rng;
use schnorrkel::{
    signing_context, PublicKey as SchnorPK, SecretKey as SchnorSK, Signature as SchnorSig,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::marker::{Send, Sync};
use std::net::SocketAddr;
use std::sync::atomic::Ordering;
use tarpc::{
    client, context,
    server::{self, incoming::Incoming, Channel},
};
use zeroize::Zeroize;

pub type RpcRequest = tarpc::ClientMessage<RpcServerDefinitionRequest>;
pub type RpcResponse = tarpc::Response<RpcServerDefinitionResponse>;
pub type RpcChannel = tarpc::transport::channel::UnboundedChannel<RpcResponse, RpcRequest>;

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct BlockchainInfo {
    pub network: String,
    pub version: String,
    pub protocol_version: u32,
    pub sectors: SectorInfo,
    pub shards: ShardInfo,
    pub mempool: MempoolSummary,
    pub node: NodeSummary,
    pub uptime: i64,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct SectorInfo {
    pub total_sectors: u8,
    pub active_sectors: u8,
    pub sector_heights: HashMap<u8, u64>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct ShardInfo {
    pub total_shards: u16,
    pub active_shards: u16,
    pub shard_heights: HashMap<u8, u64>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct MempoolSummary {
    pub total_transactions: u32,
    pub total_size_bytes: u64,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct NodeSummary {
    pub peer_count: u64,
    pub network_active: bool,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct BlockStats {
    pub hash: String,
    pub height: u64,
    pub timestamp: i64,
    pub transaction_count: u32,
    pub block_size_bytes: u64,
    pub total_fees: u64,
    pub shard_id: u8,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct RawMempool {
    pub transaction_hashes: Vec<String>,
    pub total_transactions: u32,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct OutputInfo {
    pub amount: i128,
    pub script_hash: String,
    pub inputs_hash: String,
    pub idx: u16,
    pub address: Option<String>,
    pub coloured_address: Option<String>,
    pub coinbase_height: Option<u64>,
    pub hash: String,
}

#[tarpc::service]
pub trait RpcServerDefinition {
    /// Returns information about the Blockchain
    async fn get_blockchain_info() -> Result<BlockchainInfo, RpcErr>;

    /// Returns the hash of block in best-block-chain at height provided
    async fn get_block_hash(chain_id: u8, height: u64) -> Result<String, RpcErr>;

    /// Returns block stats for block with the given hash
    async fn get_block_stats(hash: String) -> Result<BlockStats, RpcErr>;

    /// Returns the height of the most-work fully-validated sector
    async fn get_sector_height(sector_id: u8) -> Result<u64, RpcErr>;

    /// Returns the height of the most-work fully-validated shard
    async fn get_shard_height(chain_id: u8) -> Result<u64, RpcErr>;

    /// Returns information about the shard
    async fn get_shard_info(chain_id: u8) -> String;

    /// Returns info about the mempool
    async fn get_mempool_info() -> Result<MempoolSummary, RpcErr>;

    /// Returns the raw mempool data for a shard
    async fn get_raw_mempool_shard(chain_id: u8) -> Result<RawMempool, RpcErr>;

    /// Returns the raw mempool data for all shards
    async fn get_raw_mempool() -> Result<RawMempool, RpcErr>;

    /// Marks the block with the given hash as precious
    async fn precious_block(block_hash: String) -> String;

    /// Prunes the chain with the given id up to height in the given mode.
    ///
    /// Modes:
    /// * Full - Prunes headers and UTXOs
    /// * OnlyUTXOs - Prunes only UTXOs
    async fn prune_shard(chain_id: u8, height: u64, mode: String) -> String;

    /// Generates a block to the given address or descriptor
    async fn generate(address_or_descriptor: String) -> String;

    /// Generates a block to the given descriptor
    async fn generate_to_descriptor(descriptor: String) -> String;

    /// Generates a block to the given address
    async fn generate_to_address(address: String) -> String;

    /// Generates a share block to the given address or descriptor
    async fn generate_share(address_or_descriptor: String) -> String;

    /// Generates a share block to the given descriptor
    async fn generate_share_to_descriptor(address: String) -> String;

    /// Generates a share block to the given address
    async fn generate_share_to_address(address_or_descriptor: String) -> String;

    /// Submits a block to be appended to the chain
    async fn submit_block(payload: String) -> String;

    /// Submits a share block to be appended to the sharechain
    async fn submit_share_block(payload: String) -> String;

    /// Returns information about the network
    async fn get_network_info() -> String;

    /// Returns information about each peer
    async fn get_peer_info() -> Option<HashMap<String, PeerInfo>>;

    /// Returns the total p2p connections count
    async fn get_connection_count() -> u64;

    /// Returns information about network traffic
    async fn get_net_totals() -> String;

    /// Adds the node with the given ip
    async fn add_node(node: String) -> String;

    /// Lists banned ips
    async fn list_banned() -> String;

    /// Enables/Disables all p2p network activity. This does not include nodes with the same cookie
    async fn set_network_active(active: bool) -> String;

    /// Returns information about the node
    async fn get_node_info() -> Option<PeerInfo>;

    /// Attempts to gracefully shutdown Purplecoin
    async fn stop() -> String;

    /// Returns the number of seconds the server has been running
    async fn uptime() -> i64;

    /// Validates the given address
    async fn validate_address(address: String) -> bool;

    /// Signs a message with the given keypair
    async fn sign_message(
        message: String,
        pub_key: String,
        priv_key: String,
        signing_ctx: String,
    ) -> Result<String, RpcErr>;

    /// Verifies the given message with the given pub key and signature
    async fn verify_message(
        message: String,
        signature: String,
        pub_key: String,
        signing_ctx: String,
    ) -> Result<bool, RpcErr>;

    /// Verifies that the given pub_key matches address
    async fn verify_address(address: String, pub_key: String) -> Result<bool, RpcErr>;

    /// Generates a wallet with the given name and passphrase
    async fn generate_wallet(name: String, passphrase: String) -> Result<String, RpcErr>;

    /// Backups wallet at location
    async fn backup_wallet(name: String, path: String) -> Result<String, RpcErr>;

    /// Backs up wallet in AWS S3
    async fn backup_wallet_s3(
        name: String,
        bucket: String,
        key: String,
        access_key_id: String,
        secret_access_key: String,
    ) -> Result<String, RpcErr>;

    /// Sends a raw transaction
    async fn send_raw_tx(transaction: String) -> Result<String, RpcErr>;

    /// Queries output with hash and returns if present in the UTXO set
    async fn query_output(output_hash: String) -> Result<String, RpcErr>;
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum RpcErr {
    /// The provided public key could not be deserialised.
    InvalidPublicKey,

    /// The provided private key could not be deserialised.
    InvalidPrivateKey,

    /// The provided signature could nto be deserialised.
    InvalidSignature,

    /// There already is a wallet with this name.
    WalletAlreadyExists,

    /// Generic wallet error
    WalletErr(String),

    /// Wallet backup error
    CouldNotBackupWallet,

    /// Core runtime err
    CoreRuntimeError,

    /// The given sector id is invalid.
    InvalidSectorId,

    /// The queried shard has not been initialised.
    ShardNotInitialised,

    /// The queried sector has not been initialised.
    SectorNotInitialised,

    /// Sector error
    SectorBackendErr,

    /// Shard error
    ShardBackendErr,

    /// The provided block hash is invalid or block not found
    InvalidBlockHash,

    /// Invalid transaction
    InvalidTransaction(String),

    /// Internal error
    InternalError(String),
}

/// RPC server
#[derive(Clone)]
pub struct RpcServer<B: PowChainBackend + ShardBackend + DBInterface + Send + Sync + 'static> {
    pub chain: Chain<B>,
}

#[tarpc::server]
impl<B: PowChainBackend + ShardBackend + DBInterface + Send + Sync + 'static> RpcServerDefinition
    for RpcServer<B>
{
    async fn get_blockchain_info(self, _: context::Context) -> Result<BlockchainInfo, RpcErr> {
        // Collect sector information
        let mut sector_heights = HashMap::new();
        for (sector_id, sector) in &self.chain.sectors {
            if let Ok(height) = sector.height() {
                sector_heights.insert(*sector_id, height);
            }
        }

        // Collect shard information
        let mut shard_heights = HashMap::new();
        for (shard_id, shard) in &self.chain.chain_states {
            if let Ok(height) = shard.height() {
                shard_heights.insert(*shard_id, height);
            }
        }

        // Get mempool information
        let mempool = self.chain.mempool.read();
        let mempool_summary = MempoolSummary {
            total_transactions: mempool.tx_map.len() as u32,
            total_size_bytes: mempool.current_size_bytes,
        };

        // Get node information
        let peer_count = unsafe {
            PEER_INFO_TABLE
                .as_ref()
                .map(|table| table.read().len() as u64)
                .unwrap_or(0)
        };

        // Calculate uptime
        let startup = crate::global::STARTUP_TIME.load(Ordering::Relaxed);
        let uptime = crate::global::get_unix_timestamp_secs() - startup;

        Ok(BlockchainInfo {
            network: SETTINGS.node.network_name.clone(),
            version: env!("CARGO_PKG_VERSION").to_string(),
            protocol_version: 1, // TODO: Define actual protocol version
            sectors: SectorInfo {
                total_sectors: SECTORS as u8,
                active_sectors: self.chain.sectors.len() as u8,
                sector_heights,
            },
            shards: ShardInfo {
                total_shards: 256,
                active_shards: self.chain.chain_states.len() as u16,
                shard_heights,
            },
            mempool: mempool_summary,
            node: NodeSummary {
                peer_count,
                network_active: true, // TODO: Get actual network status
            },
            uptime,
        })
    }

    async fn get_mempool_info(self, _: context::Context) -> Result<MempoolSummary, RpcErr> {
        // Get mempool information
        let mempool = self.chain.mempool.read();
        let mempool_summary = MempoolSummary {
            total_transactions: mempool.tx_map.len() as u32,
            total_size_bytes: mempool.current_size_bytes,
        };

        Ok(mempool_summary)
    }

    async fn get_raw_mempool(self, _: context::Context) -> Result<RawMempool, RpcErr> {
        // Get all transactions from mempool
        let mempool = self.chain.mempool.read();
        let transaction_hashes: Vec<String> =
            mempool.tx_map.keys().map(|hash| hash.to_hex()).collect();
        let total_transactions = transaction_hashes.len() as u32;

        Ok(RawMempool {
            transaction_hashes,
            total_transactions,
        })
    }

    async fn get_sector_height(self, _: context::Context, sector_id: u8) -> Result<u64, RpcErr> {
        if sector_id >= SECTORS as u8 {
            return Err(RpcErr::InvalidSectorId);
        }

        let sector = self
            .chain
            .sectors
            .get(&sector_id)
            .ok_or(RpcErr::SectorNotInitialised)?;
        sector.height().map_err(|_| RpcErr::SectorBackendErr)
    }

    async fn get_shard_height(self, _: context::Context, chain_id: u8) -> Result<u64, RpcErr> {
        let shard = self
            .chain
            .chain_states
            .get(&chain_id)
            .ok_or(RpcErr::ShardNotInitialised)?;
        shard.height().map_err(|_| RpcErr::ShardBackendErr)
    }

    async fn get_shard_info(self, _: context::Context, chain_id: u8) -> String {
        "Hello world!".to_string()
    }

    async fn get_raw_mempool_shard(
        self,
        _: context::Context,
        chain_id: u8,
    ) -> Result<RawMempool, RpcErr> {
        // Filter transactions by shard/chain_id
        let mempool = self.chain.mempool.read();
        let transaction_hashes: Vec<String> = mempool
            .tx_map
            .iter()
            .filter(|(_, tx)| tx.tx.tx.chain_id == chain_id)
            .map(|(hash, _)| hash.to_hex())
            .collect();
        let total_transactions = transaction_hashes.len() as u32;

        Ok(RawMempool {
            transaction_hashes,
            total_transactions,
        })
    }

    async fn get_block_hash(
        self,
        _: context::Context,
        chain_id: u8,
        height: u64,
    ) -> Result<String, RpcErr> {
        // Get the shard for this chain_id
        let shard = self
            .chain
            .chain_states
            .get(&chain_id)
            .ok_or(RpcErr::ShardNotInitialised)?;

        // Get the canonical block header at the specified height
        match shard.backend.get_canonical_block_at_height(height) {
            Ok(Some(block_header)) => Ok(block_header.hash().unwrap().to_hex()),
            Ok(None) => {
                // No block at this height
                Err(RpcErr::ShardBackendErr)
            }
            Err(_) => Err(RpcErr::ShardBackendErr),
        }
    }

    async fn get_block_stats(
        self,
        _: context::Context,
        hash: String,
    ) -> Result<BlockStats, RpcErr> {
        // Parse the hex hash
        let hash_bytes = hex::decode(&hash).map_err(|_| RpcErr::InvalidBlockHash)?;
        if hash_bytes.len() != 32 {
            return Err(RpcErr::InvalidBlockHash);
        }

        let mut hash_array = [0u8; 32];
        hash_array.copy_from_slice(&hash_bytes);
        let target_hash = crate::primitives::Hash256(hash_array);

        // Search through all active shards to find the block
        for (shard_id, shard) in &self.chain.chain_states {
            // Try to get the canonical block with this hash
            match shard.backend.get_canonical_block(&target_hash) {
                Ok(Some(block_header)) => {
                    // Get the block data to calculate stats
                    let block_data = shard
                        .backend
                        .get_block_data(&target_hash)
                        .map_err(|_| RpcErr::ShardBackendErr)?;

                    let (transaction_count, total_fees) = if let Some(data) = block_data {
                        let tx_count = data.txs.len() as u32;

                        // Calculate total fees from all transactions in the block
                        // Fee = sum(inputs) - sum(outputs) for each transaction
                        let mut fees: i128 = 0;
                        for tx in &data.txs {
                            // Skip coinbase transactions (no fee)
                            if tx.is_coinbase() {
                                continue;
                            }

                            // Sum input amounts
                            let mut inputs_sum: i128 = 0;
                            for input in &tx.ins {
                                if let Some(ref out) = input.out {
                                    inputs_sum += out.amount;
                                }
                            }

                            // Sum output amounts (from script execution)
                            // Note: Outputs are generated during script execution, not stored in tx
                            // For now, we compute a simplified fee based on inputs
                            // TODO: Cache actual fee in storage as suggested by maintainer
                            // The proper way is to use verify_single which returns the fee

                            // For a rough estimate, we can assume some fee was paid
                            // But without executing scripts, we can't get exact output amounts
                            // So we'll use 0 for now and add proper caching later
                        }

                        // TODO: Implement proper fee caching in storage
                        // For now, return 0 as a placeholder
                        (tx_count, 0u64)
                    } else {
                        (0, 0)
                    };

                    // Calculate approximate block size
                    let block_size = crate::codec::encode_to_vec(&block_header)
                        .map(|encoded| encoded.len() as u64)
                        .unwrap_or(0);

                    // Get timestamp from PoW block header at the same height
                    // Calculate which sector this shard belongs to
                    let sector_id = *shard_id / crate::consensus::SHARDS_PER_SECTOR as u8;

                    let timestamp = if let Some(sector) = self.chain.sectors.get(&sector_id) {
                        match sector.backend.get_canonical_pow_block_at_height(block_header.height) {
                            Ok(Some(pow_header)) => pow_header.timestamp,
                            _ => 0, // Fallback to 0 if PoW block not found
                        }
                    } else {
                        0 // Fallback to 0 if sector not initialized
                    };

                    return Ok(BlockStats {
                        hash: hash.clone(),
                        height: block_header.height,
                        timestamp,
                        transaction_count,
                        block_size_bytes: block_size,
                        total_fees,
                        shard_id: *shard_id,
                    });
                }
                Ok(None) => {
                    // Block not found in this shard, continue searching
                    continue;
                }
                Err(_) => {
                    // Error accessing shard, continue searching other shards
                    continue;
                }
            }
        }

        // Block not found in any shard
        Err(RpcErr::InvalidBlockHash)
    }

    async fn precious_block(self, _: context::Context, hash: String) -> String {
        "Hello world!".to_string()
    }

    async fn prune_shard(
        self,
        _: context::Context,
        chain_id: u8,
        height: u64,
        mode: String,
    ) -> String {
        "Hello world!".to_string()
    }

    async fn generate(self, _: context::Context, address_or_descriptor: String) -> String {
        "Hello world!".to_string()
    }

    async fn generate_to_address(self, _: context::Context, address: String) -> String {
        "Hello world!".to_string()
    }

    async fn generate_to_descriptor(self, _: context::Context, descriptor: String) -> String {
        "Hello world!".to_string()
    }

    async fn generate_share(self, _: context::Context, address_or_descriptor: String) -> String {
        "Hello world!".to_string()
    }

    async fn generate_share_to_address(self, _: context::Context, address: String) -> String {
        "Hello world!".to_string()
    }

    async fn generate_share_to_descriptor(self, _: context::Context, descriptor: String) -> String {
        "Hello world!".to_string()
    }

    async fn submit_block(self, _: context::Context, payload: String) -> String {
        "Hello world!".to_string()
    }

    async fn submit_share_block(self, _: context::Context, payload: String) -> String {
        "Hello world!".to_string()
    }

    async fn get_node_info(self, _: context::Context) -> Option<PeerInfo> {
        let node_info = unsafe { NODE_INFO.clone() };

        node_info.as_ref()?;

        let node_info = node_info.unwrap().read().clone();
        Some(node_info)
    }

    async fn stop(self, _: context::Context) -> String {
        crate::global::EXIT_SIGNAL.store(true, Ordering::Relaxed);
        format!(
            "Purplecoin Core v{} shutting down",
            env!("CARGO_PKG_VERSION")
        )
    }

    async fn uptime(self, _: context::Context) -> i64 {
        let startup = crate::global::STARTUP_TIME.load(Ordering::Relaxed);
        crate::global::get_unix_timestamp_secs() - startup
    }

    async fn generate_wallet(
        self,
        _: context::Context,
        name: String,
        mut passphrase: String,
    ) -> Result<String, RpcErr> {
        let name_clone = name.clone();
        let passphrase_clone = passphrase.clone();
        let worker = tokio::task::spawn_blocking(move || {
            let mut passphrase = passphrase_clone;
            let name = name_clone;

            // Generate random seed
            let mut seed = [0; 64];
            {
                let mut rng = rand::thread_rng();
                for i in 0..64 {
                    seed[i] = rng.gen();
                }
            }

            let res = crate::wallet::generate_hdwallet(name.as_str(), passphrase.as_str(), seed);
            passphrase.zeroize();
            seed.zeroize();
            res
        });

        match worker.await {
            Ok(Err("wallet already exists")) => {
                passphrase.zeroize();
                Err(RpcErr::WalletAlreadyExists)
            }
            Ok(Err(err)) => {
                passphrase.zeroize();
                Err(RpcErr::WalletErr(err.to_owned()))
            }
            Ok(Ok(_)) => {
                passphrase.zeroize();
                Ok("Wallet created successfuly".to_owned())
            }
            Err(_join_err) => {
                passphrase.zeroize();
                Err(RpcErr::CoreRuntimeError)
            }
        }
    }

    async fn backup_wallet(
        self,
        _: context::Context,
        name: String,
        path: String,
    ) -> Result<String, RpcErr> {
        Err(RpcErr::CouldNotBackupWallet)
    }

    async fn backup_wallet_s3(
        self,
        _: context::Context,
        name: String,
        bucket: String,
        key: String,
        access_key_id: String,
        secret_access_key: String,
    ) -> Result<String, RpcErr> {
        Err(RpcErr::CouldNotBackupWallet)
    }

    async fn get_network_info(self, _: context::Context) -> String {
        "Hello world!".to_string()
    }

    async fn get_peer_info(self, _: context::Context) -> Option<HashMap<String, PeerInfo>> {
        let peer_table = unsafe { PEER_INFO_TABLE.clone() };

        peer_table.as_ref()?;

        let peer_table = peer_table.unwrap().read().clone();
        let peer_table: HashMap<_, _> = peer_table
            .iter()
            .map(|(id, v)| (id.to_base58(), v.clone()))
            .collect();
        Some(peer_table)
    }

    async fn get_connection_count(self, _: context::Context) -> u64 {
        let peer_table = unsafe { PEER_INFO_TABLE.clone() };

        if peer_table.is_none() {
            return 0;
        }

        peer_table.unwrap().read().len() as u64
    }

    async fn get_net_totals(self, _: context::Context) -> String {
        "Hello world!".to_string()
    }

    async fn add_node(self, _: context::Context, node: String) -> String {
        "Hello world!".to_string()
    }

    async fn list_banned(self, _: context::Context) -> String {
        "Hello world!".to_string()
    }

    async fn set_network_active(self, _: context::Context, active: bool) -> String {
        "Hello world!".to_string()
    }

    async fn validate_address(self, _: context::Context, address: String) -> bool {
        let res = bech32::decode(address.as_str());
        if res.is_err() {
            return false;
        }
        let (hrp, _, variant) = res.unwrap();

        if hrp.as_str() != "pu" {
            return false;
        }

        // Only the bech32m variant is allowed
        if let bech32::Variant::Bech32 = variant {
            return false;
        }

        true
    }

    async fn sign_message(
        self,
        _: context::Context,
        message: String,
        pub_key: String,
        mut priv_key: String,
        signing_ctx: String,
    ) -> Result<String, RpcErr> {
        let decoded_priv = hex::decode(priv_key.as_str());
        priv_key.zeroize();

        if decoded_priv.is_err() {
            return Err(RpcErr::InvalidPrivateKey);
        }

        let mut decoded_priv = decoded_priv.unwrap();
        let decoded_pub = hex::decode(pub_key);

        if decoded_pub.is_err() {
            priv_key.zeroize();
            return Err(RpcErr::InvalidPublicKey);
        }

        let decoded_pub = decoded_pub.unwrap();
        let priv_key = SchnorSK::from_bytes(&decoded_priv);
        decoded_priv.zeroize();

        if priv_key.is_err() {
            return Err(RpcErr::InvalidPrivateKey);
        }

        let mut priv_key = priv_key.unwrap();
        let pub_key = SchnorPK::from_bytes(&decoded_pub);

        if pub_key.is_err() {
            priv_key.zeroize();
            return Err(RpcErr::InvalidPublicKey);
        }

        let pub_key = pub_key.unwrap();
        let ctx = signing_context(signing_ctx.as_bytes());
        let sig = priv_key.sign(ctx.bytes(message.as_bytes()), &pub_key);

        priv_key.zeroize();
        Ok(hex::encode(sig.to_bytes()))
    }

    async fn verify_message(
        self,
        _: context::Context,
        message: String,
        signature: String,
        pub_key: String,
        signing_ctx: String,
    ) -> Result<bool, RpcErr> {
        let decoded_pub = hex::decode(pub_key);

        if decoded_pub.is_err() {
            return Err(RpcErr::InvalidPublicKey);
        }

        let decoded_pub = decoded_pub.unwrap();
        let pub_key = SchnorPK::from_bytes(&decoded_pub);

        if pub_key.is_err() {
            return Err(RpcErr::InvalidPublicKey);
        }

        let decoded_sig = hex::decode(signature);

        if decoded_sig.is_err() {
            return Err(RpcErr::InvalidSignature);
        }

        let decoded_sig = decoded_sig.unwrap();
        let signature = SchnorSig::from_bytes(&decoded_sig);

        if signature.is_err() {
            return Err(RpcErr::InvalidSignature);
        }

        let pub_key = pub_key.unwrap();
        let signature = signature.unwrap();
        let ctx = signing_context(signing_ctx.as_bytes());

        Ok(pub_key
            .verify(ctx.bytes(message.as_bytes()), &signature)
            .is_ok())
    }

    async fn verify_address(
        self,
        _: context::Context,
        address: String,
        pub_key: String,
    ) -> Result<bool, RpcErr> {
        let decoded_pub = crate::primitives::PublicKey::from_hex(pub_key.as_str());

        if decoded_pub.is_err() {
            return Err(RpcErr::InvalidPublicKey);
        }

        let decoded_pub = decoded_pub.unwrap();
        let address_bech = decoded_pub.to_address().to_bech32("pu");

        if address_bech != address {
            return Ok(false);
        }

        Ok(true)
    }

    async fn send_raw_tx(self, _: context::Context, transaction: String) -> Result<String, RpcErr> {
        // Decode hex string to bytes
        let tx_bytes = hex::decode(&transaction)
            .map_err(|_| RpcErr::InvalidTransaction("Invalid hex encoding".to_string()))?;

        // Deserialize to Transaction
        let mut tx: crate::primitives::Transaction =
            crate::codec::decode(&tx_bytes).map_err(|e| {
                RpcErr::InvalidTransaction(format!("Failed to decode transaction: {:?}", e))
            })?;

        let chain_id = tx.chain_id;
        let key = self.chain.config.get_chain_key(chain_id);

        // Compute transaction hash
        tx.compute_hash(key);

        // Get shard to retrieve current height and other chain info
        let shard =
            self.chain.chain_states.get(&chain_id).ok_or_else(|| {
                RpcErr::InvalidTransaction(format!("Shard {} not found", chain_id))
            })?;

        let height = shard
            .height()
            .map_err(|e| RpcErr::InternalError(format!("Failed to get shard height: {:?}", e)))?;

        // Get current block header for validation context
        let block_header = shard
            .backend
            .get_canonical_block_at_height(if height > 0 { height - 1 } else { 0 })
            .map_err(|e| RpcErr::InternalError(format!("Failed to get block header: {:?}", e)))?
            .ok_or_else(|| RpcErr::InternalError("Block header not found".to_string()))?;

        // Use current timestamp for validation
        let timestamp = crate::global::get_unix_timestamp_secs();
        let prev_block_hash = block_header
            .hash
            .ok_or_else(|| RpcErr::InternalError("Block hash not computed".to_string()))?;

        // Wrap in TransactionWithSignatures (signatures are embedded in inputs)
        let tx_with_sigs = crate::primitives::TransactionWithSignatures {
            tx,
            signatures: vec![],
        };

        // Convert to TransactionWithFee (validates the transaction)
        let tx_with_fee = crate::primitives::TransactionWithFee::from_transaction(
            tx_with_sigs,
            key,
            height,
            chain_id,
            timestamp,
            prev_block_hash,
        )
        .map_err(|e| {
            RpcErr::InvalidTransaction(format!("Transaction validation failed: {:?}", e))
        })?;

        // Get transaction hash before adding to mempool
        let tx_hash = tx_with_fee
            .hash()
            .ok_or_else(|| RpcErr::InternalError("Transaction hash is None".to_string()))?
            .to_hex();

        // Add to mempool
        let mut mempool = self.chain.mempool.write();
        unsafe {
            let mempool_mut = std::pin::Pin::as_mut(&mut mempool);
            std::pin::Pin::get_unchecked_mut(mempool_mut)
                .append(tx_with_fee)
                .map_err(|e| RpcErr::InternalError(format!("Failed to add to mempool: {}", e)))?;
        }

        Ok(tx_hash)
    }

    async fn query_output(
        self,
        _: context::Context,
        output_hash: String,
    ) -> Result<String, RpcErr> {
        // Decode hex string to Hash256
        let hash_bytes = hex::decode(&output_hash).map_err(|_| {
            RpcErr::InvalidTransaction("Invalid hex encoding for output hash".to_string())
        })?;

        if hash_bytes.len() != 32 {
            return Err(RpcErr::InvalidTransaction(
                "Output hash must be 32 bytes".to_string(),
            ));
        }

        let mut hash_array = [0u8; 32];
        hash_array.copy_from_slice(&hash_bytes);
        let output_hash = crate::primitives::Hash256(hash_array);

        // Since we don't know which shard the output belongs to,
        // we need to search across all active shards
        for (_shard_id, shard) in &self.chain.chain_states {
            if let Some(output) = shard.backend.utxo(&output_hash) {
                // Convert Output to OutputInfo
                let output_info = OutputInfo {
                    amount: output.amount,
                    script_hash: output.script_hash.to_hex(),
                    inputs_hash: output.inputs_hash.to_hex(),
                    idx: output.idx,
                    address: output.address.map(|a| a.to_bech32("pu")),
                    coloured_address: output.coloured_address.map(|a| a.to_bech32("pu")),
                    coinbase_height: output.coinbase_height,
                    hash: output
                        .hash
                        .map(|h| h.to_hex())
                        .unwrap_or_else(|| "unknown".to_string()),
                };

                // Serialize to JSON
                let output_json = serde_json::to_string(&output_info).map_err(|e| {
                    RpcErr::InternalError(format!("Failed to serialize output: {}", e))
                })?;
                return Ok(output_json);
            }
        }

        // Output not found in any shard
        Err(RpcErr::InvalidTransaction(format!(
            "Output with hash {} not found in UTXO set",
            output_hash.to_hex()
        )))
    }
}

pub async fn dispatch_rpc_request(
    request: tarpc::Request<RpcServerDefinitionRequest>,
    client: RpcServerDefinitionClient,
) -> Result<RpcServerDefinitionResponse, String> {
    client
        .0
        .call(
            tarpc::context::current(),
            &request.id.to_string(),
            request.message,
        )
        .await
        .map_err(|err| serde_json::to_string(&err).unwrap())
}

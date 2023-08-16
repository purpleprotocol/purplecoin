// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::node::{PeerInfo, PeerInfoTable, NODE_INFO, PEER_INFO_TABLE};
use futures::{
    future::{self, Ready},
    prelude::*,
};
use schnorrkel::{
    signing_context, PublicKey as SchnorPK, SecretKey as SchnorSK, Signature as SchnorSig,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
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

#[tarpc::service]
pub trait RpcServerDefinition {
    /// Returns information about the Blockchain
    async fn get_blockchain_info() -> String;

    /// Returns the hash of block in best-block-chain at height provided
    async fn get_block_hash(chain_id: u8, height: u64) -> String;

    /// Returns block stats for block with the given hash
    async fn get_block_stats(hash: String) -> String;

    /// Returns the height of the most-work fully-validated chain
    async fn get_height(chain_id: u8) -> u64;

    /// Returns information about the shard
    async fn get_shard_info(chain_id: u8) -> String;

    /// Returns info about the mempool
    async fn get_mempool_info() -> String;

    /// Returns the raw mempool data for a shard
    async fn get_raw_mempool_shard(chain_id: u8) -> String;

    /// Returns the raw mempool data for all shards
    async fn get_raw_mempool() -> String;

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

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub enum RpcErr {
    InvalidPublicKey,
    InvalidPrivateKey,
    WalletAlreadyExists,
    CouldNotBackupWallet,
}

/// RPC server
#[derive(Clone)]
pub struct RpcServer;

impl RpcServerDefinition for RpcServer {
    type GetBlockchainInfoFut = Ready<String>;
    type GetMempoolInfoFut = Ready<String>;
    type GetBlockHashFut = Ready<String>;
    type GetBlockStatsFut = Ready<String>;
    type GetHeightFut = Ready<u64>;
    type GetShardInfoFut = Ready<String>;
    type GetRawMempoolFut = Ready<String>;
    type GetRawMempoolShardFut = Ready<String>;
    type PreciousBlockFut = Ready<String>;
    type PruneShardFut = Ready<String>;
    type GenerateFut = Ready<String>;
    type GenerateToAddressFut = Ready<String>;
    type GenerateToDescriptorFut = Ready<String>;
    type GenerateShareFut = Ready<String>;
    type GenerateShareToAddressFut = Ready<String>;
    type GenerateShareToDescriptorFut = Ready<String>;
    type SubmitBlockFut = Ready<String>;
    type SubmitShareBlockFut = Ready<String>;
    type GetNodeInfoFut = Ready<Option<PeerInfo>>;
    type StopFut = Ready<String>;
    type UptimeFut = Ready<i64>;
    type GenerateWalletFut = Ready<Result<String, RpcErr>>;
    type BackupWalletFut = Ready<Result<String, RpcErr>>;
    type BackupWalletS3Fut = Ready<Result<String, RpcErr>>;
    type GetNetworkInfoFut = Ready<String>;
    type GetPeerInfoFut = Ready<Option<HashMap<String, PeerInfo>>>;
    type GetConnectionCountFut = Ready<u64>;
    type GetNetTotalsFut = Ready<String>;
    type AddNodeFut = Ready<String>;
    type ListBannedFut = Ready<String>;
    type SetNetworkActiveFut = Ready<String>;
    type ValidateAddressFut = Ready<bool>;
    type SignMessageFut = Ready<Result<String, RpcErr>>;
    type VerifyMessageFut = Ready<Result<bool, RpcErr>>;
    type VerifyAddressFut = Ready<Result<bool, RpcErr>>;
    type SendRawTxFut = Ready<Result<String, RpcErr>>;
    type QueryOutputFut = Ready<Result<String, RpcErr>>;

    fn get_blockchain_info(self, _: context::Context) -> Self::GetBlockchainInfoFut {
        future::ready("Hello world!".to_string())
    }

    fn get_mempool_info(self, _: context::Context) -> Self::GetMempoolInfoFut {
        future::ready("Hello world!".to_string())
    }

    fn get_raw_mempool(self, _: context::Context) -> Self::GetRawMempoolFut {
        future::ready("Hello world!".to_string())
    }

    fn get_height(self, _: context::Context, chain_id: u8) -> Self::GetHeightFut {
        future::ready(1)
    }

    fn get_shard_info(self, _: context::Context, chain_id: u8) -> Self::GetShardInfoFut {
        future::ready("Hello world!".to_string())
    }

    fn get_raw_mempool_shard(
        self,
        _: context::Context,
        chain_id: u8,
    ) -> Self::GetRawMempoolShardFut {
        future::ready("Hello world!".to_string())
    }

    fn get_block_hash(
        self,
        _: context::Context,
        chain_id: u8,
        height: u64,
    ) -> Self::GetBlockHashFut {
        future::ready("Hello world!".to_string())
    }

    fn get_block_stats(self, _: context::Context, hash: String) -> Self::GetBlockStatsFut {
        future::ready("Hello world!".to_string())
    }

    fn precious_block(self, _: context::Context, hash: String) -> Self::PreciousBlockFut {
        future::ready("Hello world!".to_string())
    }

    fn prune_shard(
        self,
        _: context::Context,
        chain_id: u8,
        height: u64,
        mode: String,
    ) -> Self::PruneShardFut {
        future::ready("Hello world!".to_string())
    }

    fn generate(self, _: context::Context, address_or_descriptor: String) -> Self::GenerateFut {
        future::ready("Hello world!".to_string())
    }

    fn generate_to_address(
        self,
        _: context::Context,
        address: String,
    ) -> Self::GenerateToAddressFut {
        future::ready("Hello world!".to_string())
    }

    fn generate_to_descriptor(
        self,
        _: context::Context,
        descriptor: String,
    ) -> Self::GenerateToDescriptorFut {
        future::ready("Hello world!".to_string())
    }

    fn generate_share(
        self,
        _: context::Context,
        address_or_descriptor: String,
    ) -> Self::GenerateShareFut {
        future::ready("Hello world!".to_string())
    }

    fn generate_share_to_address(
        self,
        _: context::Context,
        address: String,
    ) -> Self::GenerateShareToAddressFut {
        future::ready("Hello world!".to_string())
    }

    fn generate_share_to_descriptor(
        self,
        _: context::Context,
        descriptor: String,
    ) -> Self::GenerateShareToDescriptorFut {
        future::ready("Hello world!".to_string())
    }

    fn submit_block(self, _: context::Context, payload: String) -> Self::SubmitBlockFut {
        future::ready("Hello world!".to_string())
    }

    fn submit_share_block(self, _: context::Context, payload: String) -> Self::SubmitShareBlockFut {
        future::ready("Hello world!".to_string())
    }

    fn get_node_info(self, _: context::Context) -> Self::GetNodeInfoFut {
        let node_info = unsafe { NODE_INFO.clone() };

        if node_info.is_none() {
            return future::ready(None);
        }

        let node_info = node_info.unwrap().read().clone();
        future::ready(Some(node_info))
    }

    fn stop(self, _: context::Context) -> Self::StopFut {
        crate::global::EXIT_SIGNAL.store(true, Ordering::Relaxed);
        future::ready(format!(
            "Purplecoin Core v{} shutting down",
            env!("CARGO_PKG_VERSION")
        ))
    }

    fn uptime(self, _: context::Context) -> Self::UptimeFut {
        let startup = crate::global::STARTUP_TIME.load(Ordering::Relaxed);
        future::ready(crate::global::get_unix_timestamp_secs() - startup)
    }

    fn generate_wallet(
        self,
        _: context::Context,
        name: String,
        passphrase: String,
    ) -> Self::GenerateWalletFut {
        future::ready(Err(RpcErr::WalletAlreadyExists))
    }

    fn backup_wallet(
        self,
        _: context::Context,
        name: String,
        path: String,
    ) -> Self::BackupWalletFut {
        future::ready(Err(RpcErr::CouldNotBackupWallet))
    }

    fn backup_wallet_s3(
        self,
        _: context::Context,
        name: String,
        bucket: String,
        key: String,
        access_key_id: String,
        secret_access_key: String,
    ) -> Self::BackupWalletS3Fut {
        future::ready(Err(RpcErr::CouldNotBackupWallet))
    }

    fn get_network_info(self, _: context::Context) -> Self::GetNetworkInfoFut {
        future::ready("Hello world!".to_string())
    }

    fn get_peer_info(self, _: context::Context) -> Self::GetPeerInfoFut {
        let peer_table = unsafe { PEER_INFO_TABLE.clone() };

        if peer_table.is_none() {
            return future::ready(None);
        }

        let peer_table = peer_table.unwrap().read().clone();
        let peer_table: HashMap<_, _> = peer_table
            .iter()
            .map(|(id, v)| (id.to_base58(), v.clone()))
            .collect();
        future::ready(Some(peer_table))
    }

    fn get_connection_count(self, _: context::Context) -> Self::GetConnectionCountFut {
        future::ready(0)
    }

    fn get_net_totals(self, _: context::Context) -> Self::GetNetTotalsFut {
        future::ready("Hello world!".to_string())
    }

    fn add_node(self, _: context::Context, node: String) -> Self::AddNodeFut {
        future::ready("Hello world!".to_string())
    }

    fn list_banned(self, _: context::Context) -> Self::ListBannedFut {
        future::ready("Hello world!".to_string())
    }

    fn set_network_active(self, _: context::Context, active: bool) -> Self::SetNetworkActiveFut {
        future::ready("Hello world!".to_string())
    }

    fn validate_address(self, _: context::Context, address: String) -> Self::ValidateAddressFut {
        let res = bech32::decode(address.as_str());
        if res.is_err() {
            return future::ready(false);
        }
        let (hrp, _, variant) = res.unwrap();

        if hrp.as_str() != "pu" {
            return future::ready(false);
        }

        // Only the bech32m variant is allowed
        if let bech32::Variant::Bech32 = variant {
            return future::ready(false);
        }

        future::ready(true)
    }

    fn sign_message(
        self,
        _: context::Context,
        message: String,
        pub_key: String,
        priv_key: String,
        signing_ctx: String,
    ) -> Self::SignMessageFut {
        let decoded_priv = hex::decode(priv_key);

        if decoded_priv.is_err() {
            return future::ready(Err(RpcErr::InvalidPrivateKey));
        }

        let mut decoded_priv = decoded_priv.unwrap();
        let decoded_pub = hex::decode(pub_key);

        if decoded_pub.is_err() {
            decoded_priv.zeroize();
            return future::ready(Err(RpcErr::InvalidPublicKey));
        }

        let decoded_pub = decoded_pub.unwrap();
        let priv_key = SchnorSK::from_bytes(&decoded_priv);

        if priv_key.is_err() {
            return future::ready(Err(RpcErr::InvalidPrivateKey));
        }

        let pub_key = SchnorPK::from_bytes(&decoded_pub);

        if pub_key.is_err() {
            decoded_priv.zeroize();
            return future::ready(Err(RpcErr::InvalidPublicKey));
        }

        let mut priv_key = priv_key.unwrap();
        let pub_key = pub_key.unwrap();

        let ctx = signing_context(signing_ctx.as_bytes());
        let sig = priv_key.sign(ctx.bytes(message.as_bytes()), &pub_key);

        decoded_priv.zeroize();
        priv_key.zeroize();

        future::ready(Ok(hex::encode(sig.to_bytes())))
    }

    fn verify_message(
        self,
        _: context::Context,
        message: String,
        signature: String,
        pub_key: String,
        signing_ctx: String,
    ) -> Self::VerifyMessageFut {
        future::ready(Err(RpcErr::InvalidPublicKey))
    }

    fn verify_address(
        self,
        _: context::Context,
        address: String,
        pub_key: String,
    ) -> Self::VerifyAddressFut {
        let decoded_pub = crate::primitives::PublicKey::from_hex(pub_key.as_str());

        if decoded_pub.is_err() {
            return future::ready(Err(RpcErr::InvalidPublicKey));
        }

        let decoded_pub = decoded_pub.unwrap();
        let address_bech = decoded_pub.to_address().to_bech32("pu");

        if address_bech != address {
            future::ready(Ok::<bool, RpcErr>(false));
        }

        future::ready(Ok(true))
    }

    fn send_raw_tx(self, _: context::Context, transaction: String) -> Self::SendRawTxFut {
        future::ready(Ok("hello world".to_owned()))
    }

    fn query_output(self, _: context::Context, output_hash: String) -> Self::QueryOutputFut {
        future::ready(Ok("hello world".to_owned()))
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

// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use futures::{
    future::{self, Ready},
    prelude::*,
};
use serde::{Deserialize, Serialize};
use std::net::SocketAddr;
use tarpc::{
    client, context,
    server::{self, incoming::Incoming, Channel},
};

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
    async fn get_peer_info() -> String;

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
    async fn get_node_info() -> String;

    /// Attempts to gracefully shutdown Purplecoin
    async fn stop() -> String;

    /// Returns the number of seconds the server has been running
    async fn uptime() -> u64;

    /// Validates the given address
    async fn validate_address(address: String) -> bool;

    /// Signs a message with the given private key
    async fn sign_message_with_priv_key(
        message: String,
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
    type GetNodeInfoFut = Ready<String>;
    type StopFut = Ready<String>;
    type UptimeFut = Ready<u64>;
    type GenerateWalletFut = Ready<Result<String, RpcErr>>;
    type BackupWalletFut = Ready<Result<String, RpcErr>>;
    type BackupWalletS3Fut = Ready<Result<String, RpcErr>>;
    type GetNetworkInfoFut = Ready<String>;
    type GetPeerInfoFut = Ready<String>;
    type GetConnectionCountFut = Ready<u64>;
    type GetNetTotalsFut = Ready<String>;
    type AddNodeFut = Ready<String>;
    type ListBannedFut = Ready<String>;
    type SetNetworkActiveFut = Ready<String>;
    type ValidateAddressFut = Ready<bool>;
    type SignMessageWithPrivKeyFut = Ready<Result<String, RpcErr>>;
    type VerifyMessageFut = Ready<Result<bool, RpcErr>>;
    type VerifyAddressFut = Ready<Result<bool, RpcErr>>;

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
        future::ready("Hello world!".to_string())
    }

    fn stop(self, _: context::Context) -> Self::StopFut {
        future::ready("Purplecoin shutting down".to_string())
    }

    fn uptime(self, _: context::Context) -> Self::UptimeFut {
        future::ready(0)
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
        future::ready("Hello world!".to_string())
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
        future::ready(false)
    }

    fn sign_message_with_priv_key(
        self,
        _: context::Context,
        message: String,
        priv_key: String,
        signing_ctx: String,
    ) -> Self::SignMessageWithPrivKeyFut {
        future::ready(Err(RpcErr::InvalidPrivateKey))
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
        future::ready(Err(RpcErr::InvalidPublicKey))
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

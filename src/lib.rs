// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

//! # ℙurplecoin
//! Official implementation of Purplecoin, the first stateless cryptocurrency. Requires Rust `v1.63.0`.
//!
//! ## Features
//! * **Scalable**: Purplecoin is made up of 256 shards, each representing a different blockchain that processes transactions concurrently. The average transaction size is `450 bytes`, with a maximum block size of `750kb`, and a production rate of 256 blocks per 30 seconds we can achieve **~15000 transactions per second** on a blockchain system that has roughly the same safety guarantees as Bitcoin.
//! * **Decentralized & Secure**: Scalability usually comes at the cost of centralization. For example Proof of Stake consensus is scalable and green but brings the security of the network in the hands of the few. Purplecoin fully uses Proof of Work, the most secure and decentralized consensus algorithm. Miners secure the network as is the case of Bitcoin
//! * **Stateless**: Nodes are not required to store all past transactions in order to validate new blocks. **A miner only requires storing the latest 50 block headers of each shard, which total a size of 20mb, in order to start mining and fully validating new blocks across all shards**. This means that miners and ultra-light nodes **can run in memory only mode and and still be able to fully validate blocks**.
//! * **Fast Sync**: Due to the stateless design, nodes without a transaction history do not have to download all of the blocks from genesis and can synchronize with the network **in seconds**. Further, the overhead of querying the past transactions history from a fresh node that has just synced to the network, is `size_of_transactions + ~100mb * 256` per year queried. **This means that synchronising a fresh node with 10 years of transaction history in total of 1GB in size takes under 8 minutes on a 100mb/s internet connection**. Furthermore, we can still validate new blocks while querying for past transactions. For comparison, synchronizing with the Bitcoin network, regardless of the number and timespan of transactions, takes several days using the same internet speed.
//! * **Energy Efficient**: Green PoW implementation designed to reduce energy consumption from mining up to 50%
//!
//! ## Use cases
//! * **E-Notary**: Due to achieving scalability at the consensus and state layers, Purplecoin can function as an e-notary tool. In order to prove a document has been filed, one only needs the document itself and the witness for the state update. By providing only the document itself, the witness can be queried from archival nodes in `O(log n)` time where `n = current shard height`. In case of non-encrypted, public documents, the blockchain can serve as a decentralized repository of such documents and can be efficiently queried.
//! * **Decentralized File Storage**: An overlay protocol can be implemented where files are stored in encrypted form on the blockchain and can be efficiently queried.
//! * **Decentralized Order Book Exchange**: The stateless nature of Purplecoin allows decentralized trading without using AMMs but instead using a traditional order book model. Liquidity providers (traditional market makers in our case) can withdraw liquidity at will without compromising the security of the system. Advanced trading strategies can be implemented same as in a traditional Order Book exchange.
//! * **Transact/Trade Bitcoin, Ethereum, other coins or FIAT with lower fees**: The transaction format of Purplecoin coupled with the OBDEX implementation allows transacting with alternative currencies without ever owning any purplecoins. Assuming stablecoin implementations will emerge after launch, one can buy stablecoins or wrapped coins on the Purplecoin blockchain, transact or trade using them, then withdraw them at a later date, all without owning purplecoins. **Any token built on top of the Purplecoin blockchain, except NFTs, can be used to pay transaction fees**.
//!
//! ### Advantages when compared to Bitcoin
//! * Scalable
//! * Schnorr signatures
//! * Advanced smart contracts
//! * Merkelized Abstract Syntax Trees
//! * Constant chain size
//! * Decentralized mining pools
//! * Multi-asset
//! * Can be mined using the CPU
//! * Can be mined on a smartphone
//!
//! ### Disadvantages when compared to Bitcoin
//! * If one transfer involves outputs stored on multiple shards, it requires settlement on each involved shard. Atomicity is possible only on single-shard transfers
//! * Since nodes are not required to store the whole UTXO set in order to validate new blocks, light-nodes have to download their balances from an external party such as a long-running archival node. In theory, there is the non-zero possibility that no node on the network will store the unspent outputs if there is no node online specifically listening for them. In practice, this will almost definitely not happen but can introduce a DOS vector for light-nodes
//!
//! ### Advantages when compared to Ethereum v1.0
//! * Scalable
//! * Schnorr signatures
//! * Constant chain size
//! * Decentralized mining pools
//! * Can be mined using the CPU
//! * Can be mined on a smartphone
//!
//! ### Disadvantages when compared to Ethereum v1.0
//! * No global state, all contract state is passed as an input to the contract
//! * Contracts cannot interact with other contracts
//!
//! ### Advantages when compared to Ethereum v2.0
//! * Simple architecture, more easily provable that it is decentralized/secure
//! * Due to the simpler architecture, a higher number of shards is possible, which equals better scalability
//! * Energy efficient while not using Proof of Stake, which brings a degree of centralization as a cost to energy efficiency
//!
//! ### Disadvantages when compared to Ethereum v2.0
//! * While the Green PoW mining model used in Purplecoin is 50% energy efficient, Proof of Stake is 98% energy efficient
//!
//! ## Donations
//! While the development of Purplecoin initially happened in the sphere of Purple Technologies, it is not backed in any way by it or any other company. Purple Technologies is a for-profit company while Purplecoin is a decentralized project. Thereforce, the decisions and development happens at the community level. As such, the project also relies on the community at a funding level.
//!
//! If you wish to support the development of Purplecoin, donations can be sent to the following BTC address: `bc1qp3lyr0dhly4k7ku2a6hhdrgwmurfsr9f5vz4xm`

#![allow(dead_code, unused)]
#![feature(trivial_bounds)]

pub mod chain;
pub mod codec;
pub mod consensus;
pub mod global;
pub mod miner;
pub mod node;
pub mod primitives;
pub mod settings;
pub mod vm;
pub mod wallet;

#[cfg(feature = "gui")]
pub mod gui;

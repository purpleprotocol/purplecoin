# ℙurplecoin
[![Discord](https://img.shields.io/discord/435827644915777536.svg)](https://discord.gg/UCYWSsd) [![_pdf whitepaper](https://img.shields.io/badge/_pdf-whitepaper-blue.svg)](https://github.com/purpleprotocol/purplecoin_whitepaper/raw/main/whitepaper.pdf)

Official implementation of Purplecoin, the first stateless sharded cryptocurrency. Requires Rust Nightly `>=v1.70.0`, CMake, Clang.

**WARNING** The source code is still under heavy development. Use at your own risk.

## Building
Check out the [build instructions](https://github.com/purpleprotocol/purplecoin/blob/main/BUILDING.md) for each platform.

## Features
* **Scalable**: Purplecoin is made up of 256 shards, each representing a different blockchain that processes transactions concurrently. The average transaction size is `450 bytes`, with a maximum block size of `380kb`, and a production rate of 256 blocks per 30 seconds we can achieve **~12000 transactions per second** on a blockchain system that has roughly the same safety guarantees as Bitcoin. Shards are processed in groups, called "shard sectors" in order to stabilise the required hashrate to successfuly attack the system.
* **Decentralized & Secure**: Scalability usually comes at the cost of centralization. For example Proof of Stake consensus is scalable and green but brings the security of the network in the hands of the few. Purplecoin fully uses Proof of Work, the most secure and decentralized consensus algorithm. Miners secure the network as is the case of Bitcoin
* **Stateless**: Nodes are not required to store all past transactions in order to validate new blocks. **A miner only requires storing the latest 50 block headers of each shard, which total a size of 20mb, in order to start mining and fully validating new blocks across all shards**. This means that miners and ultra-light nodes **can run in memory only mode and and still be able to fully validate blocks**.
* **Fast Sync**: Due to the stateless design, nodes without a transaction history do not have to download all of the blocks from genesis and can synchronize with the network **in seconds**. Furthermore, we can still validate new blocks while querying for past transactions. For comparison, synchronizing with the Bitcoin network, regardless of the number and timespan of transactions, takes several days using the same internet speed. When using a trusted bridge, there is no need to query past blocks as the bridge stores and manages the UTXO set.
* **Energy Efficient**: Green PoW implementation designed to reduce energy consumption from mining up to 50%

## Use cases
* **E-Notary**: Due to achieving scalability at the consensus and state layers, Purplecoin can function as an e-notary tool. In order to prove a document has been filed, one only needs the document itself and the witness for the state update. In case of non-encrypted, public documents, the blockchain can serve as a decentralized repository of such documents and can be efficiently queried.
* **Decentralized File Storage**: An overlay protocol can be implemented where files are stored in encrypted form on the blockchain and can be efficiently queried.
* **Decentralized Order Book Exchange**: The stateless nature of Purplecoin allows decentralized trading without using AMMs but instead using a traditional order book model. Liquidity providers (traditional market makers in our case) can withdraw liquidity at will without compromising the security of the system. Advanced trading strategies can be implemented same as in a traditional Order Book exchange.
* **Transact/Trade Bitcoin, Ethereum, other coins or FIAT with lower fees**: The transaction format of Purplecoin coupled with the OBDEX implementation allows transacting with alternative currencies without ever owning any purplecoins. Assuming stablecoin implementations will emerge after launch, one can buy stablecoins or wrapped coins on the Purplecoin blockchain, transact or trade using them, then withdraw them at a later date, all without owning purplecoins. **Any token built on top of the Purplecoin blockchain, except NFTs, can be used to pay transaction fees**.

### Advantages when compared to Bitcoin
* Scalable
* Schnorr signatures
* Advanced smart contracts
* Merkelized Abstract Syntax Trees
* Constant chain size
* Decentralized mining pools
* Multi-asset
* Can be mined using the CPU
* Can be mined on a smartphone via decentralized mining pools

### Disadvantages when compared to Bitcoin
* If one transfer involves outputs stored on multiple shards, it requires settlement on each involved shard. Atomicity is possible only on single-shard transfers
* Since nodes are not required to store the whole UTXO set in order to validate new blocks, light-nodes have to download their balances from an external party such as a long-running archival node. In theory, there is the non-zero possibility that no node on the network will store the unspent outputs if there is no node online specifically listening for them. In practice, this will almost definitely not happen but can introduce a DOS vector for light-nodes

### Advantages when compared to Ethereum v1.0
* Scalable
* Schnorr signatures
* Constant chain size
* Asynchronous smart contracts
* Re-entrancy attacks are impossible by design
* Decentralized mining pools
* Can be mined using the CPU
* Can be mined on a smartphone

### Disadvantages when compared to Ethereum v1.0
* Contracts are cannot have a global state as they are encoded as input spending conditions. While this is better performance wise as it allows us to parallelise contract execution, state modeling is much harder. State can only be passed from an input to the next output.
* Contracts can only interact with contracts found in the same transaction

### Advantages when compared to Ethereum v2.0
* Simple architecture, more easily provable that it is decentralized/secure
* Due to the simpler architecture, a higher number of shards is possible, which equals better scalability
* Energy efficient while not using Proof of Stake, which brings a degree of centralization as a cost to energy efficiency

### Disadvantages when compared to Ethereum v2.0
* While the Green PoW mining model used in Purplecoin is 50% energy efficient, Proof of Stake is 98% energy efficient

## Donations
While the development of Purplecoin initially happened in the sphere of Purple Technologies, it is not backed in any way by it or any other company. Purple Technologies is a for-profit company while Purplecoin is a decentralized project. Therefore, the decisions and development happens at the community level. As such, the project also relies on the community at a funding level. 

If you wish to support the development of Purplecoin, donations can be sent to the following BTC address:
```
bc1qwf7lcc8rsm75c54fmkrpl8s6g57gsp4zh5n34q
```

Donations can also be sent to the following ETH address:
```
0x8948F2d65Fa48cB10Aeb2C91930b7f9d28b2E885
```

## Development

### Dependency vendoring
All dependencies used by Purplecoin are vendored under the ./vendor directory. In order to add a new dependency to the project, add the dependency to the Cargo.toml file first. After that, run the following command to vendor the new dependency:
```
cargo vendor --versioned-dirs ./vendor/crates
```

### Cargo Clippy & Format
Before merging any changes into the `main` branch, the Clippy lints must be checked and applied, followed by a code format. In order to achieve this, the following commands must be run:
```
cargo +nightly clippy --workspace --fix

cargo +nightly fmt --all
```

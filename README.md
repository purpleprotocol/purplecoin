# ℙurplecoin
[![Discord](https://img.shields.io/discord/435827644915777536.svg)](https://discord.gg/UCYWSsd) [![_pdf whitepaper](https://img.shields.io/badge/_pdf-whitepaper-blue.svg)](https://github.com/purpleprotocol/purplecoin_whitepaper/raw/main/whitepaper.pdf)

Official implementation of Purplecoin, the first stateless cryptocurrency. Requires Rust Nightly `>=v1.63.0`.

**WARNING** The source code is still under heavy development. Use at your own risk.

## Running tests
Type the following to run the test suite:
```
cargo +nightly test
```

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

## Architecture
More details about the architecture.

### Sharded Nakamoto Consensus 
Purplecoin uses Sharded Nakamoto Consensus to scale beyond the limited transaction throughput of traditional blockchains such as Bitcoin or Ethereum. 

Instead of storing a single blockchain of transactions, we would instead store `n` blockchains with the same consensus rules, each with its own UTXO set and Proof of Work.

In this way, the total balance can be represented as the sum of unspent outputs across all shards. Each shard is an independent blockchain with independent consensus. In this way, transactions are processed concurrently. 

For example let's assume Alice wants to send Bob 10 XPU. Alice has two unspent outputs: 7 XPU on shard A and 5 XPU on shard B. She would then create two independent transactions on shard A and B which would create one output of 7 XPU on shard A that Bob can spend and two outputs on shard B: one for 3 XPU which Bob can spend and a 2 XPU change output which Alice can spend.

### Scalability benefits of Sharded Nakamoto Consensus
In Sharded Nakamoto Consensus, the total transaction throughput of the system is equal to the throughput of a single chain times the number of shards.

For example, let's suppose that a single shard can process 12 transactions per second, roughly the throughput of the Ethereum blockchain. In the case of Purplecoin, we have 256 equivalent chains that process transactions concurrently, yielding a total of 12 * 256 = 3072 TPS. While of course in our case some transactions might span multiple shards thus creating overhead when compared to a single chain, it would be very rare that a transaction spans all of the shards.

### Downsides of Sharded Nakamoto Consensus
The design of this system, however, implies certain downsides compared to traditional blockchain systems:
* The sharded architecture makes atomic transfers across shards impossible. In the case atomicity is required, a transfer on a single shard should be performed.
* Shards are independent blockchains, requiring a full-node to process multiple blockchains at the same time. Of course, a full-node can actually be a cluster of nodes, each processing and storing one or several of the shards.
* Multi-shard transfers might be partially reversed in case of a fork.

### Partially spendable outputs
Outputs can be partially spent according to spending script rules, allowing things such as an atomic decentralized asset exchange mechanism.

### Decentralized asset exchange
By allowing outputs to be partially spent, and by combining different spending conditions, we can build a decentralized asset exchange where quotes are posted off-chain but settlements happen atomically on-chain. For example, let's asume we have a stablecoin named XUSD with a 1:1 exchange rate to 1 USD, now for the sake of example let's assume 1 XPU is worth 10 XUSD and we pay a miner fee of 0.01 XPU:

* Alice has one output of 10 XUSD and wants to exchange 5 XUSD for XPU
* Bob has 1 XPU output he quotes using a spending condition for 10 XUSD.
* Alice creates a transaction with the following inputs: Bob's XPU input, Alice's XUSD input and it creates the following outputs:
  - Output of 5 XUSD to Bob
  - Output of 5 XUSD to Alice
  - Output of 0.5 XPU to Bob, with the same spending conditions as his previous output
  - Output of 0.49 XPU to Alice
  - Remaining 0.01 XPU is the miner fee paid by Alice

In the same vein, let's suppose we have another stablecoin XEUR with a 1:1 exchange rate to 1 EUR. Now let's suppose the exchange rate for XEUR to XUSD is 1.2 and the exchange rate of 1 XPU to XEUR is 8 and we pay a miner fee of 0.01 XPU:

* Alice has one output of 20 XUSD and she wants to exchange 10 XUSD for XEUR. She does not have any XPU outputs.
* Bob has one output of 50 XEUR he quotes in exchange for XEUR at a price of 1.2. He does not have any XPU outputs either.
* Charlie has one output of 1 XPU he quotes in exchange for XUSD at a price of 10.
* Alice creates a transaction with 3 inputs: her own XUSD output, Bob's 50 XEUR output and Charlie's 1 XPU output. It creates the following outputs:
    - Output of 42 XEUR to Bob
    - Output of 10 XUSD to Bob
    - Output of 9.99 XUSD to Alice
    - Output of 8 XEUR to Alice
    - Output of 0.99 XPU to Charlie
    - Output of 0.1 XUSD to Charlie
    - Remaining 0.01 XPU is the miner fee paid by Alice

In this example, there is one issue for Charlie: The amount received in exchange for paying the fee, 0.1 XUSD could be too small in order to be able to economically spend the output. The solution for this is liquidity providers setting a minimum allowable exchange quantity in their quote.

### Quote adjustment
Adjusting quotes poses one big challenge in this design: 
* Once a quote is posted, anyone can accept it. If a quote is updated to a better price for the liquidity provider, someone can still settle the first transaction, invalidating the updated quote. 
* This means adjusting quotes can only be done upward in case of buy quotes and downward in case of sell quotes, very similarly to how a Dutch auction works. Strategies can then be implemented around this by adjusting the time until expiry and price parameters of a quote update.

#### Comparison with liquidity pools
We can quickly see that this mechanism resembles a traditional Order Book exchange. This brings several advantages to liquidity pools:
* Stateless design
* Market and limit orders
* No need to lock liquidity in the pool for a long time; Liquidity providers are able to access profits after each trade

### Cryptography
Purplecoin uses Schnorr implemented over Ristretto (sr25519) as its signature algorithm and blake3 as the choice of hash function.

### Green PoW
Purplecoin uses the Green PoW model which lowers the energy consumption of mining to up to 50%.

### ASIC resistance
Purplecoin uses 2 Proof of Work algorithms in tandem: RandomX and a choice out of several hash functions. One is suited to CPU mining and the other for ASIC miners. Algorithms are switched every Green PoW epoch.

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

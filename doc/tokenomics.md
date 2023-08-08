## Purplecoin Tokenomics
This document describes token economics for Purplecoin. Please note that the following values, except the amount of pre-mined coins which are distributed across all shards, apply for each shard.
* Total supply before tail emission: 2,378,392,912 XPU
* Coins from mining: 2,150,398,912 XPU
* Pre-mined coins: 227,994,000 XPU
* Block time: 30 seconds
* Initial block reward: 16 XPU per sector, with 16 sectors, 256 XPU is created every 30 seconds
* Halving period: 4.2 million blocks (4 years).
* Total halvings: 20 halvings after which tail emission of 0.00006103 XPU applies indefinitely

### Blockchain credits
XPU can be thought of as credits to use the Purple Protocol. In the same way cloud credits can be used for public clouds. XPU does not offer returns, dividends, or any kind of periodic revenue. XPU can be bought and sold via the atomic swap mechanism. This mechanism allows sending and receiving any assets or FIAT without owning XPU.

### Example usage
Let's asume we have a stablecoin named XUSD with a 1:1 exchange rate to 1 USD, now for the sake of example let's assume 1 XPU is worth 10 XUSD and we pay a miner fee of 0.01 XPU:

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

This happens by transacting through either a DEX or a CEX. The difference is that on a DEX quotes are posted off-chain somewhere and on a CEX they are hosted on a centralised exchange with its own fees and rules. The wallet can be hooked to either according to the user's wishes.

### High distribution
XPU is highly distributed both in the crowdsale (via a low individual cap), and at the mining level. It should be close to impossible for a single miner to receive the whole reward for all shards at once. This is because each shard has a different required PoW algorithm at any individual moment. A miner would have to hold a large proportion of the hashrate of all PoW algorithms (GR, Sha256, Blake2, Fugue, JH, etc) in order to receive the whole reward.

Miner monopolies are much harder to attain in Purplecoin. First-class support for decentralised mining pools is also included.

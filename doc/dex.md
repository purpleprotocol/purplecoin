## Decentralized asset exchange
A decentralised asset exchange can be theoretically implemented on top of Purplecoin.

### Partially spendable outputs
Outputs can be partially spent according to spending script rules, allowing things such as an atomic decentralized asset exchange mechanism.

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
* No need to lock liquidity in the pool for a long time; Liquidity providers are able to access profits after each trade.

### Frontrunning
Unfortunately, as liquidity is posted publicly and taker orders are also being sent publicly through the mempool, a DEX will always be susceptible to frontrunning. The only way to avoid this is, is either to use a similar exchange but with a private order book, or to swap with someone directly.

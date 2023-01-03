## Purplecoin Scripting
Purplecoin, similarly to Bitcoin, provides a scripting language for encoding spending rules on the blockchain.

### Turing Completeness
While our scripting language is inspired by that of Bitcoin, which is Turing Incomplete by design, we also introduce loop constructs in our case and as such Purplecoins scripting language can be called Turing Complete.

### The Halting Problem
The issue with a Turing Complete language in our case is the Halting Problem, which states that we cannot determine prior to executing a program that it will run forever or stop. In the case of Bitcoin, this problem does not exist as it does not have loop constructs. 

We handle this similarly to how it is handled in Ethereum, by introducing the concept of gas, with a few differences. When a transactions gas runs out, the execution is halted.

### Gas limit
In Purplecoin, there are two gas limits: a per block gas limit and a per transaction gas limit. These cannot be chosen by the transaction emitter and are hardcoded such that a single block remains within the bounds of normal processing times even if all the gas in a block is consumed.

If a script requires more gas than the implicitly allocated amount, it can yield execution by flushing the current state to the script output stack and continue execution in a new transaction by paying the fee again.

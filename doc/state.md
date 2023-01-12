## State model
Purplecoin is the first stateless blockchain. As such, the way we reason with state is completely different from other blockchain implementations.

### Stateless validation
First of all, what is a stateless blockchain? To put it simply, **a stateless blockchain validates a new block and its transactions, without any information other than the previous block header**. All required information to perform consensus is sent over the wire along with the new transactions in a  block. In a stateless blockchain, in theory, all other block headers besides the latest one can be pruned and block validation can be performed identically as a full-node. In practice, we store the latest 50 headers to handle potential forks. After 50 confirmations, a block is considered final.

This is in stark contrast to all other blockchain protocols, which require validating all transactions from genesis or a checkpoint and store a database of transactions which grows over time.

While headers can be pruned, the UTXO set in case of Bitcoin which at the time of writing is `3gb`, cannot be pruned or else it would break validation. It is the same case with Ethereum's state trie, which is around `130gb`. In our case, a node would have to store `20mb` of headers in order to validate new blocks.

This means the initial sync is more or less instant. When using a bridge, further syncs are also instant.

### Dynamic Cryptographic Acumulator
A cryptographic accumulator allows us to prove that an item belongs to a set without knowledge of the set itself. A static accumulator has a fixed set size, while a dynamic accumulator allows us to add and delete elements from the set.

We employ the RSA accumulator as the representation of our UTXO set. The RSA accumulator is 256 bits in size and we can use it to store an arbitrary number of unspent outputs.

When spending an output, we must provide the output `O` and witness `W` as an input to a transaction. `W` must be updated with every new block. As such, managing the whole global UTXO set would ultimately become unfeasible. This also requires nodes managing a subset of the UTXO set to maintain system liveness. These nodes are called bridges.

### Sharded UTXO set and Bridges
**The rule of thumb is that in Purplecoin, everyone is ultimately responsible for storing their UTXO set**. This can be done in the following ways:
* Running a personal bridge. The caveat is that a personal bridge should be online at all times in order to update the witness set.
* Relying on a public bridge. A public bridge might for example manage the entire UTXO set of a single asset as long as it isn't too large. Or one asset can be split among different public bridges. The caveat is that this relies on the goodwill of others as running a bridge can become expensive.
* Using a private bridge. A private bridge is a business which offers to manage the UTXO set of private clients in exchange of a fee. For example, in the future banks might offer such services. A private bridge can either only store the UTXO set of a client, part of their keys in a multi-sig setup, or entirely manage their private keys.

Ultimately, it is up to the user to choose how they manage their UTXO set, in the same way as it is up to them to choose how they manage their private keys. While this is inconvenient when compared to Bitcoin, as it adds another type of data the user is required to manage besides private/public keys, it is the cost of scalability.

Another way to explain it is that in Purplecoin, the UTXO set is stored off-chain while the only thing that is kept on-chain is the cryptographic accumulator of the UTXO set.

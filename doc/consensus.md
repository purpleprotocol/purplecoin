### Sharded Nakamoto Consensus 
Purplecoin's consensus algorithm works like a kind of Sharded Nakamoto Consensus. 

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

## Sectors
Shards are grouped into sectors in the consensus model of Purplecoin.

### Sector chain
A shard sector is composed of different shards, which can be processed independently as long as the corresponding Sector chain responsible for the sector is also processed.

The Sector chain does not contain any transaction body, but rather the root hash of blocks. Miners append blocks to the Sector chain and the shards in the sector.

## Rules
* In total, there are 16 Sector chains, each with its own sector composed of 16 shards. Each
shard sector is processed concurrently and without any communication with other sectors.

* Each PoW block must include the merkle root of the corresponding 16 blocks situated in its sector.

* As each block has a maximum size of `380kb`, the network will have to propagate a maximum
of `6mb` of transactions for a block to be placed in each shard in a sector. As nodes do not need to
store the UTXO set in order to validate new transactions, this is fine.

## Design rationale
By using a single chain as the Proof of Work source of truth for multiple shards, we bypass
the limitation of sharded PoW blockchains where the total hashpower required to perform a 51%
attack is divided by the number of shards. For example, the safest sharded chain model would
be a single Sector chain acting as source of truth to 256 shards. This alone increases the scalability
of the system by allowing node operators to split the workload locally across multiple nodes. However,
this doesn't really help node operators with limited hardware.

Sharding is further employed at the PoW source of truth layer, by sharding the Sector chain into
16 different chains, each responsible for a sector of 16 shards, each processed independently.

In this case, the system becomes exposed to the hashpower partition problem we described earlier: the total
hashpower percentage required to perform an attack on a single sector decreases from `51%` to `51/16 = 3.1875%`
of the total hashpower. In order to defend against attacks, we leverage the runnerup election system of
Green PoW in order to artificially increase the hashpower required to successfuly execute an attack.

We require 15 runnerup blocks instead of 1 in order for a second round block to be mined. In this case,
you would need `3.1875 * 16 = 51%` of the total hashpower in order to successfuly perform an attack.
The attacker would have to mine the first round block along with all the other required runnerup
headers faster than everyone else.

We further employ an efficient set reconciliation strategy where only missing transactions
from a block are needed to be transmitted during initial propagation. As an average 80% of
a new block's transactions are usually in any node's mempool we reduce the average upload
bandwidth required for propagating a batch for a single node. This is further reduced by running a node
in cluster mode.

### Why not use a single large block
Purplecoin does not suffer from the UTXO set explosion problem, as Bitcoin or other
cryptocurrencies do. We could have easily just used the traditional Nakamoto consensus
and increased the block size without hurting decentralization. However, this design
brings additional scalability benefits:

* Shards can be independently validated by nodes, allowing node operators to scale their setup
much more easily than in traditional cryptocurrencies where a single node can scale their disk
IOPS and CPU cores but not their bandwidth.

* For example, we can run a node in cluster mode where shards can be partitioned between different
nodes with different disks and network interfaces, possibly running in different data-centers.
Very similarly to how, for example, Apache Cassandra is deployed in production. We can further
add things such as disaster recovery systems and multi AZ deployments.

* Nodes in the same cluster receiving a new batch of blocks only need to synchronize between themselves
all the validation results of the batch in order for it to be accepted, otherwise all shards can be
downloaded independently by each node in the cluster.

* This is very useful, for example, for archival nodes which store the whole UTXO set and past transactions.
It is also very useful for both quickly querying the blockchain for past transactions and allowing archival
nodes running in cluster mode to serve a much larger number of requests.
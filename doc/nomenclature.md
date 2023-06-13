## Nomenclature 
This document describes the nomenclature of things related to Purplecoin and the Purple Protocol:

* `Purple Protocol` - The Purple Protocol is the name of the peer to peer blockchain protocol.
* `Purplecoin` - Purplecoin is the base token used to pay fees to use the Purple Protocol.
* `XPU` - Shortened version of Purplecoin.
* `purple satoshis or psats` - The smallest denomination of XPU. One XPU has 18 decimal places. Chosen in honour of the mysterious creator of Bitcoin, Satoshi Nakamoto. In order to differentiate between satoshis in Bitcoin and in Purplecoin, we shall refer to satoshis in Purplecoin as `purple satoshis` or `psats` for short.
* `Sector` - A set of 16 shards.
* `Sector chain` The proof of work chain acting as source of truth for the sector. A single block in the sector chain must contain the root hash of all blocks at the same height in all shards in the sector.
* `Shard` - Logical partition of the state. Transactions are not possible between shards. 
* `Mining epoch` - Two successive blocks. The proof of work algorithm changes each epoch. Only successful miners of uncles of the first block can mine the second block.
* `Bridge node` - Full-node storing the assets of others according to specific rules e.g. Store only XPU outputs.
* `Cluster node` -  A full-node deployed as a cluster of smaller nodes.
## Asset model
Purplecoin uses the UTXO model as a way to store assets encode assets in the ledger. This is heavily inspired by Bitcoin and the scripting language is similar to Bitcoin as well.

We however introduce a few modifications to both the scripting language and the transaction format used in Bitcoin. 

## Dynamic transaction outputs
In order to save bandwidth, transaction outputs are computed dynamically at runtime and only the transaction inputs are included in the block. This is in stark contrast to Bitcoin where outputs are also encoded in blocks. 

While in Bitcoin, spending scripts are written fully inline and thus can only follow static execution paths, in Purplecoin they are parameterised.

We can such create more complex spending conditions and outcomes with this model. For example, in the case of asset exchange, we can encode an output as being spendable by either its owner or by someone wishing to exchange another asset against it. A parameter would be the amount being exchanged, and another would be the destination address. The spending script also checks if there is another output included by the buyer to the seller with the correct amount.

## Coloured assets
Purplecoin offers the ability to create alternative assets encoded at the protocol layer, meaning, they are transacted in the same way as Purplecoins. 

### Coloured addresses
Since we have 256 shards that do not communicate between each other in any way shape or form, we have to employ a strategy that provides asset uniqueness across all shards without communication. 

The way this is resolved is by using special addresses for each encoded asset. This is a normal Purplecoin address:
```
pu1wyzgxpzedr24l28ku8nsfwd2h4zrsqas69s3mp
```

And this is an example coloured Purplecoin address:
```
pu1l4ccz4c0wchw7afxzfmgfq8wrjbusfmqn05d8d7dsunv4kdgkw5utzvduyaqhyjfhva3ey0q4a9w
```

While a normal Purplecoin address has 20 bytes, a coloured address is encoded as 40 bytes, with the first 20 bytes being the spending script hash and the rest of the 20 bytes being the asset script hash.

In this way, an asset can be created across all shards, without any communication between them. The asset script can also limit asset creation to a subset or individual shards.

### Asset scripts
Asset scripts are provided along with spending scripts in the case of coloured outputs and they provide the initial emission rules, and additional arbitrary spending conditions at the asset level.

### Asset idempotency
In order to provide idempotency in case of coloured assets, the asset script must include a block hash and height such that it is situated in the past 50 blocks. All nodes must store the past 50 blocks and will not include any duplicate asset during this window. The creator's address is also encoded in the asset script and must match the sender of the coinbase transaction. 

If the encoded block hash and transaction height are behind the past 50 blocks, the coinbase transaction for the asset will be rejected.

In this way, assets cannot be duplicated and each asset hash remains unique.
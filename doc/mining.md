## Mining explanation
We are using the [Green PoW](https://arxiv.org/pdf/2007.04086.pdf) consensus model which elapses in epochs. Each epoch has 2 rounds. In the first round, every miner participates and has the potential to mine a block. The miner who finds the solution in the first round is not entitled to participate in the second round. Then, the rest of the miners continue mining the block in the first round. 

When at least 16 miners manage to mine the block, the second round begins. These miners are called runner-ups. Only runner-ups are entitled to mine the block in the second round. Once one of the runner-ups mines the second round block, the next epoch begins. This mechanism brings energy efficiency to mining (up to 50% compared to if it wasn't employed) and secures shard sectors against 51% attacks. More details around this can be found in the Whitepaper. 

Now, every epoch will use a different algorithm. Half of the epochs will be mined exclusively with GhostRider, in order to prevent ASICs from mining a longer chain while allowing CPU/GPU mining. The other half of the epochs will be mined with an ASIC friendly algorithm, chosen randomly every epoch. This is in order to balance GhostRider, as fully ASIC resistant algorithms are subject to hashpower marketplace attacks, while ASIC algorithms are less likely to be subject to these attacks. 

Example:
```
Epoch 1: GhostRider
Epoch 2: Sha256
Epoch 3: GhostRider
Epoch 4: Fugue
```

The following are the current proposed ASIC friendly algorithms:
* Blake2s256
* Blake2b512
* Sha256
* Keccak256
* JH
* Fugue

### Mining strategies
As in our case multiple algorithms are used across multiple chain sectors, a miner might choose a strategy in order to maximise their return. Naturally, miners will gravitate towards the chain with the lowest difficulty, thus creating a difficulty arbitrage effect.

A few strategies might include:
* Mining with a single algorithm and sector at the same time.
* Mining different sectors with a single algorithm at the same time.
* Mining a single sector with multiple algorithms at the same time using different hardware but waiting for each algorithm to appear in the queue.
* Mining multiple sectors with multiple algorithms at the same time.

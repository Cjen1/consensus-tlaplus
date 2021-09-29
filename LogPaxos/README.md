# LogPaxos
This is a TLA+ specification of the LogPaxos protocol described on [Decentralised Thoughts](TODO).

It is adapted from the Paxos specification in this repository.

## Model Checking
To model check it, either open the specification in the TLA+ Toolbox and add a new model, or run `tlc2 MC.tla`. This checks a three node cluster, over two ballot numbers and which decides one of two values.

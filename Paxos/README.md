# Paxos
This is a Paxos specification adapted and abstracted from the [TLA+ example](https://github.com/tlaplus/Examples/blob/master/specifications/Paxos/Paxos.tla) by Lamport et. al.

It abstracts away certain parts of the protocol in order to highlight similarities with LogPaxos.

## Model Checking
To model check it, either open the specification in the TLA+ Toolbox and add a new model, or run `tlc2 MC.tla`. This checks a three node cluster, over two ballot numbers and which decides one of two values.

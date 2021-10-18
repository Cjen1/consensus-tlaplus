---- MODULE LPSafe ----

EXTENDS LogPaxos, TLC

CONSTANTS MaxRound

FiniteRounds == 0..MaxRound

Symmetry == Permutations(Commands) \union Permutations(Acceptors) 

NoDuplicateCommands == \A m \in {m \in msgs: m.type = "2a"}: \A i,j \in DOMAIN m.bal.val: m.bal.val[i] = m.bal.val[j] => i = j

====

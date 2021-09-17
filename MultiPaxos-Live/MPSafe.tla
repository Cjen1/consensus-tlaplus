---- MODULE MPSafe ----
EXTENDS MultiPaxos, TLC

CONSTANTS MaxBallot

FiniteRounds == -1..MaxBallot

Symmetry == Permutations(Proposers) \union Permutations(Acceptors) \union Permutations(Values)

----

PossiblyDecided(l) ==
  \E Q \in Quorums, b \in BallotNumbers: 
    \A a \in Q: \E m \in msgs: /\ m.type = "2b"
                               /\ m.acc = a
                               /\ m.bal.bal = b
                               /\ Prefix(l, m.bal.val)

ImplicitConsistency ==
  LET 
      relevantMsgs == {m \in Messages: m.type = "2a"}
      proposedValues == {m.bal.val : m \in relevantMsgs}
  IN \A l1, l2 \in {l \in proposedValues: PossiblyDecided(l)}:
    Prefix(l1, l2) \/ Prefix(l2, l1)

====

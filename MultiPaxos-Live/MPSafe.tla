---- MODULE MPSafe ----
EXTENDS MultiPaxos, TLC

CONSTANTS MaxBallot

FiniteRounds == -1..MaxBallot

Symmetry == Permutations(Proposers) \union Permutations(Acceptors) \union Permutations(Values)

----

(* The system is consistent if any two proposers with committed logs, if one's ballot is greater it's log will extend the lower's one*)
Consistency ==
  \A p1, p2 \in Proposers: 
  (prop[p1].commitBal < prop[p2].commitBal) => Prefix(prop[p1].committed, prop[p2].committed)

(* A proposer should only ever extend its committed log. This should allow
 * reads to be served by the proposer. *)
ProposerConsistency ==
  \A p \in Proposers: Prefix(prop[p].committed, prop'[p].committed)

TemporalProperties ==
  [][ProposerConsistency]_prop

====

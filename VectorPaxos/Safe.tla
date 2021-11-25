---- MODULE Safe ----

EXTENDS VectorPaxos, TLC, Integers

Symmetry == Permutations(Commands) \union Permutations(Acceptors) \union Permutations(Proposers)

CONSTANT MaxBalNum
maxBalNum == 
  LET bals == {State.prop[p].balNum :p \in Proposers}
  IN Max(BallotNumLeq, bals).num

maxExpectedBalNums == 0..MaxBalNum

BallotConstraint == maxBalNum < MaxBalNum

Consistency == [][State.commit = None \/ State'.commit = State.commit]_<<State>>

=============================================================================
\* Modification History
\* Created Thu Sep 09 11:49:18 BST 2021 by cjen1

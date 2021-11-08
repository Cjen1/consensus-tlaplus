---- MODULE MC ----

EXTENDS VectorPaxos, TLC

CONSTANTS MaxBallotDepth

RECURSIVE GenerateBalNum(_)
GenerateBalNum(n) ==
  IF n = 1
  THEN {<<a,{}>> : a \in Proposers}
  ELSE LET prev == GenerateBalNum(n-1)
       IN UNION {{IncrementBallotNumber(b, b1) : b \in prev} : b1 \in prev} \cup prev

FiniteBallotNumbers == Print("FBN", GenerateBalNum(MaxBallotDepth))

Symmetry == Permutations(Commands) \union Permutations(Acceptors)

=============================================================================
\* Modification History
\* Created Thu Sep 09 11:49:18 BST 2021 by cjen1

---- MODULE Safe ----

EXTENDS VectorPaxos, TLC, Integers

Symmetry == Permutations(Commands) \union Permutations(Acceptors)

ILEQ(a,b) == a <= b

RECURSIVE BalDepth(_)
BalDepth(b) == 
  IF b = InitBalNum
  THEN 0
  ELSE 1 + Max(ILEQ, {BalDepth(b1): b1 \in b[2]})

MessageBallotNumbers == 
  LET nacks == {m \in msgs: m.type = "nack"}
      m1a == {m \in msgs: m.type = "1a"}
      m1b == {m \in msgs: m.type = "1b"}
      m2a == {m \in msgs: m.type = "2a"}
      m2b == {m \in msgs: m.type = "2b"}
  IN {m.balNum : m \in nacks} \cup 
     {m.balNum : m \in m1a}   \cup
     {m.balNum : m \in m1b}   \cup
     {m.bal.bal : m \in m2a}  \cup
     {m.bal.bal : m \in m2b}

NodeBallotNumbers ==
  LET accMBals == {acc[a].maxBalNum : a \in Acceptors}
      accMVBals == {acc[a].maxBal.bal : a \in Acceptors}
      propBals == {prop[p].balNum : p \in Proposers}
  IN accMBals \cup accMVBals \cup propBals

MaxBallotDepth == Max(ILEQ, {BalDepth(b) : b \in MessageBallotNumbers \cup NodeBallotNumbers})

CONSTANT MaxDepth
BallotConstraint == MaxBallotDepth <= MaxDepth

VARIABLES commit

Commitable(v) ==
  \E p \in Proposers:
  \E Q \in Quorums:
  \A a \in Q: \E m \in msgs: 
    /\ m.type = "2b"
    /\ m.bal = [bal |-> prop[p].balNum, val |-> v]
    /\ m.acc = a

TryCommit == 
  LET commitable == {v \in Commands: Commitable(v)}
  IN IF commitable = {}
     THEN commit' = commit
     ELSE \E v \in commitable: commit' = v

Consistency == [][commit = None \/ commit' = commit]_<<commit>>

ConsNext == Next /\ TryCommit

consvars == vars \o << commit >>

ConsistencySpec == Init /\ (commit = None) /\ [][ConsNext]_consvars

=============================================================================
\* Modification History
\* Created Thu Sep 09 11:49:18 BST 2021 by cjen1

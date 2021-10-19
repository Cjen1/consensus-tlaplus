------------------------------- MODULE Tempo -------------------------------

EXTENDS Utils, Integers,TLC

CONSTANTS Acceptors, P1Quorums, P2Quorums, Commands, BallotNumbers

VARIABLES msgs,
          acc

Bot == CHOOSE v : v \notin Commands

TimeStamps == Nat

Values == 
  LET AllValues == [cmd : Commands, ts : TimeStamps, fixup : {TRUE, FALSE}] \cup {[cmd |-> Bot, ts |-> 0, fixup |-> TRUE]}
  IN SUBSET AllValues

InitialValue == {[cmd |-> Bot, ts |-> 0, fixup |-> TRUE]}

LEQ(a,b) == \A va \in a: \E vb \in b: 
  /\ va.cmd = vb.cmd 
  /\ \/ /\ ~va.fixup 
        /\ vb.fixup 
	/\ va <= vb
     \/ va.ts = vb.ts

UpdatePrev(prev, c) == prev \cup {[cmd |-> c, ts |-> max(LAMBDA a,b : a <= b, {v.ts: v \in prev}) + 1, fixup |-> FALSE]}

CommandsRepresented(v) == {c.cmd: c \in v}

R == 
  INSTANCE OnePaxos WITH
    Acceptors <- Acceptors,
    P1Quorums <- P1Quorums,
    P2Quorums <- P2Quorums,
    Commands <- Commands,
    BallotNumbers <- BallotNumbers,
    msgs <- msgs,
    acc <- acc,
    Values <- Values,
    InitialValue <- InitialValue,
    LEQ <- LEQ,
    UpdatePrev <- UpdatePrev,
    CommandsRepresented <- CommandsRepresented

Spec == R!Spec

TypeInvariant == R!TypeInvariant

ProtocolCommitable(v) == R!PaxosCommitable(v)

Consistency == 
  /\ \A v1, v2 \in R!ProposedValues:
      ProtocolCommitable(v1) /\ ProtocolCommitable(v2)
      => \A i \in v1, j \in v2: (i.cmd = j.cmd => i.ts = j.ts)
  /\ R!Consistency

=============================================================================
\* Modification History
\* Last modified Tue Oct 19 12:43:15 BST 2021 by cjen1
\* Created Mon Oct 18 14:33:21 BST 2021 by cjen1

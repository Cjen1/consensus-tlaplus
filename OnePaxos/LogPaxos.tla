---- MODULE LogPaxos ----

EXTENDS Utils, Sequences, Integers

CONSTANTS Acceptors, P1Quorums, P2Quorums, Commands, BallotNumbers

VARIABLES msgs,
          acc

InitialValue == <<>>

LEQ(a,b) ==
  /\ Len(a) =< Len(b)
  /\ \A i \in DOMAIN a : a[i] = b[i]

UpdatePrev(prev, c) == prev \o <<c>>

CommandsRepresented(v) == Range(v)

Values == AllSeqFromSet(Commands)

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


Consistency == 
  /\ \A v1, v2 \in Values:
      R!PaxosCommitable(v1) /\ R!PaxosCommitable(v2)
      => \A i \in (DOMAIN v1) \cap (DOMAIN v2): v1[i] = v2[i]
  /\ R!Consistency
====

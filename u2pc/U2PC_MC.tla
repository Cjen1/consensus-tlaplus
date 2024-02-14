---- MODULE U2PC_MC ----

EXTENDS Apalache, U2PC

\* @type: (a, b) => <<a, b>>;
Pair(A,B) == << A,B >>

T1 == SetAsFun({Pair("T1", {"X"})})
S1 == SetAsFun({Pair("X", {"X1", "X2"})})

CInit ==
  /\ Txns := T1
  /\ Shards := S1

Invs == TRUE
  \*/\ ~\E t \in TIDs: Coordinator_state[t] = "Lock"

====

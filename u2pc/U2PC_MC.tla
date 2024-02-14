---- MODULE U2PC_MC ----

EXTENDS Apalache, U2PC, TLC

\* @type: (a, b) => <<a, b>>;
Pair(A,B) == << A,B >>

T1 == SetAsFun({Pair("T1", {"X"})})
T1_2 == SetAsFun({Pair("T1", {"X"}), Pair("T2", {"X"})})
S1 == SetAsFun({Pair("X", {"X1", "X2"})})

T3 == SetAsFun({Pair("T1", {"X", "Y"}), Pair("T2", {"Y","Z"}), Pair("T3", {"Z", "X"})})
S3 == SetAsFun({Pair("X", {"X1", "X2"}), Pair("Y", {"Y1", "Y2"}), Pair("Z", {"Z1", "Z2"})})


CInit ==
  /\ Txns := T3
  /\ Shards := S3

Safety_non_recovery == Serialisability(CommittedTIDs)

Safety_recovery ==
  \E S \in SUBSET RIDs:
  \* Valid recovery
  /\ \A k \in DOMAIN Shards: \E r \in S: r \in Shards[k] 
  /\ LET recovery_committed == 
         {t \in TIDs: 
           \A r \in S:
           KeyLookup[r] \in Txns[t] => /\ Replicas[r].locked 
                                       /\ Replicas[r].logged = t}
     IN IF Serialisability(CommittedTIDs \cup recovery_committed)
        THEN TRUE
        ELSE Print([rec |-> recovery_committed, com |-> CommittedTIDs], FALSE)
       

Invs ==
  /\ Safety_recovery
  \*/\ ~\E t \in TIDs: Coordinator_state[t] = "Lock"
  \*/\ ~\E t \in TIDs: Coordinator_state[t] = "Commit"
  \*/\ ~\E r \in RIDs: Replicas[r].version = "T2"
  /\ TRUE

====

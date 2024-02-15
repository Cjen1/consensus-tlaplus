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

TransitiveClosure(R) ==
  LET S == {r[1] : r \in R} \cup {r[2] : r \in R}
      RECURSIVE TCR(_)
      TCR(T) == IF T = {} 
                  THEN R
                  ELSE LET r == CHOOSE s \in T : TRUE
                           RR == TCR(T \ {r})
                       IN  RR \cup {<<s, t>> \in S \X S : 
                                      <<s, r>> \in RR /\ <<r, t>> \in RR}
  IN  TCR(S)

TransactionOrdering == LET
  F(acc, tid) == acc \union (Range(Coordinator_txn_state[tid]) \X {tid})
  Base == ApaFoldSet(F, {}, TIDs)
  IN TransitiveClosure(Base)

RecoveryCommitted(S) == 
  {t \in TIDs: 
    \A r \in S:
    KeyLookup[r] \in Txns[t] 
    => \/ Replicas[r].locked /\ Replicas[r].logged = t
       \/ Replicas[r].version = t
       \/ <<t, Replicas[r].version>> \in TransactionOrdering
  }

Safety_recovery ==
  \A S \in SUBSET RIDs:
  \* Valid recovery
  \A k \in DOMAIN Shards: \E r \in S: r \in Shards[k] 
  =>
  IF Serialisability(CommittedTIDs \cup RecoveryCommitted(S))
  THEN TRUE
  ELSE Print([rec |-> RecoveryCommitted(S), com |-> CommittedTIDs], FALSE)

RecoveryAborted(S) ==
  {t \in TIDs:
    \E r \in S:
    /\ KeyLookup[r] \in Txns[t]
    /\ \/ ~Replicas[r].locked
       \/ Replicas[r].locked /\ Replicas[r].logged /= t}

Durability ==
  \A S \in SUBSET RIDs:
  \* Valid recovery
  (\A k \in DOMAIN Shards: \E r \in S: r \in Shards[k])
  =>
  \A t \in TIDs:
  /\ t \in CommittedTIDs => t \in RecoveryCommitted(S)
  /\ t \in AbortedTIDs => t \in RecoveryAborted(S)

Invs ==
  \*/\ Safety_recovery
  /\ Durability
  \*/\ ~\E t \in TIDs: Coordinator_state[t] = "Lock"
  \*/\ ~\E t \in TIDs: Coordinator_state[t] = "Commit"
  \*/\ ~\E r \in RIDs: Replicas[r].version = "T2"
  /\ TRUE

====

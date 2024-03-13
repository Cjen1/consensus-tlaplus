---- MODULE U2PC_MC ----

EXTENDS Apalache, U2PC, TLC

\* @type: (a, b) => <<a, b>>;
Pair(A,B) == << A,B >>

\********************
\* 1 shard, 1-2 transactions
\* Checking simple commit, and conflict behaviours
\********************
T1 == SetAsFun({Pair("T1", {"X"})})
T1_2 == SetAsFun({Pair("T1", {"X"}), Pair("T2", {"X"})})
S1 == SetAsFun({Pair("X", {"X1", "X2"})})

\********************
\* 3 shards, 3 transactions, 
\* Checking indirect dependency loops
\********************
T3 == SetAsFun({
  Pair("T1", {"X", "Y"}),
  Pair("T2", {"Y","Z"}), 
  Pair("T3", {"Z", "X"})})
S3 == SetAsFun({
  Pair("X", {"X1", "X2"}), 
  Pair("Y", {"Y1", "Y2"}), 
  Pair("Z", {"Z1", "Z2"})})

\********************
\* Initial state for Apalache testing
\********************
CInit ==
  /\ Txns := T3
  /\ Shards := S3

\********************
\* Credit to github.com/tlaplus/examples 
\********************
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

\********************
\* Every transaction committed during recovery preserves linearisability
\********************
Safety_recovery ==
  \A S \in SUBSET RIDs:
  \* Valid recovery
  (\A k \in DOMAIN Shards: \E r \in S: r \in Shards[k])
  => Linearisability(CommittedTIDs \cup RecoveryCommitted(S))

RecoveryAborted(S) ==
  {t \in TIDs:
    \E r \in S:
    /\ KeyLookup[r] \in Txns[t]
    /\ \/ ~Replicas[r].locked
       \/ Replicas[r].locked /\ Replicas[r].logged /= t}

\********************
\* Every committed or aborted transaction results in the same recovery decision
\********************
Durability ==
  \A S \in SUBSET RIDs:
  \* Valid recovery
  (\A k \in DOMAIN Shards: \E r \in S: r \in Shards[k])
  =>
  \A t \in TIDs:
  /\ t \in CommittedTIDs => t \in RecoveryCommitted(S)
  /\ t \in AbortedTIDs => t \in RecoveryAborted(S)

\********************
\* Since recovery stops every replica it uses, an explicit recovery check is unnecessary
\* since that is equivalent to just checking that every possible recovery using the current
\* state preserves the invariants.
\********************
Invs ==
  /\ Safety_recovery
  /\ Durability

====

---- MODULE U2PC ----
EXTENDS FiniteSets, Integers, Apalache, TLC

\* @typeAlias: key = Str;
\* @typeAlias: rid = Str;
\* @typeAlias: tid = Str;
\* @typeAlias: version = $tid;
\* @typeAlias: txn = Set($key);
\* @typeAlias: txnstate = $key -> $version;
U2PC_ALIAS == TRUE

CONSTANTS
  \* @type: $key -> Set($rid);
  Shards,
  \* @type: $tid -> $txn;
  Txns

ASSUME \A k1, k2 \in DOMAIN Shards: k1 /= k2 => Shards[k1] \cap Shards[k2] = {}
ASSUME "Init" \notin DOMAIN Txns

\* msg_read = Str;
\* msg_read_resp = {key: $key, ver : $version};
\* msg_lock = {txn: $txn, key: $key, ver: $version};
\* msg_lock_resp = Bool;
\* msg_unlock = Bool;
\* msg_unlock_resp = Bool;

VARIABLES
  \* @type: $rid -> {locked : Bool, version: $version, logged: $version};
  Replicas,
  \* @type: $tid -> Str;
  Coordinator_state,
  \* @type: $tid -> $txnstate;
  Coordinator_txn_state,
  \* @type: Set({src : $tid, key : $key});
  M_read,
  \* @type: Set({src : $rid, dst: $tid, ver: $version});
  M_read_resp,
  \* @type: Set({tid : $tid, txn: $txn, state: $txnstate});
  M_lock,
  \* @type: Set({src : $rid, dst : $tid, locked : Bool});
  M_lock_resp,
  \* @type: Set({src : $tid, apply : Bool});
  M_unlock,
  \* @type: Set({src : $rid, tid : $tid});
  M_unlock_resp

Msgs == <<M_read, M_read_resp, M_lock, M_lock_resp, M_unlock, M_unlock_resp>>

\* @type: (a -> b) => Set(b);
Range(F) == {F[x] : x \in DOMAIN F}

\* @type: Set($rid);
RIDs == UNION Range(Shards)
TIDs == DOMAIN Txns

KeyLookup == [r \in RIDs |-> CHOOSE k \in DOMAIN Shards: r \in Shards[k]]

Init ==
  /\ Replicas = [r \in RIDs |-> [locked |-> FALSE, version |-> "Init", logged |-> "NULL"]]
  /\ Coordinator_state = [t \in TIDs |-> "Start"]
  /\ Coordinator_txn_state = [t \in TIDs |-> SetAsFun({})]
  /\ M_read = {} /\ M_read_resp = {}
  /\ M_lock = {} /\ M_lock_resp = {}
  /\ M_unlock = {} /\ M_unlock_resp = {}

RelevantReplicas(t) == UNION {Shards[k]: k \in Txns[t]}

CoordinatorStart(t) ==
  /\ Coordinator_state[t] = "Start"
  /\ M_read' = M_read \cup {[src |-> t, key |-> k] : k \in Txns[t]}
  /\ UNCHANGED << M_read_resp, M_lock, M_lock_resp, M_unlock, M_unlock_resp >>
  /\ Coordinator_state' = [Coordinator_state EXCEPT ![t] = "Read"]
  /\ UNCHANGED <<Coordinator_txn_state, Replicas>>

ReplicaRead(r) ==
  /\ Replicas[r].locked = FALSE
  /\ \E m \in M_read:
     /\ ~\E m1 \in M_read_resp: m1.src = r /\ m1.dst = m.src
     /\ M_read_resp' = M_read_resp \cup {[src |-> r, dst |-> m.src, ver |-> Replicas[r].version]}
     /\ UNCHANGED << M_read, M_lock, M_lock_resp, M_unlock, M_unlock_resp>>
  /\ UNCHANGED << Replicas, Coordinator_state, Coordinator_txn_state >>

CoordinatorRead(t) ==
  /\ Coordinator_state[t] = "Read"
  /\ \A k \in Txns[t]: \E m \in M_read_resp: KeyLookup[m.src] = k
  /\ \E F \in [Txns[t] -> RIDs]:
     /\ \A k \in Txns[t]: /\ k = KeyLookup[F[k]] 
                          /\ \E m \in M_read_resp: m.dst = t /\ m.src = F[k]
     /\ Coordinator_txn_state' = [Coordinator_txn_state EXCEPT ![t] = [
         k \in Txns[t] |-> (CHOOSE m \in M_read_resp : m.dst = t /\ m.src = F[k]).ver
         ]]
  /\ Coordinator_state' = [Coordinator_state EXCEPT ![t] = "Lock"]
  /\ UNCHANGED << Replicas, Msgs >>

CoordinatorLock(t) ==
  /\ Coordinator_state[t] = "Lock"
  /\ M_lock' = M_lock \cup {[tid |-> t, txn |-> Txns[t], state |-> Coordinator_txn_state[t]]}
  /\ UNCHANGED << M_read, M_read_resp, M_lock_resp, M_unlock, M_unlock_resp >>
  /\ Coordinator_state' = [Coordinator_state EXCEPT ![t] = "Decide"]
  /\ UNCHANGED <<Coordinator_txn_state, Replicas>>

ReplicaLock(r) ==
  /\ \E m \in M_lock:
     /\ KeyLookup[r] \in m.txn
     /\ ~\E m1 \in M_lock_resp: m1.src = r /\ m1.dst = m.tid
     /\ IF (~Replicas[r].locked) /\ Replicas[r].version = m.state[KeyLookup[r]]
        THEN 
          /\ Replicas' = [Replicas EXCEPT ![r] = [
              locked |-> TRUE, version |-> Replicas[r].version, logged |-> m.tid]]
          /\ M_lock_resp' = M_lock_resp \cup {[src |-> r, dst |-> m.tid, locked |-> TRUE]}
        ELSE
          /\ M_lock_resp' = M_lock_resp \cup {[src |-> r, dst |-> m.tid, locked |-> FALSE]}
          /\ UNCHANGED Replicas
  /\ UNCHANGED << M_read, M_read_resp, M_lock, M_unlock, M_unlock_resp >>
  /\ UNCHANGED << Coordinator_state, Coordinator_txn_state >>

CoordinatorCommit(t) ==
  /\ Coordinator_state[t] = "Decide"
  /\ \A k \in Txns[t]: \A r \in Shards[k]: \E m \in M_lock_resp:
       /\ m.src = r /\ m.dst = t
       /\ m.locked
  /\ Coordinator_state' = [Coordinator_state EXCEPT ![t] = "Commit"]
  /\ M_unlock' = M_unlock \cup {[src |-> t, apply |-> TRUE]}
  /\ UNCHANGED << M_read, M_read_resp, M_lock, M_lock_resp, M_unlock_resp >>
  /\ UNCHANGED << Replicas, Coordinator_txn_state >>

CoordinatorStartAbort(t) ==
  /\ Coordinator_state[t] = "Decide"
  /\ \E k \in Txns[t]: \E r \in Shards[k]: \E m \in M_lock_resp:
       /\ m.src = r /\ m.dst = t
       /\ ~m.locked
  /\ Coordinator_state' = [Coordinator_state EXCEPT ![t] = "TryAbort"]
  /\ M_unlock' = M_unlock \cup {[src |-> t, apply |-> FALSE]}
  /\ UNCHANGED << M_read, M_read_resp, M_lock, M_lock_resp, M_unlock_resp >>
  /\ UNCHANGED << Replicas, Coordinator_txn_state >>

ReplicaUnlock(r) ==
  \E m \in M_unlock:
  /\ Replicas[r].locked
  /\ m.src = Replicas[r].logged
  /\ IF m.apply
     THEN Replicas' =  [Replicas EXCEPT ![r] = [
           locked |-> FALSE, version |-> Replicas[r].logged, logged |-> "NULL"]]
     ELSE Replicas' =  [Replicas EXCEPT ![r] = [
           locked |-> FALSE, version |-> Replicas[r].version, logged |-> "NULL"]]
  /\ M_unlock_resp' = M_unlock_resp \cup {[src |-> r, tid |-> Replicas[r].logged]}
  /\ UNCHANGED << M_read, M_read_resp, M_lock, M_lock_resp, M_unlock>>
  /\ UNCHANGED << Coordinator_state, Coordinator_txn_state >>

CoordinatorAbort(t) ==
  /\ Coordinator_state[t] = "TryAbort"
  /\ \E k \in Txns[t]: \A r \in Shards[k]: 
     \/ \E m \in M_unlock_resp: m.src = r /\ m.tid = t
     \/ \E m \in M_lock_resp: m.src = r /\ m.dst = t /\ ~m.locked
  /\ Coordinator_state' = [Coordinator_state EXCEPT ![t] = "Abort"]
  /\ UNCHANGED << Replicas, Msgs, Coordinator_txn_state >>


Next ==
  \/ \E r \in RIDs: \/ ReplicaRead(r)
                    \/ ReplicaLock(r)
                    \/ ReplicaUnlock(r)
  \/ \E t \in TIDs: \/ CoordinatorStart(t)
                    \/ CoordinatorRead(t)
                    \/ CoordinatorLock(t)
                    \/ CoordinatorCommit(t)
                    \/ CoordinatorStartAbort(t)
                    \/ CoordinatorAbort(t)

Spec == Init /\ [][Next]_<< Replicas, Coordinator_state, Coordinator_txn_state, Msgs >>

Serialisability(C) == 
  \/ Cardinality(C) < 2
  \/ \E R \in SUBSET (C \X C):
     \* Irreflexive
     /\ \A t1 \in C: <<t1, t1>> \notin R
     \* Transitive
     /\ \A t1, t2, t3 \in C: (<<t1,t2>> \in R /\ <<t2, t3>> \in R) => <<t1, t3>> \in R
     \* Above 2 ensure there are no cycles
     \* R respects observed order
     /\ \A t1, t2 \in C:
        (\E k \in Txns[t2] : Coordinator_txn_state[t2][k] = t1) => <<t1, t2>> \in R
     \* If two transactions interfere, there is an order
     /\ \A t1, t2 \in C:
        (t1 /= t2 /\ Txns[t1] \cap Txns[t2] /= {}) => <<t1, t2>> \in R \/ <<t2, t1>> \in R

CommittedTIDs == {t \in TIDs: Coordinator_state[t] = "Commit"}

====

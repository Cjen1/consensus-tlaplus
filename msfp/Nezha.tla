---- MODULE Nezha ----

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
  RIDs,
  BaseValues

VARIABLE quorums

InitQuorum == 
  quorums \in 
    {Q \in SUBSET SUBSET RIDs:
      /\ Cardinality(Q) > 0
      /\ \A q \in Q: Cardinality(q) > Cardinality(RIDs) \div 2
      /\ \A q1, q2 \in Q: q1 \cap q2 /= {}
    }

VARIABLE coordinator_id

InitCoordinatorID == coordinator_id \in RIDs

VARIABLES
  replica_states,
  proposals,
  state_updates

a \sqsubseteq b ==
  /\ a.primed <= b.primed
  /\ Len(a.v) <= Len(b.v)
  \* primed sections match
  /\ \A i \in DOMAIN a.v:
     i <= a.primed => a[i] = b[i]
  \* unprimed sections match
  /\ \A i \in DOMAIN b.v:
     i > b.primed => \/ i <= Len(a.v)
                     \/ a[i] = b[i]

Propose(rid, s) ==
/\ replica_states[rid] \sqsubseteq s
/\ replica_states[rid] /= s
/\ replica_states' = [replica_states EXCEPT ![rid] = s]
/\ state_updates' = state_updates \cup {<<rid, s>>}

CoordinatorPropose(rid, v) ==
LET new_state == [v |-> replica_states[rid].v \o << v >>, primed |-> replica_states[rid].primed + 1] IN
/\ rid = coordinator_id
/\ Propose(rid, new_state)

ReplicaPropose(rid, v) ==
LET new_state == [v |-> replica_states[rid].v \o << v >>, primed |-> replica_states[rid].primed] IN
/\ rid /= coordinator_id
/\ Propose(rid, new_state)

Merge(rid) ==
\E <<r,u>> \in state_updates:
LET merged_log == 
  [ i \in DOMAIN u.v \cup DOMAIN replica_states[rid].v |->
    IF i <= u.primed
    THEN u[i]
    ELSE replica_states[rid].v]
IN
\* Required to more precisely follow Nezha
/\ r = coordinator_id
/\ replica_states[rid].primed < u.primed
/\ Propose(rid, [primed |-> u.primed, v |-> merged_log])

Committable(v) ==
LET votes == {<<r, s>> \in state_updates: v \sqsubseteq s}
    voting_rids == {r : <<r,s>> \in votes}
IN \E q \in quorums: q \subseteq voting_rids


====

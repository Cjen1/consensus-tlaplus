---- MODULE SimpleValue ----

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
  RIDs,
  BaseValues

VARIABLE
  quorums

InitQuorum == 
  quorums \in 
    {Q \in SUBSET SUBSET RIDs:
      /\ Cardinality(Q) > 0
      /\ \A q \in Q: Cardinality(q) > Cardinality(RIDs) \div 2
      /\ \A q1, q2 \in Q: q1 \cap q2 /= {}
    }

VARIABLES
  replica_states,
  proposals,
  state_updates

Null == CHOOSE v : v \notin BaseValues
a \sqsubseteq b == a = Null \/ a = b

Values == BaseValues \cup {Null}

InitReplica == 
  replica_states = [r \in RIDs |-> Null]

Propose(v) ==
  /\ v \notin proposals
  /\ proposals' = proposals \cup {v}

ReplicaVote(rid) ==
\E p \in proposals:
  /\ replica_states[rid] \sqsubseteq p /\ replica_states[rid] /= p
  /\ replica_states' = [replica_states EXCEPT ![rid] = p]
  /\ state_updates' = state_updates \cup {<< rid, p >>}

Next == 
/\ UNCHANGED << quorums >>
/\ \/ \E v \in BaseValues: Propose(v) /\ UNCHANGED <<replica_states, state_updates>>
   \/ \E r \in RIDs: ReplicaVote(r) /\ UNCHANGED <<proposals>>

Init == 
  /\ InitQuorum
  /\ InitReplica
  /\ proposals = {}
  /\ state_updates = {}

Spec == Init /\ [][Next]_<<quorums, replica_states, proposals, state_updates>>

Committable(v) ==
LET votes == {<<r, s>> \in state_updates: v \sqsubseteq s}
    voting_rids == {r : <<r,s>> \in votes}
IN \E q \in quorums: q \subseteq voting_rids

InvCommit ==
  Cardinality({v \in BaseValues : Committable(v)}) <= 1

====

------------------------------ MODULE OnePaxos ------------------------------

(*

Paxos gives that the subsequent phase 1s will choose a value which extends it.

Persistance, a = persist(v) /\ b = persist(v') => a ~> b => v <= v'
Regular paxos ~> via proposer ordering and quorum intersection on phases
Fast Paxos    ~> via p2 intersection   and quorum intersection on phases

Execution, some safety constraint, 
commit(v) /\ commit(v') => v <= v' => 
(Tempo)         \A va \in v, vb \in v': va[cmd] = vb[cmd] => va[ts] = vb[ts]
(Lists)         \A i \in Nat: v[i] = v'[i]

Paxos side
Phase 1. Choose a value which extends all ones which could have been committed previously
Phase 2. Emit persist(v) when a larger one is accepted by a quorum of other acceptors
         Only propose values which permit phase 1 constraint
         P2 \cup P1 <> {}

Fast Paxos side
Phase 2. Multiple proposers which still must ensure the Phase 1 constraint (ie write leases)
         Fast P2 quorums must intersect
         
         If a value is persisted it can be committed.

         If we allow committing 'the maximum value where a quorum has larger values'
           Then we allow loops/bubbles in the leq graph.
           
           It would be really great to deal with this at the paxos side, 
             rather than application side

Tempo:
  Client:
    On recv(cmd):
      - update V to be V \cup {< cmd, max{v \in V: v.ts}>} 
      - send([2a, b, V])
  
  Acceptor:
    On recv([2a, b, V]):
      - Standard paxos, if greater update stored ballot and ack
      - Otherwise nack with current value
  
  Client: 
    On recv([2b, b, v, success]):
      - If success (and quorum of other resps)
        - then commit v
        - Otherwise if timeout then add

Proof of safety Tempo:

*)
\* A concrete example of OnePaxos using Tempo style committment
\* ie Once a value is committed with some timestamp it is never increased

EXTENDS Integers, FiniteSets, Utils

CONSTANTS Acceptors, P1Quorums, P2Quorums, Commands, BallotNumbers

CONSTANTS Values, InitialValue, LEQ(_,_), UpdatePrev(_,_), CommandsRepresented(_)

VARIABLES msgs,
          acc

ASSUME \A p1 \in P1Quorums, p2 \in P2Quorums: (p1 \cup p2) /= {}

----

BallotLEQ(a,b) ==
  \/ a.bal < b.bal
  \/ a.bal = b.bal /\ LEQ(a.val, b.val)

Send(m) == msgs' = msgs \cup {m}

---- 
\* -------- Proposer behaviours --------

Phase1a(b) ==
  /\ ~\E m \in msgs: m.type = "1a" /\ m.balNum = b
  /\ Send([type |-> "1a", balNum |-> b])
  /\ UNCHANGED << acc >>

Phase2a(b) ==
  LET p2a_msgs == {m \in msgs: m.type = "2a" /\ m.bal.bal = b}
      all_p1b_msgs == {m \in msgs: m.type = "1b" /\ m.balNum = b}
      quorum(S) == \E Q \in P1Quorums: \A a \in Q: \E m \in S: m.acc = a
      p1b_msgs == {S \in SUBSET all_p1b_msgs: quorum(S)}
      prevValue == IF p2a_msgs = {}
                   THEN {max(BallotLEQ,{m.maxBal: m \in M}).val: M \in p1b_msgs}
                   ELSE {max(LEQ, {m.bal.val : m \in p2a_msgs})}
  IN \E prev \in prevValue: 
     /\ \/ \E c \in Commands \ CommandsRepresented(prev):
             Send([type |-> "2a", bal |-> [bal |-> b, val |-> UpdatePrev(prev, c)]])
        \/ Send([type |-> "2a", bal |-> [bal |-> b, val |-> prev]])
     /\ UNCHANGED << acc >>

----
\* -------- Commitable Values--------

PaxosCommitable(v) ==
  \E b \in BallotNumbers, Q \in P2Quorums:
  \A a \in Q: \E m \in msgs: 
     /\ m.type = "2b" 
     /\ m.acc = a
     /\ m.bal.bal = b
     /\ LEQ(v, m.bal.val)

----
\* -------- Acceptor Behaviours --------

Phase1b(a) ==
  \E m \in msgs:
    /\ m.type = "1a"
    /\ m.balNum > acc[a].maxBalNum
    /\ acc' = [acc EXCEPT ![a] = [acc[a] EXCEPT !.maxBalNum = m.balNum]]
    /\ Send([type |-> "1b", balNum |-> m.balNum, acc |-> a, maxBal |-> acc[a].maxBal])

Phase2b(a) == 
  \E m \in msgs:
    /\ m.type = "2a"
    /\ m.bal.bal >= acc[a].maxBalNum
    /\ \/ /\ BallotLEQ(acc[a].maxBal, m.bal)
          /\ acc' = [acc EXCEPT ![a] = [acc[a] EXCEPT !.maxBalNum = m.bal.bal, !.maxBal = m.bal]]
	  /\ Send([type |-> "2b", bal |-> m.bal, acc |-> a])
\*       \/ /\ ~ BallotLEQ(acc[a].maxBal, m.bal)
\*          /\ acc' = [acc EXCEPT ![a] = [acc[a] EXCEPT !.maxBalNum = m.bal.bal]]
\*	  /\ Send([type |-> "2b", bal |-> acc[a].maxBal, acc |-> a])

----
\* -------- Spec --------
Init == 
  /\ msgs = {} 
  /\ acc = [a \in Acceptors |-> [maxBalNum |-> -1, maxBal |-> [bal |-> -1, val |-> InitialValue]]]

Next ==
  \/ \E p \in BallotNumbers : Phase1a(p) \/ Phase2a(p)
  \/ \E a \in Acceptors     : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_<< msgs, acc >>

----
\* -------- Type Check --------

PossibleBallots == [bal : BallotNumbers \cup {-1}, val : Values]

Messages ==      [type : {"1a"}, balNum : BallotNumbers]
            \cup [type : {"1b"}, acc : Acceptors, balNum : BallotNumbers, maxBal : PossibleBallots]
            \cup [type : {"2a"}, bal : PossibleBallots]
            \cup [type : {"2b"}, acc : Acceptors, bal : PossibleBallots]

AcceptorState == [maxBalNum : BallotNumbers \cup {-1}, maxBal : PossibleBallots]

TypeInvariant == 
  /\ msgs \in SUBSET Messages
  /\ acc \in [Acceptors -> AcceptorState]

----
\* -------- Invariants --------

Consistency == 
  \A v1 , v2 \in Values: PaxosCommitable(v1) /\ PaxosCommitable(v2) => LEQ(v1, v2) \/ LEQ(v2, v1)

=============================================================================
\* Modification History
\* Last modified Mon Oct 18 16:36:18 BST 2021 by cjen1
\* Last modified Mon Oct 18 16:27:35 BST 2021 by cjen1
\* Last modified Thu Oct 14 12:13:07 BST 2021 by cjjen
\* Created Thu Oct 14 12:04:01 BST 2021 by cjjen

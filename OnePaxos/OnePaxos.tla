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

EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS Acceptors, P1Quorums, P2Quorums, Command

VARIABLES msgs,
          acc,
          proposed_commands

ASSUME \A p1 \in P1Quorums, p2 \in P2Quorums: p1 \cup p2 \neq {}

\* Assume single designated proposer per ballot number
BallotNumbers == Nat

\*Value == SUBSET [cmd : Command, ts : Nat]
\*
\*LEQ(a,b) ==
\*  /\ \A va \in a: \E vb \in b: 
\*       /\ va.val = vb.val 
\*       /\ va.ts <= vb.ts
\*  /\ \A vextra \in b \ a, va \in a:
\*       vextra.ts > va.ts

Value == AllSeqFromSet(Command)

LEQ(a,b) ==
  /\ Len(a) =< Len(b)
  /\ \A i \in DOMAIN a : a[i] = b[i]

BallotLEQ(a,b) = 
  \/ a.bal < b.bal
  \/ a.bal = b.bal /\ LEQ(a.val, b.val)

----


----

Send(m) == msg' = msgs \cup {m}

Phase1a(b) ==
  /\ ~\E m \in msgs: m.type = "1a" /\ m.balNum = b
  /\ Send([type |-> "1a", balNum |-> b])
  /\ UNCHANGED << acc >>

Phase1b(a) ==
  \E m \in msgs:
    /\ m.type = "1a"
    /\ m.balNum > acc[a].maxBalNum
    /\ acc' = [acc EXCEPT ![a] = [acc[a] EXCEPT !.maxBalNum = m.balNum]]
    /\ Send([type |-> "1b", balNum |-> m.balNum, acc |-> a, maxBal |-> acc[a].maxBal])

Phase2a(b) ==
  LET p2a_msgs == {m \in msgs: m.type = "2a" /\ m.balNum = b}
      all_p1b_msgs == SUBSET {m \in msgs: m.type = "1b" /\ m.balNum = b}
      quorum(S) == \E Q \in P1Quorums: \A a \in Q: \E m \in S: m.acc = a
      p1b_msgs == {S \in all_p1b_msgs: quourm(S)}
      prevValue == IF p2a_msgs = {} 
                    THEN {max(BallotLEQ,{m.bal: m \in M}).val: M \in p1b_msgs}
                    ELSE {max(LEQ, {m.val : m \in p2a_msgs})}
  IN \E prev \in prevValue: 
     \E c \in Command \ proposed_commands:
     /\ Send([type |-> "2a", bal |-> [bal |-> b, val |-> UpdatePrev(prev, c)]])
     /\ proposed_commands' = proposed_commands \cup c

Phase2b(a) ==
  
=============================================================================
\* Modification History
\* Last modified Thu Oct 14 12:13:07 BST 2021 by cjjen
\* Created Thu Oct 14 12:04:01 BST 2021 by cjjen

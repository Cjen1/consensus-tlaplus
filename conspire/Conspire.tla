----------------------------- MODULE Conspire -----------------------------
\* This protocol is a collaborative variation of FastPaxos
\* It ammends the last line of Figure 2 in Lamport's Fast Paxos paper
\*   to such that it chooses the union of all proposed values in the previous round
\* Supposing multiple proposers collide on the first round.
\* Then you have at most one value per acceptor.
\* Thus on round 2, O4 is false and we can choose any proposed value
\* By choosing the union of read values in phase 1 we collaborate between proposers
\* Thus supposing each round the set of proposed values collides, then after 
\*   |Acceptors| rounds the proposed value must include all initially proposed values
\* Recovery is simply a node listing for the acks from the previous round

\* Additionally this can be viewed as a piggybacked fast paxos variant

EXTENDS Integers, FiniteSets, TLC

CONSTANTS Acceptors, PropValues

VARIABLES acc, prop, msg

BallotNumbers == Nat

vars == << acc, prop, msg >>

Proposers == PropValues

None == CHOOSE v: v \notin SUBSET PropValues

\* This is the simple majority quorums approach
\* Fast flexible paxos should be feasible
Quorums == {Q \in SUBSET Acceptors: Cardinality(Q) = (2 * Cardinality(Acceptors)) \div 3 + 1}

TBallot == [val : SUBSET PropValues \union {None}, num : BallotNumbers]

TInitBallot == [val : {None}, num : {-1}]

TMsg == [kind : {"req"}, src : Proposers, bal : TBallot] \union
        [kind : {"ack"}, src : Acceptors, bal : TBallot]

TypeOk ==
  /\ msg  \in SUBSET TMsg
  /\ acc  \in [Acceptors -> TBallot \union TInitBallot]
  /\ prop \in [Proposers -> TBallot \union TInitBallot]

Send(m) == msg' = msg \cup {m}

Init == 
  /\ msg  = {}
  /\ acc  = [a \in Acceptors |-> [val |-> None, num |-> -1]]
  /\ prop = [v \in Proposers |-> [val |-> None, num |-> -1]]

ChooseValue(M) ==
  LET V == {m.bal.val: m \in M}
      O4(v) == 
        \E Q \in Quorums:
        \A m \in {m \in M: m.src \in Q}: \* Q intersection M.src
          m.bal.val = v 
  IN IF \E v \in V: O4(v)
     THEN CHOOSE v \in V: O4(v)
     ELSE UNION V

Propose(p) ==
  IF prop[p].num = -1
  THEN \* Round 0 
    LET bal == [num |-> 0, val |-> {p}]
    IN /\ prop' = [prop EXCEPT ![p] = bal]
       /\ Send([kind |-> "req", src |-> p, bal |-> bal])
       /\ UNCHANGED << acc >>
  ELSE \* Otherwise
    \E M \in SUBSET {m \in msg: m.kind = "ack" /\ m.bal.num = prop[p].num}: 
      /\ \E Q \in Quorums: Q \subseteq {m.src: m \in M}
      /\ LET v == ChooseValue(M)
             bal == [num |-> prop[p].num + 1, val |-> v]
         IN /\ prop' = [prop EXCEPT ![p] = bal]
            /\ Send([kind |-> "req", src |-> p, bal |-> bal])
            /\ UNCHANGED << acc >>


Reply(a) == \E m \in {m \in msg: m.kind = "req"}:
  /\ IF /\ m.bal.num > acc[a].num
     THEN 
       /\ Send([kind |-> "ack", src |-> a, bal |-> m.bal])
       /\ acc' = [acc EXCEPT ![a] = m.bal]
     ELSE
       /\ Send([kind |-> "ack", src |-> a, bal |-> acc[a]])
       /\ UNCHANGED << acc >>
  /\ UNCHANGED << prop >>

Next ==
  \/ \E v \in Proposers: Propose(v)
  \/ \E a \in Acceptors: Reply(a)

Spec == /\ Init 
        /\ [][Next]_vars 

Symmetry == Permutations(PropValues) \union Permutations(Acceptors)

\* A ballot can be committed if there exists a quorum of responses for it
Committable(v) ==
  \E balnum \in {m.bal.num: m \in msg}, Q \in Quorums:
  \A a \in Q: \E m \in msg: 
    /\ m.kind = "ack"
    /\ m.src = a
    /\ m.bal = [val |-> v, num |-> balnum]

ConsInv == \A v1, v2 \in SUBSET PropValues: (Committable(v1) /\ Committable(v2)) => v1 = v2
NoNoneRep == \A m \in msg: m.kind = "req" => m.bal.val /= None

BalLimit == 5
BalNumConstraint == \A p \in Proposers: prop[p].num <= BalLimit
=============================================================================

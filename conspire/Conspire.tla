----------------------------- MODULE Conspire -----------------------------
\* This protocol is a collaborative variation of FastPaxos
\* It ammends the last line of Figure 2 in Lamport's Fast Paxos paper
\*   to such that it chooses the union of all proposed values in the previous round
\* Supposing multiple proposers collide on the first round.
\* Then you have at most one value per acceptor.
\* Thus on round 2, O4 is false and we can choose any proposed value
\* By choosing the union of rec values in phase 1 we collaborate between proposers
\* Thus supposing each round the set of proposed values collides, then after 
\*   |Acceptors| rounds the proposed value must include all initially proposed values
\* Recovery is simply a node listing for the acks from the previous round

\* Additionally this can be viewed as a piggybacked fast paxos variant

EXTENDS Integers, FiniteSets, Apalache

CONSTANTS 
  \* @type: Set(ACC);
  Acceptors, 
  \* @type: Set(VALUE);
  PropValues

VARIABLES 
  \* @type: ACC -> BALLOT;
  acc_maxVBal,
  \* @type: ACC -> BALLOTNUMBER;
  acc_maxBal,
  \* @type: PRO -> COMMITABLE_VALUE;
  prop_val,
  \* @type: PRO -> BALLOTNUMBER;
  prop_balnum,
  \* @type: [req: Set(MREQ), rec: Set(MREC), ack: Set(MACK)];
  msg

\*@typeAlias: PRO = VALUE;
\*@typeAlias: COMMITABLE_VALUE = Set(VALUE);
\*@typeAlias: BALLOTNUMBER = Int;
\*@typeAlias: BALLOT = [num : BALLOTNUMBER, val : COMMITABLE_VALUE];
\*@typeAlias: MREQ   = [src : PRO, bal : BALLOT];
\*@typeAlias: MREC   = [src : PRO, balnum : BALLOTNUMBER];
\*@typeAlias: MACK   = [src : ACC, bal : BALLOT, balnum : BALLOTNUMBER]; 

vars == << acc_maxVBal, acc_maxBal, prop_val, prop_balnum, msg >>

Proposers == PropValues

\* This is the simple majority quorums approach
\* Fast flexible paxos should be feasible
Quorums == {Q \in SUBSET Acceptors: Cardinality(Q) = (2 * Cardinality(Acceptors)) \div 3 + 1}

SendReq(m) == msg' = [msg EXCEPT !.req = msg.req \union {m}]
SendRec(m) == msg' = [msg EXCEPT !.rec = msg.rec \union {m}]
SendAck(m) == msg' = [msg EXCEPT !.ack = msg.ack \union {m}]

Init == 
  /\ acc_maxVBal   := [a \in Acceptors |-> [val |-> {}, num |-> 0]]
  /\ acc_maxBal    := [a \in Acceptors |-> 0]
  /\ prop_val      := [v \in Proposers |-> {}]
  /\ prop_balnum   := [v \in Proposers |-> 0]
  /\ msg           := [req |-> {}, rec |-> {}, ack |-> {}]

InitPropose(p) ==
  /\ prop_balnum[p] = 0
  /\ prop_balnum' := [prop_balnum EXCEPT ![p] = 1]
  /\ prop_val' := [prop_val EXCEPT ![p] = {p}]
  /\ SendReq([src |-> p, bal |-> [num |-> 1, val |-> {p}]])
  /\ UNCHANGED << acc_maxVBal, acc_maxBal >>

\* @type: Set(MACK) => COMMITABLE_VALUE;
ChooseValue(M) ==
  LET 
      V == {m.bal.val : m \in M}
      O4(v) == 
        \E Q \in Quorums:
        \A m \in {m \in M: m.src \in Q}: \* Q \cup M.src
          m.bal.val = v
  IN IF \E v \in V: O4(v)
     THEN CHOOSE v \in V: TRUE
     ELSE UNION V

\* @type: PRO => Bool;
Request(p) ==
  \E votes \in SUBSET {m \in msg.ack: m.balnum = prop_balnum[p]}:
  LET balnums == {m.bal.num: m \in votes}
      maxBalNum == CHOOSE b \in balnums: \A b1 \in balnums: b1 <= b
      v == ChooseValue({m \in votes: m.bal.num = maxBalNum})
  IN /\ \E Q \in Quorums: Q \subseteq {m.src: m \in votes}
     /\ prop_val' := [prop_val EXCEPT ![p] = v]
     /\ prop_balnum' := [prop_balnum EXCEPT ![p] = prop_balnum[p] + 1]
     /\ SendReq([src |-> p, bal |-> [val |-> v, num |-> prop_balnum[p]]])
     /\ UNCHANGED <<acc_maxVBal, acc_maxBal >>

\* Used to force a response from a quorum of proposers
\* @type: PRO => Bool;
Recover(p) ==
  LET balnum == prop_balnum[p] + 1
  IN
  /\ prop_balnum' := [prop_balnum EXCEPT ![p] = balnum]
  /\ SendRec([src |-> p, balnum |-> balnum])
  /\ UNCHANGED << acc_maxVBal, acc_maxBal, prop_val >>

\* @type: ACC => Bool;
ReplyReq(a) ==
  \E m \in msg.req:
    /\ m.balnum > acc_maxBal[a]
    /\ SendAck([src |-> a, bal |-> m.bal, balnum |-> m.balnum])
    /\ acc_maxBal' := [acc_maxBal EXCEPT ![a] = m.balnum]
    /\ acc_maxVBal' := [acc_maxVBal EXCEPT ![a] = m.bal]
    /\ UNCHANGED << prop_val, prop_balnum >>

\* @type: ACC => Bool;
ReplyRecover(a) ==
  \E m \in msg.rec:
    /\ m.balnum > acc_maxBal[a]
    /\ SendAck([src |-> a, bal |-> acc_maxVBal[a], balnum |-> m.balnum])
    /\ acc_maxBal' = [acc_maxBal EXCEPT ![a] = m.balnum]
    /\ UNCHANGED << acc_maxVBal, prop_val, prop_balnum >>

Next ==
  \/ \E p \in Proposers: \/ InitPropose(p)
                         \/ Request(p)
                         \/ Recover(p)
  \/ \E a \in Acceptors: \/ ReplyReq(a)
                         \/ ReplyRecover(a)

Spec == /\ Init 
        /\ [][Next]_vars 

UsedBallotNumbers == 
  {m.bal.num: m \in msg.req} \union
  {m.balnum: m \in msg.rec}  \union
  {m.bal.num: m \in msg.ack} \union
  {m.balnum: m \in msg.ack}

\* A ballot can be committed if there exists a quorum of responses for it
Committable(v, b) ==
  \E Q \in Quorums:
  \A a \in Q: \E m \in msg.ack: 
    /\ m.src = a
    /\ m.bal = [val |-> v, num |-> b]

ConsInv == 
  \A b1, b2 \in UsedBallotNumbers, v1, v2 \in SUBSET PropValues:
    (Committable(v1, b1) /\ Committable(v2, b2))    => v1 = v2

NonTriviality == 
  \A v \in SUBSET PropValues: 
    (\E b \in UsedBallotNumbers: Committable(v, b)) => /\ v /= {} 
                                                    /\ \A c \in v: c \in PropValues 

\*----- Apalache -----

StateInv == /\ ConsInv
            /\ NonTriviality

\*ConstInit4 == 
\*  /\ Acceptors = {"a1", "a2", "a3", "a4"}
\*  /\ PropValues = {"w", "x", "y", "z"}

ConstInit_4_2 == 
  /\ Acceptors := Gen(4)
  /\ PropValues := Gen(2)

\* Full inductive invariant

BallotLimit == 3
TBallotNum == 0..BallotLimit
TValue == SUBSET PropValues
TBallot == [val : TValue, num : TBallotNum]
TMReq == [src : Proposers, bal : TBallot]
TMRec == [src : Proposers, balnum : TBallotNum]
TMAck == [src : Acceptors, bal : TBallot, balnum : TBallotNum]

TypeOk ==
  /\ msg \in [req : SUBSET TMReq, rec : SUBSET TMRec, ack : SUBSET TMAck]
  /\ msg.req \subseteq TMReq
  /\ msg.rec \subseteq TMRec
  /\ msg.ack \subseteq TMAck
  /\ acc_maxVBal   \in [Acceptors -> TBallot]
  /\ acc_maxBal    \in [Acceptors -> TBallotNum]
  /\ prop_val      \in [Proposers -> TValue]
  /\ prop_balnum   \in [Proposers -> TBallotNum]

InvAckBalnum ==
  \A m \in msg.ack:
    /\ m.balnum >= m.bal.num

InvAccState ==
  \A m \in msg.ack:
    (\A m1 \in msg.ack: 
       /\ m.src = m1.src
       /\ m.bal.num >= m1.bal.num
    ) => acc_maxVBal[m.src].bal = m.bal 
  
InvStateValid == 
  /\ TypeOk
  /\ InvAckBalnum
  /\ InvAccState

CommittedValuesAreReproposed ==
  \A b \in UsedBallotNumbers:
     \A v \in TValue: 
       Committable(v, b)
       => \A m \in {m \in msg.req: m.bal.num > b}: m.bal.val = v

InvSafety ==
  /\ CommittedValuesAreReproposed

IndInv == 
  /\ InvStateValid
  /\ InvSafety

\* This ensures that after a single step the ballots are in 0..BallotLimit
BallotsBounded == \A p \in Proposers: prop_balnum[p] < BallotLimit

IndInvInit ==
  /\ IndInv
  /\ BallotsBounded

=============================================================================

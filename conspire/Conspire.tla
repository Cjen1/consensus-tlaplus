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

EXTENDS Integers, FiniteSets, Apalache, Sequences

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
  \* @type: PRO -> BALLOTNUMBER;
  prop_balnum,
  \* @type: [req: Set(MREQ), rec: Set(MREC), ack: Set(MACK)];
  msg,

\*@typeAlias: PRO = VALUE;
\*@typeAlias: COMMITABLE_VALUE = Set(VALUE);
\*@typeAlias: BALLOTNUMBER = Int;
\*@typeAlias: BALLOT = [num : BALLOTNUMBER, val : COMMITABLE_VALUE];
\*@typeAlias: MREQ   = [src : PRO, bal : BALLOT];
\*@typeAlias: MREC   = [src : PRO, balnum : BALLOTNUMBER];
\*@typeAlias: MACK   = [src : ACC, bal : BALLOT, balnum : BALLOTNUMBER]; 

vars == << acc_maxVBal, acc_maxBal, prop_balnum, msg >>

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
  /\ prop_balnum   := [v \in Proposers |-> 0]
  /\ msg           := [req |-> {}, rec |-> {}, ack |-> {}]

\* If a value may have been decided then choose that, otherwise return set of possible values
\* @type: Set(MACK) => COMMITABLE_VALUE;
ChooseValue(votes) ==
  LET balnums == {m.bal.num: m \in votes}
      maxBalNum == CHOOSE b \in balnums: \A b1 \in balnums: b1 <= b
      M == {m\in votes: m.bal.num = maxBalNum}
      V == {m.bal.val : m \in M}
      O4(v) == 
        \E Q \in Quorums:
        \A m \in {m \in M: m.src \in Q}: \* Q \cup M.src
          m.bal.val = v
  IN IF \E v \in V: O4(v)
     THEN CHOOSE v \in V: TRUE \* A value may have been chosen
     ELSE UNION V \* No value chosen => can choose 'best' value

\* Send write and read
Request(p) ==
  \/ /\ prop_balnum[p] = 0
     /\ prop_balnum' := [prop_balnum EXCEPT ![p] = 1]
     /\ SendReq([src |-> p, bal |-> [num |-> 0, val |-> prop_val[p]]])
     /\ UNCHANGED << acc_maxVBal, acc_maxBal >>
  \/ \E Q \in Quorums:
     LET votes == {m \in msg.acks: m.balnum = prop_balnum[p] /\ m.src \in Q}
         pv = ChooseValue(votes)
         v == IF PV /= {} THEN PV ELSE prop_val[p]
     IN
     /\ \A a \in Q: \E m \in votes: m.src = a
     /\ SendReq([src |-> p, bal |-> [val |-> v, num |-> prop_balnum[p]]])
     /\ prop_balnum' := [prop_balnum EXCEPT ![p] = prop_balnum[p] + 1]
     /\ UNCHANGED << acc_maxVBal, acc_maxBal >>

\* Just send read
Recover(p) ==
  /\ prop_balnum' := [prop_balnum EXCEPT ![p] = prop_balnum[p] + 1]
  /\ SendRec([src |-> p, balnum |-> prop_balnum[p] + 1])
  /\ UNCHANGED << acc_maxVBal, acc_maxBal >>

\* We limit acceptors to one response here, since we have no explicit message loss
\* In a real system recving a read would prompt a response
DoRec(a, m, bal) ==
  \E m \in msg.req:
  /\ m.balnum > acc_maxBal[a]
  /\ acc_maxBal' = [acc_maxBal EXCEPT ![a] = m.balnum]
  /\ SendAck([src |-> a, bal |-> bal, balnum |-> m.balnum])
  /\ UNCHANGED << prop_balnum >>

\* Rec(balnum) is a read for balnum
RecvRec(a) ==
  \E m \in msg.req: 
  /\ DoRec(a, m, acc_maxVBal[a])
  /\ UNCHANGED << acc_maxVBal >>

\* Req(bal) is a write for bal.num, piggybacked with a read for bal.num + 1
RecvReq(a) ==
  \E m \in msg.req:
  /\ m.bal.num >= acc_maxBal[a]
  /\ acc_maxVBal' = [acc_maxVBal EXCEPT ![a] = m.bal]
  /\ DoRec(a, [src |-> m.src, balnum |-> m.bal.num + 1], m.bal)

Next ==
  \/ \E p \in Proposers: \/ Request(p)
                         \/ Recover(p)
  \/ \E a \in Acceptors: \/ RecvReq(a)
                         \/ RecvRec(a)

Spec == /\ Init 
        /\ [][Next]_vars 

UsedBallotNumbers == 
  {m.bal.num: m \in msg.req} \union
  {m.balnum: m \in msg.rec}  \union
  {m.bal.num: m \in msg.ack} \union
  {m.balnum: m \in msg.ack}

\* A ballot can be committed in b if there exists a quorum of responses for it
\* This can be extended to the consecutive ballots thingy-mabob
Committable(v, b) ==
  \E Q \in Quorums:
  \A a \in Q: \E m \in msg.ack: 
    /\ m.src = a
    /\ m.bal = [val |-> v, num |-> b]
    /\ m.balnum = b

ConsInv == 
  \A b1, b2 \in UsedBallotNumbers, v1, v2 \in SUBSET PropValues:
    (Committable(v1, b1) /\ Committable(v2, b2))    => v1 = v2

\*----- Apalache -----

StateInv == /\ ConsInv
            /\ NonTriviality

ConstInit_4 == 
  /\ Acceptors = {Gen(1), Gen(1), Gen(1), Gen(1)}
  /\ PropValues = {Gen(1), Gen(1), Gen(1), Gen(1)}
  /\ Cardinality(Acceptors) = 4
  /\ Cardinality(PropValues) = 4

ConstInit_4_2 == 
  /\ Acceptors = {Gen(1), Gen(1), Gen(1), Gen(1)}
  /\ PropValues = {Gen(1), Gen(1)}
  /\ Cardinality(Acceptors) = 4
  /\ Cardinality(PropValues) = 2

ConstInit_1 ==
  /\ Acceptors = {Gen(1)}
  /\ PropValues = {Gen(1)}
  /\ Cardinality(Acceptors) = 1
  /\ Cardinality(PropValues) = 1

\*ConstInit_4_2 == 
\*  /\ Acceptors := Gen(4)
\*  /\ PropValues := Gen(2)

\* Full inductive invariant
(*

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

InvBalAndNum ==
  /\ \A m \in msg.ack:
       /\ m.balnum >= m.bal.num
  /\ \A a \in Acceptors:
      acc_maxBal[a] >= acc_maxVBal[a].num

InvMaxAckEqAcc ==
  \A a \in Acceptors:
     \A m1 \in msg.ack:
       \* If this is the 'newest' message
       (\A m2 \in msg.ack: m1.balnum >= m2.balnum)
       => /\ acc_maxBal[a] = m1.balnum
          /\ acc_maxVBal[a] = m1.bal

InvAckMutex ==
  \A m1, m2 \in msg.ack:
    (m1.balnum = m2.balnum /\ m1.src = m2.src) => m1 = m2

InvAccAck ==
  /\ \A m \in msg.ack: m.balnum > 0
  \* Written by an req, and could be committable
  /\ \A m \in msg.ack: m.balnum = m.bal.num => Cardinality(m.bal.val) >= 1 
  /\ InvBalAndNum
  /\ InvMaxAckEqAcc
  /\ InvAckMutex

InvReqQuorum ==
  \A m \in msg.req:
  \* Initial msg
  \/ m.bal.num = 1
  \* Response from quorum
  \/ /\ m.bal.num > 1
     /\ \E Q \in Quorums:
        LET votes == {ma \in msg.ack: ma.balnum = m.bal.num - 1 /\ ma.src \in Q}
            PV == ChooseValue(votes)
        IN /\ \A a \in Q: \E ma \in votes: ma.src = a
           /\ \/ /\ PV =  {} 
                 /\ m.bal.val \in {{v} :v \in PropValues}
              \/ /\ PV /= {} 
                 /\ m.bal.val = PV

InvReqRecMutex ==
  /\ \A mq \in msg.req, mc \in msg.rec: ~(mq.src = mc.src /\ mq.bal.num = mc.balnum)

InvReqRecBalnum ==
  /\ \A mq \in msg.req: mq.bal.num <= prop_balnum[mq.src]
  /\ \A mc \in msg.rec: mc.balnum <= prop_balnum[mc.src]

InvMaxReqRecProp ==
  \A p \in Proposers:
  LET req == {m \in msg.req : m.src = p}
      rec == {m \in msg.rec : m.src = p}
      req_bal == {m.bal.num : m \in req}
      rec_bal == {m.balnum : m \in rec}
      balnums == req_bal \union rec_bal
  IN
  \* Balnum is max of req and rec msgs
  /\ \A b1 \in balnums: 
      (\A b2 \in balnums: b1 >= b2)
      => prop_balnum[p] = b1
  \* max bal in req defines val
  /\ \/ /\ Cardinality(req) > 0 
        /\ \A m \in req:
             (\A m1 \in req: m.bal.num >= m1.bal.num)
             => prop_val[p] = m.bal.val
     \/ /\ prop_val[p] = {p}

InvReqRecProp ==
  /\ \A p \in Proposers: prop_val[p] /= {}
  /\ InvReqQuorum
  /\ InvReqRecMutex
  /\ InvReqRecBalnum
  /\ InvMaxReqRecProp

InvStateValid == 
  /\ TypeOk
  /\ InvAccAck
  /\ InvReqRecProp

CommittedValuesAreReproposed ==
  \A b \in UsedBallotNumbers:
     \A v \in TValue: 
       Committable(v, b)
       => \A m \in {m \in msg.req: m.bal.num > b}: m.bal.val = v

InvSafety ==
  /\ CommittedValuesAreReproposed

IndInv == 
  /\ Cardinality(Quorums) >= 1
  /\ InvStateValid
  /\ InvSafety

\* This ensures that after a single step the ballots are in 0..BallotLimit
BallotsBounded == \A p \in Proposers: prop_balnum[p] < BallotLimit

IndInvInit ==
  /\ Hist = << >>
  /\ IndInv
  /\ BallotsBounded
  *)

=============================================================================

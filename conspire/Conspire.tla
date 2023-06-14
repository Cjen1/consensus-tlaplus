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

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS 
  \* @type: Set(ACC);
  Acceptors, 
  \* @type: Set(VALUE);
  PropValues,
  \* @type: BALLOTNUMBER;
  BallotLimit

VARIABLES 
  \* @type: ACC -> BALLOTNUMBER;
  acc_maxBal,
  \* @type: ACC -> BALLOT;
  acc_maxVBal,
  \* @type: PRO -> BALLOTNUMBER;
  prop_balnum,
  \* @type: [req: Set(MREQ), rec: Set(MREC), ack: Set(MACK)];
  msg

PrintVal(id, exp)  ==  Print(<<id, exp>>, TRUE)

LEQ(A,B) == A \subseteq B

\*LEQ(a,b) ==
\*  /\ Len(a) =< Len(b)
\*  /\ \A i \in DOMAIN a: a[i] = b[i]

\* Must preserve: \A v \in LBs: v < RES
Merge(LBs, Vs) == UNION LBs \union UNION Vs

\*@typeAlias: PRO = VALUE;
\*@typeAlias: COMMITABLE_VALUE = Set(VALUE);
\*@typeAlias: BALLOTNUMBER = Int;
\*@typeAlias: BALLOT = [num : BALLOTNUMBER, val : COMMITABLE_VALUE];
\*@typeAlias: MREQ   = [src : PRO, bal : BALLOT];
\*@typeAlias: MACK   = [src : ACC, bal : BALLOT, balnum : BALLOTNUMBER]; 

vars == << acc_maxVBal, acc_maxBal, prop_balnum, msg >>

Proposers == PropValues

\* This is the simple majority quorums approach
\* Fast flexible paxos should be feasible
Quorums == {Q \in SUBSET Acceptors: Cardinality(Q) = (2 * Cardinality(Acceptors)) \div 3 + 1}

SendReq(m) == msg' = [msg EXCEPT !.req = msg.req \union {m}]
SendAck(m) == msg' = [msg EXCEPT !.ack = msg.ack \union {m}]

Init == 
  /\ acc_maxVBal   = [a \in Acceptors |-> [val |-> {}, num |-> 0]]
  /\ acc_maxBal    = [a \in Acceptors |-> 0]
  /\ prop_balnum   = [v \in Proposers |-> 0]
  /\ msg           = [req |-> {}, ack |-> {}]

\* If a value may have been decided then choose that, otherwise return set of possible values
\* @type: Set(MACK) => COMMITABLE_VALUE;
ChooseValue(votes) ==
  LET balnums == {m.bal.num: m \in votes}
      maxBalNum == CHOOSE b \in balnums: \A b1 \in balnums: b1 <= b
      M == {m\in votes: m.bal.num = maxBalNum}
      V == {m.bal.val : m \in M}
      O4(v) == 
        \E Q \in Quorums:
        \A m \in {m \in M: m.src \in Q}: LEQ(v, m.bal.val)
      \* Use either what could have been committed
      VO4 == {v \in V: O4(v)}
  IN Merge(VO4, V)

Request(p) ==
  \/ /\ prop_balnum[p] = 0
     /\ prop_balnum' = [prop_balnum EXCEPT ![p] = 1]
     /\ SendReq([src |-> p, bal |-> [num |-> 0, val |-> {p}]])
     /\ UNCHANGED << acc_maxBal, acc_maxVBal >>
  \* Steady state
  \/ \E b \in {m.balnum : m \in msg.ack}:
     /\ b >= prop_balnum[p]
     /\ \E votes \in SUBSET {m \in msg.ack: m.balnum = b}:
        LET pv == ChooseValue(votes)
            v == IF pv /= {} THEN pv ELSE {p}
        IN
        \* valid votes
        /\ \E Q \in Quorums: \A a \in Q: \E m \in votes: m.src = a
        \* Update balnum and send req
        /\ prop_balnum' = [prop_balnum EXCEPT ![p] = b]
        /\ SendReq([src |-> p, bal |-> [val |-> v, num |-> b]])
        /\ UNCHANGED << acc_maxBal, acc_maxVBal >>

(* If conflict increment term, to allow non-conflict pipelining *)
(* If old msg generate response for this term *)
RecvReq(a) ==
  \E m \in msg.req:
  LET newer_balnum == m.bal.num > acc_maxBal[a]
      should_update == /\ m.bal.num >= acc_maxBal[a]
                       /\ \/ m.bal.num > acc_maxVBal[a].num
                          \/ m.bal.num = acc_maxVBal[a].num /\ LEQ(acc_maxVBal[a].val, m.bal.val)
      must_increment == /\ m.bal.num = acc_maxBal[a]
                        /\ m.bal.num = acc_maxVBal[a].num /\ ~LEQ(acc_maxVBal[a].val, m.bal.val)
      \* @type: BALLOTNUMBER;
      new_balnum == IF newer_balnum 
                    THEN m.bal.num 
                    ELSE IF must_increment
                         THEN acc_maxBal[a] + 1
                         ELSE acc_maxBal[a]
      \* @type: BALLOT;
      new_vbal   == IF should_update THEN m.bal ELSE acc_maxVBal[a]
  IN 
  /\ acc_maxBal' = [acc_maxBal EXCEPT ![a] = new_balnum]
  /\ acc_maxVBal' = [acc_maxVBal EXCEPT ![a] = new_vbal]
  /\ SendAck([src |-> a, balnum |-> new_balnum, bal |-> new_vbal])
  /\ UNCHANGED << prop_balnum >>

Next ==
  \/ \E p \in Proposers: Request(p)
  \/ \E a \in Acceptors: RecvReq(a)

Spec == /\ Init 
        /\ [][Next]_vars 

UsedBallotNumbers == 
  {m.bal.num: m \in msg.req} \union
  {m.bal.num: m \in msg.ack} \union
  {m.balnum: m \in msg.ack}

UsedValues ==
  {m.bal.val: m \in msg.req} \union
  {m.bal.val: m \in msg.ack}

\* A ballot can be committed in b if there exists a quorum of responses for larger values
\* This can be extended to the consecutive ballots thingy-mabob
Committable(v, b) ==
  \E Q \in Quorums:
  \A a \in Q: \E m \in msg.ack: 
    /\ m.src = a
    /\ m.bal.num = b
    /\ LEQ(v, m.bal.val)

CanCommit(v) ==
  \E b \in UsedBallotNumbers: Committable(v,b)

Serialised ==
  \A v1, v2 \in UsedValues:
    /\ (/\ \E b \in UsedBallotNumbers: Committable(v1, b)
        /\ \E b \in UsedBallotNumbers: Committable(v2, b)
       ) => \/ LEQ(v1, v2)
            \/ LEQ(v2, v1)

Pipelined == FALSE

CommitAll == CanCommit(PropValues)

Inv ==
  /\ Serialised
  /\ ~CommitAll

BallotsBounded == \A p \in Proposers: prop_balnum[p] < BallotLimit

\*----- Apalache -----

(*
StateInv == /\ ConsInv

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
*)

=============================================================================

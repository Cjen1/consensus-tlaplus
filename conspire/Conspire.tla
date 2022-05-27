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

EXTENDS Integers, FiniteSets, TLC

CONSTANTS 
  \* @type: Set(ID);
  Acceptors, 
  \* @type: Set(ID);
  PropValues

VARIABLES 
  \* @type: Str -> BALLOT;
  acc_maxVBal,
  \* @type: Str -> BALLOTNUMBER;
  acc_maxBal,
  \* @type: Str -> COMMITABLE_VALUE;
  prop_val,
  \* @type: Str -> BALLOTNUMBER;
  prop_balnum,
  \* @type: Str -> Set(MESSAGE);
  prop_recv_buf,
  \* @type: Set(MESSAGE);
  msg

\*@typeAlias: ID = Str;
\*@typeAlias: COMMITABLE_VALUE = Set(ID);
\*@typeAlias: BALLOTNUMBER = Int;
\*@typeAlias: BALLOT = [num : BALLOTNUMBER, val : COMMITABLE_VALUE];
\*@typeAlias: MESSAGE = [tag: Str, src : Str, bal : BALLOT, balnum: BALLOTNUMBER];

vars == << acc_maxVBal, acc_maxBal, prop_val, prop_balnum, msg, prop_recv_buf >>

Proposers == PropValues

\* This is the simple majority quorums approach
\* Fast flexible paxos should be feasible
Quorums == {Q \in SUBSET Acceptors: Cardinality(Q) = (2 * Cardinality(Acceptors)) \div 3 + 1}

Send(m) == msg' = msg \cup {m}

Init == 
  /\ acc_maxVBal       = [a \in Acceptors |-> [val |-> {}, num |-> 0]]
  /\ acc_maxBal   = [a \in Acceptors |-> 0]
  /\ prop_val      = [v \in Proposers |-> {}]
  /\ prop_balnum   = [v \in Proposers |-> 0]
  /\ prop_recv_buf = [v \in Proposers |-> {}]
  /\ msg           = {}

InitPropose(p) ==
  /\ prop_balnum[p] = 0
  /\ prop_balnum' = [prop_balnum EXCEPT ![p] = 1]
  /\ prop_val' = [prop_val EXCEPT ![p] = {p}]
  /\ Send([tag |-> "req", src |-> p, bal |-> [num |-> 1, val |-> {p}], balnum |-> 1])
  /\ UNCHANGED << acc_maxVBal, acc_maxBal, prop_recv_buf >>

RecvAck(p) ==
  \E m \in {m \in msg: m.tag = "ack"}:
    /\ m.balnum = prop_balnum[p]
    /\ prop_recv_buf' = [prop_recv_buf EXCEPT ![p] = prop_recv_buf[p] \cup {m}]
    /\ UNCHANGED << acc_maxVBal, acc_maxBal, prop_balnum, prop_val, msg>>

\* @type: Set(MESSAGE) => COMMITABLE_VALUE;
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

\* @type: ID => Bool;
Request(p) ==
  LET votes == {m \in prop_recv_buf[p]: m.tag = "ack" /\ m.balnum = prop_balnum[p]}
      balnums == {m.bal.num: m \in votes}
      maxBalNum == CHOOSE b \in balnums: \A b1 \in balnums: b1 <= b
      v == ChooseValue({m \in votes: m.bal.num = maxBalNum})
  IN /\ \E Q \in Quorums: Q \subseteq {m.src: m \in votes}
     /\ prop_val' = [prop_val EXCEPT ![p] = v]
     /\ prop_balnum' = [prop_balnum EXCEPT ![p] = prop_balnum[p] + 1]
     /\ Send([tag |-> "req", src |-> p, bal |-> [val |-> v, num |-> prop_balnum[p]]])
     /\ prop_recv_buf' = [prop_recv_buf EXCEPT ![p] = {}]
     /\ UNCHANGED <<acc_maxVBal, acc_maxBal >>

\* Used to force a response from a quorum of proposers
\* @type: ID => Bool;
Recover(p) ==
  LET balnum == prop_balnum[p] + 1
  IN
  /\ prop_balnum' = [prop_balnum EXCEPT ![p] = balnum]
  /\ prop_recv_buf' = [prop_recv_buf EXCEPT ![p] = {}]
  /\ Send([tag |-> "rec", src |-> p, balnum |-> balnum])
  /\ UNCHANGED << acc_maxVBal, acc_maxBal, prop_val >>

\* @type: ID => Bool;
ReplyReq(a) ==
  \E m \in {m \in msg: m.tag = "req"}:
    /\ m.balnum > acc_maxBal[a]
    /\ Send([tag |-> "ack", src |-> a, bal |-> m.bal, balnum |-> m.balnum])
    /\ acc_maxBal' = [acc_maxBal EXCEPT ![a] = m.balnum]
    /\ acc_maxVBal' = [acc_maxVBal EXCEPT ![a] = m.bal]
    /\ UNCHANGED << prop_val, prop_balnum, prop_recv_buf >>

\* @type: ID => Bool;
ReplyRecover(a) ==
  \E m \in {m \in msg: m.tag = "rec"}:
    /\ m.balnum > acc_maxBal[a]
    /\ Send([tag |-> "ack", src |-> a, bal |-> acc_maxVBal[a], balnum |-> m.balnum])
    /\ acc_maxBal' = [acc_maxBal EXCEPT ![a] = m.balnum]
    /\ UNCHANGED << acc_maxVBal, prop_val, prop_balnum, prop_recv_buf >>

Next ==
  \/ \E p \in Proposers: \/ InitPropose(p)
                         \/ RecvAck(p)
                         \/ Request(p)
                         \/ Recover(p)
  \/ \E a \in Acceptors: \/ ReplyReq(a)
                         \/ ReplyRecover(a)

Spec == /\ Init 
        /\ [][Next]_vars 

Symmetry == Permutations(PropValues) \union Permutations(Acceptors)

UsedBallotNumbers == {m.bal.num: m \in msg}

\* A ballot can be committed if there exists a quorum of responses for it
Committable(v, b) ==
  \E Q \in Quorums:
  \A a \in Q: \E m \in msg: 
    /\ m.tag = "ack"
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

ConstInit4 == 
  /\ Acceptors = {"a1", "a2", "a3", "a4"}
  /\ PropValues = {"w", "x", "y", "z"}

ConstInit_4_2 == 
  /\ Acceptors = {"a1", "a2", "a3", "a4"}
  /\ PropValues = {"x", "y"}

BallotLimit == 5
\* This ensures that after a single step the ballots are in 0..5
BallotsBounded == \A p \in Proposers: prop_balnum[p] < BallotLimit

\* Full inductive invariant

TBallotNum == 0..BallotLimit
TVALUE == SUBSET PropValues
TBallot == [val : TVALUE, num : TBallotNum]
TMsg == [tag : {"req"},  src : Proposers, bal : TBallot] \union
        [tag : {"rec"}, src : Proposers, balnum : TBallotNum] \union
        [tag : {"ack"},  src : Acceptors, bal : TBallot, balnum : TBallotNum]

TypeOk ==
  /\ msg \in SUBSET TMsg
  /\ acc_maxVBal   \in [Acceptors -> TBallot]
  /\ acc_maxBal    \in [Acceptors -> TBallotNum]
  /\ prop_val      \in [Proposers -> TVALUE]
  /\ prop_balnum   \in [Proposers -> TBallotNum]
  /\ prop_recv_buf \in [Proposers -> SUBSET TMsg]

InvAckBalnum ==
  \A m \in msg:
    /\ m.tag = "ack"
    /\ m.balnum >= m.bal.num

InvAccState ==
  \A m \in msg: 
    /\ m.tag = "ack" 
    /\ \A m1 \in msg: 
          /\ m.src = m1.src
          /\ m.bal.num >= m.bal.num
    => acc_maxVBal[m.src].bal = m.bal 
  
InvPropBuf ==
  \A p \in PropValues:
  \A m \in prop_recv_buf[p]:
     /\ m \in msg 
     /\ m.balnum = prop_balnum[p]

InvStateValid == 
  /\ TypeOk
  /\ InvAckBalnum
  /\ InvAccState
  /\ InvPropBuf

CommittedValuesAreReproposed ==
  \A b \in UsedBallotNumbers:
     \A v \in SUBSET PropValues: 
       Committable(v, b)
       => \A m \in {m \in msg: m.tag = "req" /\ m.bal.num > b}: m.bal.val = v

InvSafety ==
  /\ CommittedValuesAreReproposed

IndInv == 
  /\ InvStateValid
  /\ InvSafety

IndInvInit ==
  /\ IndInv
  /\ BallotsBounded

=============================================================================

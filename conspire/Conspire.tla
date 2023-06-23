----------------------------- MODULE Conspire -----------------------------
(*
This protocol is a collaborative variation of FastPaxos
It allows multiple proposers to do the recovery after a conflict in FastPaxos

Notable points 
- Acceptors increment their term when they encounter a value which conflicts with their current value
  - This generates the votes required to fully recover the current state
  - It also means that the maximum round in a set of votes will either be the maximum round which exists or the one before it
- Any proposer can send a write message, so long as it is greater than values in previous rounds

- For efficiency we reduce our checks to just the values which are proposed, rather than the set of all possible values.

*)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS 
  \* @type: Set(ACC);
  Acceptors, 
  \* @type: Set(VALUE);
  PropValues

VARIABLES 
  \* @type: ACC -> BALLOTNUMBER;
  acc_maxBal,
  \* @type: ACC -> BALLOT;
  acc_maxVBal,
  \* @type: PRO -> BALLOTNUMBER;
  prop_balnum,
  \* @type: PRO -> COMMITABLE_VALUE;
  prop_val,
  \* @type: [req: Set(MREQ), rec: Set(MREC), ack: Set(MACK)];
  msg

\*@typeAlias: PRO = VALUE;
\*@typeAlias: COMMITABLE_VALUE = Seq(VALUE);
\*@typeAlias: BALLOTNUMBER = Int;
\*@typeAlias: BALLOT = [num : BALLOTNUMBER, val : COMMITABLE_VALUE];
\*@typeAlias: MREQ   = BALLOT;
\*@typeAlias: MACK   = [src : ACC, bal : BALLOT, balnum : BALLOTNUMBER]; 

\*====================
\* Utility functions
\*====================

\* @type: (a -> x) => Set(x);
Range(S) == {S[i] : i \in DOMAIN S}
\* @type: Seq(x) => Set(x);
RangeS(S) == {S[i] : i \in DOMAIN S}

UsedValues ==
  {m.val: m \in msg.req} \union
  {m.bal.val: m \in msg.ack} \union
  {acc_maxVBal[a].val: a \in Acceptors}
   
UsedBallotNumbers == 
  {m.num: m \in msg.req} \union
  {m.bal.num: m \in msg.ack} \union
  {m.balnum: m \in msg.ack} \union
  Range(prop_balnum) \union
  Range(acc_maxBal) \union
  {b.num : b \in Range(acc_maxVBal)}

Proposers == PropValues

\*----------
\* Spec utility funcs 
\*----------
vars == << acc_maxVBal, acc_maxBal, prop_balnum, prop_val, msg >>

\* This is the simple majority quorums approach
\* Fast flexible paxos should be feasible
Quorums == {Q \in SUBSET Acceptors: Cardinality(Q) = (2 * Cardinality(Acceptors)) \div 3 + 1}

SendReq(m) == m \notin msg.req /\ msg' = [msg EXCEPT !.req = msg.req \union {m}]
SendAck(m) == m \notin msg.ack /\ msg' = [msg EXCEPT !.ack = msg.ack \union {m}]

Init == 
  /\ acc_maxVBal   = [a \in Acceptors |-> [val |-> <<>>, num |-> -1]]
  /\ acc_maxBal    = [a \in Acceptors |-> 0]
  /\ prop_balnum   = [v \in Proposers |-> -1]
  /\ prop_val      = [v \in Proposers |-> <<>>]
  /\ msg           = [req |-> {}, ack |-> {}]

\*====================
\* Specialisation for logs
\*====================
LEQ(a,b) ==
  /\ Len(a) =< Len(b)
  /\ \A i \in DOMAIN a: a[i] = b[i]

\*====================
\* Node actions
\*====================

ReqInit(p) ==
  /\ prop_balnum[p] = -1
  /\ prop_balnum' = [prop_balnum EXCEPT ![p] = 0]
  /\ prop_val' = [prop_val EXCEPT ![p] = <<p>>]
  /\ SendReq([num |-> 0, val |-> <<p>>])
  /\ UNCHANGED << acc_maxBal, acc_maxVBal >>

\* @type: Set(MACK) => Set(COMMITABLE_VALUE);
ChoosableValues(votes) ==
  LET balnums == {m.bal.num: m \in votes}
      maxBalNum == CHOOSE b \in balnums: \A b1 \in balnums: b1 <= b
      M == {m\in votes: m.bal.num = maxBalNum}
      \* there exists a quorum which could have committed v
      O4(v) == 
        \E Q \in Quorums:
        \A a \in Q:
        \* a voted for larger value
        \/ \E m \in M: /\ m.src = a 
                       /\ LEQ(v, m.bal.val)
        \* a did not vote => we assume it voted for this one
        \/ ~ \E m \in votes: m.src = a
      UsedVals == {v \in UsedValues: \E m \in votes: LEQ(v, m.bal.val)}
  IN 
  {
    v \in UsedVals: 
    /\ \A l \in UsedVals: O4(l) => LEQ(l, v) \* correctness (if commit in prev term)
    /\ \E m \in M: LEQ(m.bal.val, v)         \* correctness (inductive)
  }

Request(p) ==
  \E b \in {m.balnum : m \in msg.ack}:
  /\ b >= prop_balnum[p]
  /\ \E votes \in SUBSET {m \in msg.ack: m.balnum = b}:
     \* valid votes
     /\ \E Q \in Quorums: \A a \in Q: \E m \in votes: m.src = a
     \* choose value
     /\ \E lb \in ChoosableValues(votes):
        LET v == IF p \notin RangeS(lb) THEN lb \o << p >> ELSE lb IN
        \* Update balnum and send req:
        /\ b = prop_balnum[p] => LEQ(prop_val[p], v)
        /\ prop_val' = [prop_val EXCEPT ![p] = v]
        /\ prop_balnum' = [prop_balnum EXCEPT ![p] = b]
        /\ SendReq([val |-> v, num |-> b])
        /\ UNCHANGED << acc_maxBal, acc_maxVBal >>

(* If conflict increment term, to allow non-conflict pipelining *)
(* If old msg generate response for this term *)
RecvReq(a) ==
  \E m \in msg.req:
  LET newer_balnum == m.num > acc_maxBal[a]
      should_update == /\ m.num >= acc_maxBal[a]
                       /\ \/ m.num > acc_maxVBal[a].num
                          \/ m.num = acc_maxVBal[a].num /\ LEQ(acc_maxVBal[a].val, m.val)
      must_increment == /\ m.num = acc_maxBal[a]
                        /\ m.num = acc_maxVBal[a].num /\ ~LEQ(acc_maxVBal[a].val, m.val)
      \* @type: BALLOTNUMBER;
      new_balnum == IF newer_balnum 
                    THEN m.num 
                    ELSE IF must_increment
                         THEN acc_maxBal[a] + 1
                         ELSE acc_maxBal[a]
      \* @type: BALLOT;
      new_vbal   == IF should_update THEN m ELSE acc_maxVBal[a]
  IN 
  /\ acc_maxBal' = [acc_maxBal EXCEPT ![a] = new_balnum]
  /\ acc_maxVBal' = [acc_maxVBal EXCEPT ![a] = new_vbal]
  /\ SendAck([src |-> a, balnum |-> new_balnum, bal |-> new_vbal])
  /\ UNCHANGED << prop_balnum, prop_val >>

\* A ballot can be committed in b if there exists a quorum of responses for larger values
\* This can be extended to the consecutive ballots thingy-mabob
Committable(v, b) ==
  \E Q \in Quorums:
  \A a \in Q: \E m \in msg.ack: 
    /\ m.src = a
    /\ m.bal.num = b
    /\ LEQ(v, m.bal.val)

Next ==
  \/ \E p \in Proposers: ReqInit(p) \/ Request(p)
  \/ \E a \in Acceptors: RecvReq(a)
  \/ /\ \E v \in UsedValues: RangeS(v) = PropValues /\ \E b \in UsedBallotNumbers: Committable(v,b)
     /\ UNCHANGED <<vars>>

Spec == /\ Init 
        /\ [][Next]_vars 

Serialised ==
  \A v1, v2 \in UsedValues:
    /\ (/\ \E b \in UsedBallotNumbers: Committable(v1, b)
        /\ \E b \in UsedBallotNumbers: Committable(v2, b)
       ) => \/ LEQ(v1, v2)
            \/ LEQ(v2, v1)

Inv == 
 /\ Serialised 

Symmetry == Permutations(Proposers) \union Permutations(Acceptors)

=============================================================================

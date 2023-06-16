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

\* @type: Seq(VALUE) => Set(VALUE);
Range(S) == {S[i] : i \in DOMAIN S}

UsedValues ==
  {m.bal.val: m \in msg.req} \union
  {m.bal.val: m \in msg.ack} \union
  {acc_maxVBal[a].val: a \in Acceptors}
   
UsedBallotNumbers == 
  {m.bal.num: m \in msg.req} \union
  {m.bal.num: m \in msg.ack} \union
  {m.balnum: m \in msg.ack} \union
  Range(prop_balnum) \union
  Range(acc_maxBal) \union
  {b.num : b \in Range(acc_maxVBal)}

\* @type: (_,_) => Bool;
PrintVal(id, exp)  ==  Print(<<id, exp>>, TRUE)

\*LEQ(A,B) == A \subseteq B

LEQ(a,b) ==
  /\ Len(a) =< Len(b)
  /\ \A i \in DOMAIN a: a[i] = b[i]

\* Must preserve: \A v \in LBs: v < RES
\*Merge(LBs, Vs) == UNION LBs \union UNION Vs
Merge(LBs, Vs) == 
  IF LBs = {}
  THEN CHOOSE v \in Vs: TRUE \* TODO fancy?
  ELSE IF \E v \in LBs: \A v1 \in LBs: LEQ(v1, v)
       THEN CHOOSE v \in LBs: \A v1 \in LBs: LEQ(v1, v) \* Does not work for convergent values (set, PSMR)
       ELSE PrintVal("LBs", LBs) /\ CHOOSE v \in Vs: FALSE

\*@typeAlias: PRO = VALUE;
\*@typeAlias: COMMITABLE_VALUE = Seq(VALUE);
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
  /\ acc_maxVBal   = [a \in Acceptors |-> [val |-> <<>>, num |-> -1]]
  /\ acc_maxBal    = [a \in Acceptors |-> 0]
  /\ prop_balnum   = [v \in Proposers |-> 0]
  /\ msg           = [req |-> {}, ack |-> {}]

\* If vote for next term, then take greatest-lower-bound on values which could have been committed in this terms
\* Otherwise choose GLB on all values from this term (since it'll be greater than any committed in previous terms)
\* @type: Set(MACK) => COMMITABLE_VALUE;
ChooseValue(votes) ==
  LET cbalnum == CHOOSE b \in {m.balnum: m \in votes}: TRUE
      balnums == {m.bal.num: m \in votes}
      maxBalNum == CHOOSE b \in balnums: \A b1 \in balnums: b1 <= b
      M == {m\in votes: m.bal.num = maxBalNum}
      Vs == {m.bal.val : m \in M}
      \* Generate all possibly committed lower bounds
      V == {v \in UsedValues: \E e \in Vs: LEQ(v, e)} 
      O4(v) == 
      IF cbalnum > maxBalNum
      THEN \* Then prev term is blocked, we take LUB
           \* Exists a quorum which could have been used to commit it.
           \E Q \in Quorums:
           \A a \in Q:
           \* acc vote for larger value
           \/ \E m \in M: /\ m.src = a 
                          /\ LEQ(v, m.bal.val)
           \* acc did not vote
           \/ ~ \E m \in votes: m.src = a
      ELSE \* Current term can still make progress
           \* Choose GLB
           \* This can also be inferred using prev incremnet vote
           \A m \in M: LEQ(v, m.bal.val)
      VO4 == {v \in V: O4(v)}
  IN 
  IF \/ \E v \in VO4: \A v1 \in VO4: LEQ(v1, v)
     \/ VO4 = {}
  THEN  Merge(VO4, V)
  ELSE /\ PrintVal("votes", votes)
       /\ PrintVal("VO4", VO4)
       /\ CHOOSE x \in votes: FALSE

Request(p) ==
  \/ /\ prop_balnum[p] = 0
     /\ prop_balnum' = [prop_balnum EXCEPT ![p] = 1]
     /\ SendReq([src |-> p, bal |-> [num |-> 0, val |-> <<p>>]])
     /\ UNCHANGED << acc_maxBal, acc_maxVBal >>
  \* Steady state
  \/ \E b \in {m.balnum : m \in msg.ack}:
     /\ b >= prop_balnum[p]
     /\ \E votes \in SUBSET {m \in msg.ack: m.balnum = b}:
        LET pv == ChooseValue(votes)
            v == IF p \notin Range(pv) THEN pv \o << p >> ELSE pv
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
            \/ Print([v1 |-> v1, b1 |-> CHOOSE b \in UsedBallotNumbers: Committable(v1, b) ,v2 |-> v2, b2 |-> CHOOSE b \in UsedBallotNumbers: Committable(v2, b)  ], FALSE)

Pipelined == FALSE

CommitAll ==
  \E V \in UsedValues:
  /\ \A v \in PropValues: v \in Range(V)
  /\ CanCommit(V)

Inv ==
  /\ Serialised

BallotsBounded == \A p \in Proposers: prop_balnum[p] < BallotLimit

Symmetry == Permutations(Proposers) \union Permutations(Acceptors)

=============================================================================

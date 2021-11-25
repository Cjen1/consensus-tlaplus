----------------------------- MODULE VectorPaxos -----------------------------

EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS Proposers, Acceptors, Commands
CONSTANTS Quorums, MaxChannelSize

----
(* Generic utils *)
Max(Leq(_,_), s) == CHOOSE v \in s: \A v1 \in s: Leq(v1, v)
Min(Leq(_,_), s) == CHOOSE v \in s: \A v1 \in s: Leq(v, v1)

Replace(F, F1) ==
  [x \in DOMAIN F |-> IF x \in DOMAIN F1 THEN F1[x] ELSE F[x]]

Range(F) == {F[x] : x \in DOMAIN F}

ProposerMapping == 
  CHOOSE f \in [Proposers -> 1..Cardinality(Proposers)]:
    \A p1,p2 \in Proposers: /\ p1 /= p2 => f[p1] /= f[p2] 
                            /\ p1 = p2 => f[p1] = f[p2]

BallotNumLeq(a,b) ==
  \/ a.num < b.num
  \/ a.num = b.num /\ ProposerMapping[a.prop] <= ProposerMapping[b.prop]

BallotLeq(a, b) ==
  \/ BallotNumLeq(a.b, b.b) /\ ~ BallotNumLeq(b.b, a.b)
  \/ a = b
----

(* State variables and types *)

VARIABLES State

None == CHOOSE v : v \notin Proposers /\ v \notin Commands

TProposer == Proposers
TAcceptor == Acceptors
TProcess  == TProposer \union TAcceptor
TCommand  == Commands
TValue    == TCommand \union {None}

TBalNum == Nat

TBallotNumber == [num : TBalNum, prop : Proposers \union {None}]

TBallot == [bal : TBallotNumber, val : TValue]

TMsg == [type : {"1a"}, balNum : TBallotNumber] \union
        [type : {"1b"}, balNum : TBallotNumber, maxBal : TBallot] \union
	[type : {"2a"}, bal : TBallot]

TChans == [(TProposer \X TAcceptor) \cup (TAcceptor \X TProposer) -> UNION {[1..max -> TMsg] : max \in 0..MaxChannelSize }]

TPropSM == [kind : {"follower"}] \union
           [kind : {"candidate"}, bals : [acc : TAcceptor, bal : TBallot]] \union
           [kind : {"leader"}, val : TCommand]
	   

TProp == [sm : TPropSM, balNum : TBallotNumber]

TAcc == [mBalNum : TBallotNumber, mBal : TBallot]

TState == [ chans : TChans,
            prop  : [Proposers -> TProp],
	    acc   : [Acceptors -> TAcc],
	    commit: TValue,
	    action: {"none","p1a", "p1b", "recv_p1b", "p2a"}
	  ]

----

TypeInvariant == State \in TState

Init == 
  State = [
    chans  |-> [s \in ((Proposers \X Acceptors) \union (Acceptors \X Proposers)) |-> <<>>],
    prop   |-> [p \in Proposers |-> [
                  sm |-> [kind |-> "follower"],
                  balNum |-> [num |-> 0, prop |-> p]
                  ]
               ],
    acc    |-> [a \in Acceptors |-> [mBalNum |-> [num |-> 0, prop |-> None], mBal |-> [bal |-> [prop |-> None, num |-> 0], val |-> None]]],
    commit |-> None,
    action |-> "none"
    ]

----

(* Specific utils *)

SetProp(st, p, pp) ==
  [st EXCEPT !.prop = [st.prop EXCEPT ![p] = pp]]

SetAcc(st, a, ap) ==
  [st EXCEPT !.acc = [st.acc EXCEPT ![a] = ap]]

SetAct(act, st) ==
  [st EXCEPT !.action = act]

(* Limited window reliable inorder messaging *)
SendChan(chan, m) ==
  IF Len(chan) < MaxChannelSize
  THEN chan \o << m >>
  ELSE chan

Send(st, m, s, d) ==
  [st EXCEPT !.chans = Replace(st.chans, [<<src,dst>> \in { <<s,d>> } |-> SendChan(st.chans[src,dst],m)])]

Broadcast(st, m, s, D) ==
  LET updatedChans == [<<src,dst>> \in { <<s,d>> : d \in D} |-> SendChan(st.chans[src,dst],m)]
  IN [st EXCEPT !.chans = Replace(st.chans, updatedChans)]

RecvOne(st, s, d) ==
  IF <<s,d>> \in DOMAIN st.chans /\ Len(st.chans[s,d]) > 0
  THEN [
    poss |-> TRUE,
    msg |-> Head(st.chans[s,d]),
    st |-> [st EXCEPT !.chans = [st.chans EXCEPT ![s,d] = Tail(st.chans[s,d])]],
    src |-> s
  ]
  ELSE [poss |-> FALSE]

RecvAbles(st, d) ==
  LET recvables == {RecvOne(st, s, d):s \in Proposers \union Acceptors}
  IN {rs \in recvables: rs.poss}

----

(* State transitions *)

DoPhase1a(st, p) ==
  LET pState == st.prop[p]
      nPState == [pState EXCEPT !.balNum = [num |-> pState.balNum.num + 1, prop |-> p], !.sm = [kind |-> "follower"]]
      nUState == SetProp(st, p, nPState)
      nst == Broadcast(nUState, [type |-> "1a", balNum |-> nPState.balNum], p, Acceptors)
  IN SetAct("p1a", nst)

DoPhase1b(st, a, p, m1a) ==
  LET aState == st.acc[a]
      m1b == [type |-> "1b", balNum |-> m1a.balNum, maxBal |-> aState.mBal]
      nAState == [aState EXCEPT !.mBalNum = m1a.balNum]
      uState == SetAcc(st, a, nAState)
  IN IF BallotNumLeq(aState.mBalNum, m1a.balNum)
     THEN SetAct("p1b", Send(uState, m1b, a, p))
     ELSE st

DoR1b(st, p, a, m1b) ==
  LET pState == st.prop[p]
      nPState == [pState 
        EXCEPT !.sm = 
	  [pState.sm 
	    EXCEPT !.bals = 
	      (pState.sm.bals \cup [acc |-> a, bal |-> m1b.mBal])
	  ]
	]
  IN IF pState.sm.kind = "candidate"
     THEN SetAct("recv_p1b", SetProp(st, p, nPState))
     ELSE st

DoPhase2a(st, p) ==
  IF /\ st.prop[p].sm.kind = "candidate" 
     /\ \E Q \in Quorums: 
        \A a \in Q: 
	\E b \in st.prop[p].sm.bals:
	  b.acc = a
  THEN LET chosen_value == Max(BallotLeq, {b.bal : b \in st.prop[p].sm.bals}).val
           nPState == [st.prop[p] EXCEPT !.sm = [kind |-> "leader", val |-> chosen_value]]
	   nUState == SetProp(st, p, nPState)
	   value_options == IF chosen_value = None THEN Commands ELSE {chosen_value}
       IN {Broadcast(
             nUState,
             [type |-> "2a", bal |-> [bal |-> chosen_value, val |-> chosen_value]],
	     p,
	     Acceptors)
	  :v \in value_options}
  ELSE IF st.prop[p].sm.kind = "leader"
  THEN {Broadcast(
          st,
          [type |-> "2a", bal |-> [bal |-> st.prop[p].balNum, val |-> st.prop[p].sm.val]],
	  p,
	  Acceptors)}
  ELSE {st}

DoPhase2b(st, a, p, m2a) ==
  LET aState == st.acc[a]
      nAState == [aState EXCEPT !.mBalNUm = m2a.bal.bal, !.mBal = m2a.bal]
      nUState == SetAcc(st, a, nAState)
  IN IF /\ aState.mBalNum <= m2a.bal.bal
        /\ BallotLeq(aState.mBal, m2a.bal)
     THEN nUState
     ELSE st

----

(* Spec construction *)

DoPropAnytime(st, p) == {DoPhase1a(st, p)} \union DoPhase2a(st, p)

DoPropRecv(cst, p) ==
  LET msgs == RecvAbles(cst, p)
      doPropRecv(st, m, src) ==
        IF m.type = "1b"
	  THEN DoR1b(st, p, src, m)
	ELSE Assert(FALSE, [invalid |-> m])
  IN {doPropRecv(s.st, s.msg, s.src) : s \in msgs}

DoAccRecv(cst, a) ==
  LET msgs == RecvAbles(cst, a)
      doAccRecv(st, m, src) ==
        IF m.type = "1a"
	  THEN DoPhase1b(st, a, src, m)
	ELSE IF m.type = "2a"
	  THEN DoPhase2b(st, a, src, m)
	ELSE Assert(FALSE, [invalid |-> m])
  IN {doAccRecv(s.st, s.msg, s.src) : s \in msgs}

\* If there exists a quorum of acceptors with the same ballot number and value, then that could be committed
UpdateCommit(st) ==
  LET commitable(Q) ==
        LET arbA == CHOOSE a \in Q: TRUE
	    bal == st.acc[arbA].mBal
	IN IF \A a \in Q: st.acc[a].mBal = bal
	   THEN [poss |-> TRUE, val |-> bal.val]
	   ELSE [poss |-> FALSE]
      commitProbes == {commitable(Q) : Q \in Quorums}
      canCommit == {cp \in commitProbes: cp.poss}
      committed == CHOOSE v \in canCommit: TRUE
  IN IF /\ canCommit /= {} 
        /\ Assert(Cardinality(canCommit) \in {0, 1}, canCommit)
     THEN [st EXCEPT !.commit = committed.val]
     ELSE st

Normalise(st) == st
Generalise(st) == st

Next ==
  LET cst == Normalise(State)
      nextStates == 
        UNION (
          {DoPropAnytime(cst, p) : p \in Proposers} \union
	  {DoPropRecv(cst, p)    : p \in Proposers} \union
	  {DoAccRecv(cst, a)     : a \in Acceptors}
	)
  IN \E st \in nextStates: State' = Generalise(UpdateCommit(st))

Spec == Init /\ [][Next]_<< State >>

====

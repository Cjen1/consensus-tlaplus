----------------------------- MODULE VectorPaxos -----------------------------

EXTENDS TLC, Integers, Sequences, FiniteSets

----
(* Generic utils *)
Max(Leq(_,_), s) == CHOOSE v \in s: \A v1 \in s: Leq(v1, v)
Min(Leq(_,_), s) == CHOOSE v \in s: \A v1 \in s: Leq(v, v1)

Replace(F, F1) ==
  [x \in DOMAIN F |-> IF x \in DOMAIN F1 THEN F1[x] ELSE F[x]]

Range(F) == {F[x] : x \in DOMAIN F}

ProposerMapping == 
  CHOOSE F \in [Proposers -> 0..Cardinality(Proposers)]:
  \A p1,p2 \in Proposers: F[p1] \= F[p2]

BallotNumLeq(a,b) ==
  \/ a.num < b.num
  \/ a.num = b.num /\ ProposerMapping(a.prop) <= ProposerMapping(b.prop)

BallotLeq(a, b) ==
  \/ BallotNumLeq(a.b, b.b) /\ ~ BallotNumLeq(b.b, a.b)
  \/ a = b

----

(* State variables and types *)

CONSTANTS Proposers, Acceptors, Quorums, Commands, MaxChannelSize

(* proposers
 * acceptors
 * channels
 * *)

VARIABLES State

None == CHOOSE v \notin Commands: TRUE

TProposer == Proposers
TAcceptor == Acceptors
TProcess  == TProposer \union TAcceptor
TCommand  == Commands

TBallotNumber == [num : Nat, prop : Proposers]

TBallot == [bal : TBallotNumber, val : TCommand]

TMsg == [type |-> "1a", balNum : TBallotNumber] \union
        [type |-> "1b", balNum : TBallotNumber, maxBal : TBallot] \union
	[type |-> "2a", bal : TBallot]

TChans == [(TProposer \X TAcceptor) \cup (TAcceptor \X TProposer) -> [Nat -> TMsg]]

TPropSM == {[kind |-> "follower"],
                [kind |-> "candidate", bals : [acc : Acceptors, bal : Ballots]]
                [kind |-> "leader", val : Commands]
	       }

TProp == [sm : TPropSM, balNum : TBallotNumber]

TAcc == [mBalNum : TBallotNumber, mBal |-> TBallot]

TState == [ chans : TChans,
            prop  : TProp,
	    acc   : TAcc,
	    commit: TCommand
	  ]

----

Init == 
  State = [
    chans |-> [p \in Proposers \X Acceptors |-> <<>>] \union 
              [p \in Acceptors \X Proposers |-> <<>>],
    prop  |-> [p \in Proposers |-> [
                 sm |-> [kind |-> "follower"],
                 balNum |-> 0
                 ]
              ],
    acc   |-> [a \in Acceptors |-> [mBalNum |-> 0, mBal |-> [n |-> 0, v |-> None]]],
    commit |-> None
    ]

----

(* Specific utils *)

SetAcc(st, a, ap) ==
  [st EXCEPT !.acc = [st.acc EXCEPT ![a] = ap]]

SetProp(st, p, pp) ==
  [st EXCEPT !.prop = [st.prop EXCEPT ![p] = pp]]

(* Limited window reliable inorder messaging *)
SendChan(chan, m) ==
  IF Len(chan) < MaxChannelSize
  THEN chan \o << m >>
  ELSE chan

Send(st, m, s, d) ==
  [st EXCEPT !.chans = Replace(st.chans, [<<s,d>> |-> SendChan(st.chans[s,d], m)])]

Broadcast(st, m, s, D) ==
  LET updatedChans == UNION {[<<s,d>> |-> SendChan(st.chans[s,d], m)]: d \in D}
  IN [st EXCEPT !.chans = Replace(st.chans, updatedChans)]

RecvOne(st, s, d) ==
  IF Len(st.chans[s,d]) > 0
  THEN [
    poss |-> TRUE,
    msg |-> [msg |-> Head(st.chans[s,d]), src |-> s],
    st |-> [st EXCEPT !.chans = [st.chans EXCEPT ![s,d] = Tail(st.chans[s,d],m]],
    src |-> s
  ]
  ELSE [poss |-> FALSE]

RecvAbles(st, d) ==
  LET recvables == {RecvOne(st, s, d):s \in Processes}
  IN {rs \in recvables: rs.poss}

----

(* State transitions *)

DoPhase1a(st, p) ==
  LET pState == st.prop[p]
      nPState == [pState EXCEPT !.balNum = [num |-> pState.balNum.num + 1, prop |-> p], !.sm = [kind |-> "follower"]]
      nUState == SetProp(st, p, nPState)
  IN Broadcast(nUState, [type |-> "1a", balNum |-> nPState.balNum], s, Acceptors)

DoPhase1b(st, a, p, m1a) ==
  LET aState == st.acc[a]
      m1b == [type |-> "1b", balNum |-> m.balNum, maxBal |-> aState.maxBal]
      nAState == [aState EXCEPT !.mBalNum = m1a.balNum]
      uState == SetAcc(st, nAState)
  IN IF aState.mBalNum <= m1a.balNum
     THEN Send(uState, m, a, p)
     ELSE st

DoR1b(st, p, a, m1b) ==
  LET pState == st.prop[p]
      nPState == [pState EXCEPT !.sm = [pState.sm EXCEPT !.bals = !.bals \cup [acc |-> a, bal |-> m1b.maxBal]]]
  IN IF pState.sm.kind = "candidate"
     THEN SetProp(st, p, nPState)
     ELSE st

Phase2a(st, p) ==
  IF st.prop[p].sm.kind = "candidate" /\ \E Q \in Quorums: \A a \in Q: \E b \in st.prop[p].sm.bals: b.acc = a
  THEN LET chosen_value == Max(BallotLeq, {b.bal : b \in st.prop[p].sm.bals}).val
           nPState == [st.prop[p] EXCEPT !.sm = [kind |-> "leader", val |-> chosen_value]]
	   nUState == SetProp(st, nPState)
	   value_options == IF chosen_value = None THEN Commands ELSE {chosen_value}
       IN {Broadcast(
             nUState,
             [type |-> "2a", bal |-> [bal |-> chosen_value, val |-> chosen_value],
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
  IN IF /\ aState.maxBalNum <= m2a.bal.bal
        /\ BallotLeq(aState.mBal, m2a.bal)
     THEN nUState
     ELSE st

----

(* Spec construction *)

DoPropAnytime(st, p) == {DoPhase1a(st, p)} \union DoPhase2a(st, p)}

DoPropRecv(st, p) ==
  LET msgs == RecvAbles(st, p)
      doPropRecv(st, m, src) ==
        IF m.type = "1b"
	  THEN DoR1b(st, p, src, m)
	  ELSE st
  IN {doPropRecv(s.st, s.msg, s.src) : s \in msgs}

DoAccRecv(st, a) ==
  LET msgs == RecvAbles(st, a)
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
	    bal == st.acc[a].mBal
	IN IF \A a \in Q: st.acc[a].mBal = bal
	   THEN [poss |-> TRUE, val |-> bal.val]
	   ELSE [poss |-> FALSE]
      commitProbes == {commitable(Q) : Q \in Quorums}
      canCommit == {cp \in commitProbes: cp.poss}
      committed == CHOOSE v \in canCommit: TRUE
  IN IF canCommit \= {} /\ Assert(Cardinality(canCommit) \in {0, 1}, canCommit)
     THEN [st EXCEPT commit = committed]
     ELSE st

Normalise(st) == st
Generalise(st) == st

Next ==
  LET st == Normalise(State)
      nextStates == 
        UNION (
          {DoPropAnytime(st, p) : p \in Proposers} \union
	  {DoPropRecv(st, p)    : p \in Proposers} \union
	  {DoAccRecv(st, a)     : a \in Acceptors}
	)
  IN \E st \in NextStates: State' = Generalise(UpdateCommit(st))

Spec == Init /\ [][Next]_<< State >>

MaxBalNum == 
  LET bals == {State.prop[p].balNum :p \in Proposers}
  IN Max(BallotNumLeq, bals).num

TypeInvariant == State \in TState
    

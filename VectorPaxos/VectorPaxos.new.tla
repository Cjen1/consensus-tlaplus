----------------------------- MODULE VectorPaxos -----------------------------

EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS Proposers, Acceptors, Quorums, Commands, MaxChannelSize

(* proposers
 * acceptors
 * channels
 * *)

VARIABLES State

None == CHOOSE v \notin Commands: TRUE

BallotNumbers == Nat

Processes == Proposers \union Acceptors

Max(Leq(_,_), s) == CHOOSE v \in s: \A v1 \in s: Leq(v1, v)
Min(Leq(_,_), s) == CHOOSE v \in s: \A v1 \in s: Leq(v, v1)

Replace(F, F1) ==
  [x \in DOMAIN F |-> IF x \in DOMAIN F1 THEN F1[x] ELSE F[x]]

BallotLeq(a, b) ==
  \/ a.b < b.b
  \/ a.b = b.b

----

Init == State == [
  chans |-> [p \in Processes \X Processes |-> <<>>]],
  prop  |-> [p \in Proposers |-> [pstate |-> "startup", val |-> None, balNum |-> 0]],
  acc   |-> [a \in Acceptors |-> [mBalNum |-> 0, mBal |-> [n |-> 0, v |-> None]]],
  action |-> None
  ]

(* Limited window reliable inorder messaging *)
Send(st, m, s, d) == 
  IF Len(st.chans[s][d]) < MaxChannelSize
  THEN [st EXCEPT !.chans = [!.chans EXCEPT ![s,d] = Append(st.chans[s,d], m)]]
  ELSE st

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
    val |-> [msg |-> Head(st.chans[s,d]), src |-> s],
    s |-> [st EXCEPT !.chans = [st.chans EXCEPT ![s,d] = Tail(st.chans[s,d],m]]
  ]
  ELSE [poss |-> FALSE]

RecvAbles(st, d) ==
  LET recvables == {RecvOne(st, s, d):s \in Processes}
      filtRecv  == {rs \in recvables: rs.poss}
  IN {[val |-> s.val, s |-> s.s] : s \in filtRecv}

DoP1a(st, p) ==
  LET pState == st.prop[p]
      nPState == [pState EXCEPT !.balNum = pState.balNum + 1]
      broadcasted == Broadcast(st, [type |-> "1a", balNum |-> nPState.balNum], s, Acceptors)
  IN [broadcasted EXCEPT !.prop = [!.prop EXCEPT ![p] = [![p] EXCEPT balNum = nBalNum]],
                         !.action = [p1a |-> p]
       ]

Normalise(st) == st

Next ==
  LET NextStates == UNION {{Recv(val, d) : RecvAbles} : d \in Acceptors} \cup {DoP1a(State, p) : p \in Proposers}
  IN \E st \in NextStates: State' = Normalise(st)

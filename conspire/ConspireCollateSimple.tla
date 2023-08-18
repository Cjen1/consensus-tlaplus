---- MODULE ConspireCollateSimple ----

EXTENDS Sequences

\* @typeAlias: NID = Str;
\* @typeAlias: VALUE = Str;
\* @typeAlias: TERM = Int;
\* @typeAlias: State = [term : TERM, vterm : TERM, vval : Seq(VALUE)];
\* @typeAlias: Msg = [src : NID, state : State];

CONSTANTS 
  \* @type: Set(NID);
  Nodes,
  \* @type: Set(VALUE);
  Values

VARIABLES
  \* @type: NID -> State;
  local_states,
  \* @type: NID -> (NID -> State);
  remote_state_caches,
  \* @type: Set(Msg);
  msgs

\*====================
\* Utility functions
\*====================

Quorums == {Q \in SUBSET Acceptors: Cardinality(Q) = (2 * Cardinality(Acceptors)) \div 3 + 1}

Send(src,s) ==
  LET msg == [src |-> src, state |-> s] IN
  /\ msg \notin msgs

LEQ(a,b) ==
  /\ Len(a) =< Len(b)
  /\ \A i \in DOMAIN a: a[i] = b[i]

LEQState(a,b) ==
  /\ a.term <= b.term
  /\ a.vterm <= b.vterm
  /\ LEQ(a.vval, b.vval)

\* @type: (a -> x) => Set(x);
Range(S) == {S[i] : i \in DOMAIN S}
\* @type: Seq(x) => Set(x);
RangeS(S) == {S[i] : i \in DOMAIN S}

GetState(n, a) ==
  IF a = n THEN local_states[a] ELSE remote_state_caches[n][a]

AllSubSeqs(S) ==
  {SubSeq(S,1,h)  : h \in 1..Len(S)}

\*====================
\* Main functions
\*====================

ProposeExtend(n) ==
  /\ local_states[n].term = local_states[n].vterm
  /\ \E v \in Values: 
     /\ v \notin Range(local_states[n].vval)
     /\ LET new_state == [local_states[n] EXCEPT !.vval = Append(local_states[n].vval,v)] IN
        /\ msgs' = msgs \union {[src |-> n, state |-> new_state]}
        /\ local_states' = [local_states EXCEPT ![n] = new_state]
  /\ UNCHANGED remote_state_caches

RecvUpdate(n) ==
  \E m \in msgs:
  \* Update is newer than cached one
  /\ m.src \= n
  /\ LEQState(remote_state_caches[n][m.src], m.state)
  /\ remote_state_caches' = [remote_state_caches EXCEPT
       ![n] = [remote_state_caches[n] EXCEPT
         ![m.src] = m.state]]
  /\ LET 
     new_state == 
       (* should just overwrite if newer (vterm & value) *)
       IF \/ m.state.vterm > local_states[n].term
          \/ /\ m.state.vterm = local_states[n].term
             /\ \/ m.state.vterm > local_states[n].vterm
                \/ /\ m.state.vterm = local_states[n].vterm
                   /\ LEQ(local_states[n].vval, m.state.vval)
       THEN m.state
       ELSE 
       (* same vterm but conflict value *)
       IF /\ m.state.vterm = local_states[n].term
          /\ m.state.vterm = local_states[n].vterm
          /\ NoRel(m.state.vval, local_states[n].vval)
       THEN  [local_states[n] EXCEPT !.term = local_states[n] + 1]
       ELSE local_states[n] 
     IN
     /\ local_states' = [local_states EXCEPT ![n] = new_state]
     /\ msg' = msg \union {[src |-> n, new_state]}

ProposeRecover(n) ==
  LET 
    states == {GetState(n,a): a \in Acceptors}
    max_term == (CHOOSE s \in states: \A t \in states: t.term <= s.term).term
    tstates == {v \in states: v.term = max_term}
    max_vterm == (CHOOSE s \in tstates: \A t \in tstates: t.vterm <= s.vterm).vterm
    votes == {v \in tstates: v.vterm = max_vterm}
    VotesForV(n, a, max_term, max_vterm, v) ==
      /\ GetState(n,a).term = max_term
      /\ GetState(n,a).vterm = max_vterm
      /\ LEQ(v, GetState(n,a).vval)
    VotedIn(n, a, max_term) == GetState(n,a).term = max_term
    PossiblyCommittable(v) ==
      \E Q \in Quorums:
      \A a \in Q:
      \/ ~ VotedIn(n, a, max_term)
      \/ VotesForV(n, a, max_term, max_vterm, v)
    all_values == UNION {AllSubSeqs(v.vval) : v \in votes}
    poss_commit_values == {v \in all_values: PossiblyCommittable(v)}
  IN 
  (* Sufficient votes *)
  /\ \E Q \in Quorums:
     \A a \in Q: GetState(n,a).term = max_term
  /\ \E v \in all_values:
     LET new_state == [term |-> max_term, vterm |-> max_term, vval |-> v] IN
     /\ \A ov \in poss_commit_values: LEQ(ov, v)
     /\ local_states' = [local_states EXCEPT ![n] = new_state ]
     /\ Send(n, new_state)
  /\ UNCHANGED remote_state_caches
     
\*====================
\* Main functions
\*====================

InitState == [term |-> 0, vterm |-> 0, vval |-> <<>>]

Init ==
  /\ local_states = [n \in Nodes |-> InitState]
  /\ remote_state_caches = [n \in Nodes |-> [r \in Nodes |-> InitState]]
  /\ msgs = {}

Next ==
  \E n \in Nodes:
  \/ ProposeExtend(n)
  \/ RecvUpdate(n)
  \/ ProposeRecover(n)

Spec == Init /\ [][Next]_<<local_states, remote_state_caches, msgs>>

Committable(v, t) ==
  \E Q \in Quorums:
  \A a \in Q: 
  \E m \in msgs:
  /\ m.src = a
  /\ m.state.vterm = t
  /\ LEQ(v, m.state.vval)

UsedValues == \E v \in 

Serialised ==
  

====

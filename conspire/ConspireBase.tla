---- MODULE ConspireBase ----

EXTENDS FiniteSets, Integers

\* @typeAlias: nid = Str;
\* @typeAlias: value = Str;
\* @typeAlias: term = Int;
\* @typeAlias: reqMsg = {term : $term, val : $value};
\* @typeAlias: repMsg = {src : $nid, state : $state};
\* @typeAlias: state = {term : $term, vterm : $term, vval : $value};
CONSPIRE_BASE_ALIAS == TRUE

CONSTANTS
  \* @type: Set($nid);
  Nodes,
  \* @type: Set($value);
  Values,
  \* @type: $value;
  None

VARIABLES
  \* @type: $nid -> $state;
  local_states,
  \* @type: Set($reqMsg);
  req_msgs,
  \* @type: Set($repMsg);
  rep_msgs

ASSUME ~None \in Values

Quorums == {Q \in SUBSET Nodes: Cardinality(Q) = (2 * Cardinality(Nodes)) \div 3 + 1}

\* @type: ($nid, $state) => Bool;
Send(src, s) ==
  LET msg == [src |-> src, state |-> s] IN
  /\  ~ msg \in rep_msgs
  /\ rep_msgs' = rep_msgs \union {msg}

\* @type: Set($term);
UsedTerms == 
  UNION ({{local_states[n].term, local_states[n].vterm}: n \in DOMAIN local_states} \union 
         {{m.term}: m \in req_msgs} \union
         {{m.state.term, m.state.vterm}: m \in rep_msgs})

\*====================
\* Main functions
\*====================

Init ==
  /\ local_states = [n \in Nodes |-> [term |-> 0, vterm |-> -1, vval |-> None]]
  /\ req_msgs = {[term |-> 0, val |-> v] : v \in Values}
  /\ rep_msgs = {}

Reply(n) ==
  \E m \in req_msgs:
  /\ m.term >= local_states[n].term
  /\ \/ m.term > local_states[n].vterm  
     \/ m.term = local_states[n].vterm /\ local_states[n].vval = None
  /\ LET new_state == [term |-> m.term, vterm |-> m.term, vval |-> m.val] IN
     /\ local_states' = [local_states EXCEPT ![n] = new_state]
     /\ Send(n, new_state)
  /\ UNCHANGED req_msgs

IncrTerm(n) ==
  LET new_state == [local_states[n] EXCEPT !.term = local_states[n].term + 1] IN
  /\ new_state.term < 10
  /\ local_states' = [local_states EXCEPT ![n] = new_state]
  /\ Send(n, new_state)
  /\ UNCHANGED req_msgs

Propose ==
  \E t \in UsedTerms:
  \E Qr \in Quorums:
  \* Valid votes
  \E S \in SUBSET {m \in rep_msgs: /\ m.state.term = t
                            /\ m.src \in Qr}:
     LET max_vterm == (CHOOSE m \in S: \A m1 \in S: m1.state.vterm <= m.state.vterm).state.vterm
         max_vterm_msgs == {m \in S: m.state.vterm = max_vterm}
         \* @type: ($value) => Bool;
         PossiblyCommittable(v) ==
           \E Qw \in Quorums:
           \A n \in Qw:
           \* Voted for v
           \/ \E m \in max_vterm_msgs: 
              /\ m.src = n
              /\ m.state.vval = v
           \* Did not vote
           \/ ~\E m \in S: m.src = n
         max_vterm_vals == {m.state.vval : m \in max_vterm_msgs}
         ChoosableVals == {v \in max_vterm_vals: PossiblyCommittable(v)}
     IN
     /\ \A n \in Qr: \E m \in S: m.src = n
     /\ \E v \in Values:
        LET msg == [term |-> t, val |-> v] IN
        \* Inductive base case
        /\ \A lb \in ChoosableVals: lb = None \/ lb = v
        \* Inductive case
        /\ \E lb \in max_vterm_vals: lb = v
        /\ ~ msg \in req_msgs
        /\ req_msgs' = req_msgs \union {msg}
        /\ UNCHANGED << local_states, rep_msgs >>
        
Next ==
  \/ Propose
  \/ \E n \in Nodes: Reply(n) \/ IncrTerm(n)

Spec == Init /\ [][Next]_<<local_states, req_msgs, rep_msgs>>

\*====================
\* Invariants
\*====================

\* @type: ($term, $value) => Bool;
Committable(t,v) ==
  \E Q \in Quorums:
  \A n \in Q:
  \E m \in rep_msgs:
  /\ m.src = n
  /\ m.state.vterm = t
  /\ m.state.vval = v

Safety ==
  LET CanCommit == {v \in Values: \E t \in UsedTerms: Committable(t,v)} IN
  \A v1, v2 \in CanCommit: v1 = v2

====

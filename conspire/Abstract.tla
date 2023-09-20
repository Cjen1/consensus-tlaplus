---- MODULE Abstract ----

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
  proposals,
  \* @type: Set($repMsg);
  states

ASSUME ~None \in Values

Quorums == {Q \in SUBSET Nodes: Cardinality(Q) = (2 * Cardinality(Nodes)) \div 3 + 1}

\* @type: Set($term);
UsedTerms == 
  UNION ({{local_states[n].term, local_states[n].vterm}: n \in DOMAIN local_states} \union 
         {{m.term}: m \in proposals} \union
         {{m.state.term, m.state.vterm}: m \in states})

\*====================
\* Main functions
\*====================

Init ==
  /\ local_states = [n \in Nodes |-> [term |-> 0, vterm |-> -1, vval |-> None]]
  /\ proposals = {[term |-> 0, val |-> v] : v \in Values}
  /\ states = {}

Vote(n) ==
  \E m \in proposals:
  /\ m.term >= local_states[n].term
  /\ \/ m.term > local_states[n].vterm  
     \/ m.term = local_states[n].vterm /\ local_states[n].vval = None
  /\ local_states' = [local_states EXCEPT ![n] =
       [term |-> m.term, vterm |-> m.term, vval |-> m.val]]

IncrTerm(n) == local_states' = [local_states EXCEPT ![n] = 
                 [local_states[n] EXCEPT !.term = local_states[n].term + 1]]

BroadcastState(n) ==
  LET msg == [src |-> n, state |-> local_states[n]] IN
  /\  ~ msg \in states
  /\ states' = states \union {msg}

Propose ==
  \E t \in UsedTerms:
  \E Qr \in Quorums:
  \* Valid votes
  \E S \in SUBSET {m \in states: /\ m.state.term = t
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
        /\ \E lb \in max_vterm_vals: lb = None \/ lb = v
        /\ ~ msg \in proposals
        /\ proposals' = proposals \union {msg}
        
Next ==
  \/ \E n \in Nodes: \/ /\ \/ Vote(n) 
                           \/ IncrTerm(n)
                        /\ UNCHANGED << states, proposals >>
                     \/ /\ BroadcastState(n)
                        /\ UNCHANGED << local_states, proposals>>
  \/ Propose /\ UNCHANGED << local_states, states >>

Spec == Init /\ [][Next]_<<local_states, proposals, states>>

\*====================
\* Invariants
\*====================

\* @type: ($term, $value) => Bool;
Committable(t,v) ==
  \E Q \in Quorums:
  \A n \in Q:
  \E m \in states:
  /\ m.src = n
  /\ m.state.vterm = t
  /\ m.state.vval = v

Safety ==
  LET CanCommit == {v \in Values: \E t \in UsedTerms: Committable(t,v)} IN
  \A v1, v2 \in CanCommit: v1 = v2

====

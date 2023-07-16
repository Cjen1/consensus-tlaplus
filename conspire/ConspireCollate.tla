----------------------- MODULE ConspireCollate -----------------------------
(* This is an optimised version of the Conspire spec which co-locates acceptors and proposers.
 * This allows for simplified and deduplicated synchronisation of logs between nodes (a la automerge / git)
 * Specifically it works from the observation that if the message is always delivered locally,
 *  the vterm and vval will generally equal the proposer's.
 * Additionally any vterm and vval can be used to generated sync messages for that vterm, effectively resetting the local proposer.
 * Thus we can ignore the proposer and just use the vterm and vval of the acceptor.

 * Additionally we can also cache the latest message from other nodes locally however 
 * I do not believe reliable in-order delivery is required, except for a rational sync protocol.
 
 * tl;dr This is a consensus protocol where nodes replicate their local log to other nodes, which then use that log to reach consensus.
 * *)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS 
  \* @type: Set(ACC);
  Acceptors, 
  \* @type: Set(VALUE);
  PropValues

VARIABLES
  \* @type: ACC -> STATE;
  node_state,
  \* @type: ACC -> (ACC -> STATE);
  state_cache,
  \*       host -> dst
  \* @type: ACC -> (ACC -> Int);
  msg_hwm,
  \*        dst -> src
  \* @type: ACC -> (ACC -> Seq(STATE));
  msg

vars == << node_state, state_cache, msg_hwm, msg >>

\* @typeAlias: COMMITTABLE_VALUE = Seq(Set(VALUE));
\* @typeAlias: TERM = Int;
\* @typeAlias: STATE = [vterm : TERM, vval: COMMITTABLE_VALUE, term: TERM];

\*====================
\* Utility functions
\*====================

\* @type: (a -> x) => Set(x);
Range(S) == {S[i] : i \in DOMAIN S}
\* @type: Seq(x) => Set(x);
RangeS(S) == {S[i] : i \in DOMAIN S}

\*----------
\* Spec utility funcs 
\*----------
Quorums == {Q \in SUBSET Acceptors: Cardinality(Q) = (2 * Cardinality(Acceptors)) \div 3 + 1}

LEQ(a,b) ==
  /\ Len(a) =< Len(b)
  /\ \A i \in DOMAIN a: a[i] = b[i]

Send(src,dst,m) ==
  LET rel == msg[dst][src] IN
  IF m \in RangeS(rel) \/ dst=src THEN rel ELSE (rel \o << m >>)

UsedValues ==
  {node_state[a].vval : a \in Acceptors} \union
  {state_cache[a][rem].vval : a,rem \in Acceptors} \union
  {s.vval : s \in UNION {RangeS(msg[dst][src]) : dst,src \in Acceptors}}

UsedVTerms ==
  {node_state[a].vterm : a \in Acceptors} \union
  {state_cache[a][rem].vterm : a,rem \in Acceptors} \union
  {s.vterm : s \in UNION {RangeS(msg[dst][src]) : dst,src \in Acceptors}}

UsedTerms == UsedVTerms \union
  {node_state[a].term : a \in Acceptors} \union
  {state_cache[a][rem].term : a,rem \in Acceptors} \union
  {s.term : s \in UNION {RangeS(msg[dst][src]) : dst,src \in Acceptors}}

\*====================
\* Main functions
\*====================

\* standard acceptor, take vote and update local state
\* @type: (STATE, STATE) => STATE;
DoAcceptorResponse(state, m) ==
  LET newer_term == m.vterm > state.term
      should_update == /\ m.vterm >= state.term
                       /\ \/ m.vterm > state.vterm
                          \/ m.vterm = state.vterm /\ LEQ(state.vval, m.vval)
      must_increment == /\ m.vterm = state.term
                        /\ m.vterm = state.vterm /\ ~LEQ(state.vval, m.vval)
      new_term == IF newer_term 
                  THEN m.vterm 
                  ELSE IF must_increment
                       THEN state.term + 1
                       ELSE state.term
      new_vterm == IF should_update THEN m.vterm ELSE state.vterm
      new_vval  == IF should_update THEN m.vval ELSE state.vval
  IN [term |-> new_term, vterm |-> new_vterm, vval |-> new_vval]

\* If sufficient votes and need to recover, then do recovery
\* @type: (ACC, STATE, ACC -> STATE) => STATE;
DoConflictRecovery(a, local_state, local_state_cache) == 
  LET 
      \* collate states for easier analysis
      states == {
         [src |-> acc,
          s   |-> IF acc = a THEN local_state ELSE local_state_cache[acc]]
          : acc \in Acceptors
          }
      max_term == (CHOOSE s \in states: \A s1 \in states: s1.s.term <= s.s.term).s.term
      \* relevant votes for conflict recovery
      vstates == {state \in states: state.s.term = max_term}
      max_vterm == (CHOOSE s \in states: \A s1 \in states: s1.s.vterm <= s.s.vterm).s.vterm
      \* votes which are sufficiently new
      M == {s \in states: s.s.vterm = max_vterm}
      \* there exists a quorum which could have committed v
      O4(v) == 
        \E Q \in Quorums:
        \A a1 \in Q:
        \* a voted for larger value
        \/ \E s \in M: /\ s.src = a1
                       /\ LEQ(v, s.s.vval)
        \* a did not vote => we assume it voted for this one
        \/ ~ \E m \in vstates: m.src = a1
      used_vals == {v \in UsedValues: \E s \in vstates: LEQ(v, s.s.vval)}
      o4_vals == {v \in used_vals: O4(v)}
      \* Values which are greater than every committed value
      lbs == {
        v \in used_vals:
        /\ \A l \in o4_vals: LEQ(l, v) \* Safety for commit in prev term
        /\ \E s \in M: LEQ(s.s.vval, v)\* Inductive safety
      }
      \* For every index take union over values. Committed values will only have one option
      \* This should help to avoid retries and improve performance
      max_lb == CHOOSE lb \in lbs: \A l1 \in lbs: Len(l1) <= Len(lb)
      merged_lbs == [i \in DOMAIN max_lb |->
        UNION {IF i \in DOMAIN lb THEN lb[i] ELSE {} : lb \in lbs}
      ]
      recovered_state ==
        [term |-> max_term, vterm |-> max_term, vval |-> merged_lbs]
    \* The above is lazily evaluated, so only if sufficient votes actually calculate the recovered state
  IN IF /\ \E Q \in Quorums: \A acc \in Q: \E s \in vstates: s.src = acc
        /\ max_term > local_state.vterm
     THEN recovered_state
     ELSE local_state

RecvUpdate(a) ==
  \E ar \in Acceptors:
    LET idx == msg_hwm[a][ar] + 1
        m == msg[a][ar][idx]
        \* split updates to allow single action update
        new_state_cache == [state_cache[a] EXCEPT ![ar] = m] 
        post_acc_state == DoAcceptorResponse(node_state[a], m)
        new_state == DoConflictRecovery(a, post_acc_state, new_state_cache)
    IN
    /\ msg_hwm[a][ar] + 1 \in DOMAIN msg[a][ar]
    /\ msg_hwm' = [msg_hwm EXCEPT ![a][ar] = msg_hwm[a][ar] + 1] 
    /\ node_state' = [node_state EXCEPT ![a] = new_state]
    /\ state_cache' = [state_cache EXCEPT ![a] = new_state_cache]
    /\ msg' = [msg EXCEPT ![ar] = [msg[ar] EXCEPT ![a] = Send(a,ar,new_state)]]

AddValue(a) ==
  \* locally not conflicted, this check can be ignored if we disambiguate between strong and eventual replication
  /\ node_state[a].vterm = node_state[a].term
  /\ \E v \in PropValues:
     LET new_state == [ node_state[a] EXCEPT !.vval = node_state[a].vval \o <<{v}>>] IN
     /\ v \notin UNION RangeS(node_state[a].vval)
     /\ node_state' = [node_state EXCEPT ![a] = new_state]
     /\ msg' = [dst \in DOMAIN msg |->
                [msg[dst] EXCEPT ![a] = Send(a,dst,new_state)]]
  /\ UNCHANGED <<msg_hwm, state_cache>>

Init == 
  LET empty_state == [term |-> 0,vterm |-> 0, vval |-> <<>>] IN
  /\ node_state =  [a \in Acceptors |-> empty_state]
  /\ state_cache = [a \in Acceptors |-> [src \in Acceptors |-> empty_state]]
  /\ msg_hwm =     [host \in Acceptors |-> [msg_src \in Acceptors |-> 0 ]]
  /\ msg =         [dst \in Acceptors  |-> [src \in Acceptors |-> <<>> ]]

\* A ballot can be committed in b if there exists a quorum of responses for larger values
\* This can be extended to the consecutive ballots thingy-mabob
Committable(v, b) ==
  \E Q \in Quorums:
  \A a \in Q: 
  \E dst \in Acceptors: 
  \E m \in RangeS(msg[dst][a]):
    /\ m.vterm = b
    /\ LEQ(v, m.vval)

Next ==
  \E a \in Acceptors: 
  \/ RecvUpdate(a)
  \/ AddValue(a)

Spec == /\ Init 
        /\ [][Next]_vars

\* Since there exists some total order over all committed values, any logs used to commit values will be some prefix of that 'uber log'
\* Thus we can check that if two values are committable then one is a prefix of the other.
Serialised ==
  \A v1, v2 \in UsedValues:
    /\ (/\ \E b \in UsedTerms: Committable(v1, b)
        /\ \E b \in UsedTerms: Committable(v2, b)
       ) => \/ LEQ(v1, v2)
            \/ LEQ(v2, v1)

Inv == Serialised 

Symmetry == Permutations(Acceptors) \union Permutations(PropValues)

\* tests to check for deadlock not due to everything being committed
AllCompleteStutter ==
   /\ \E b \in UsedTerms: \E v \in UsedValues: UNION Range(v) = PropValues /\ Committable(v,b)
   /\ UNCHANGED vars
Next_deadlock_free == Next \/ AllCompleteStutter
Spec_deadlock_free == Init /\ [][Next_deadlock_free]_vars

========

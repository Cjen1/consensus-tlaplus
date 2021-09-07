----------------------------- MODULE MultiPaxos -----------------------------

EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS Ballots, Acceptors, Values, Quorums

VARIABLES   msgs,
            acc,
            prop

\* a =< b
Prefix(a,b) ==
  /\ Len(a) =< Len(b)
  /\ \A i \in DOMAIN a: a[i] = b[i]

Range(s) == {s[i] : i \in DOMAIN s}

Max(Leq(_,_), s) == CHOOSE v \in s: \A v1 \in s: Leq(v1, v)
Min(Leq(_,_), s) == CHOOSE v \in s: \A v1 \in s: Leq(v, v1)

AllSeqFromSet(S) ==
  LET unique(f) == \A i,j \in DOMAIN f: i /= j => f[i] /= f[j]
      subseq(c) == {seq \in [1..c -> S]: unique(seq)}
  IN
  UNION {subseq(c): c \in 0..Cardinality(S)}

PossibleValues == AllSeqFromSet(Values)

Messages ==      [type : {"1a"}, bal : Ballots]
            \cup [type : {"1b"}, bal : Ballots, 
                    maxVBal : Ballots \cup {-1}, maxVal : PossibleValues,
                    acc : Acceptors]
            \cup [type : {"2a"}, bal : Ballots, val : PossibleValues]
            \cup [type : {"2b"}, bal : Ballots, val : PossibleValues, acc : Acceptors]

ProposerState == [val : PossibleValues,
                  valSelect : {TRUE, FALSE},
		  committed : PossibleValues,
		  hasCommitted : {TRUE,FALSE}]

AcceptorState == [maxBal : Ballots \cup {-1},
                  maxVBal: Ballots \cup {-1},
                  maxVal : PossibleValues]


TypeInvariant == /\ msgs \in SUBSET Messages
                 /\ acc \in [Acceptors -> AcceptorState]
                 /\ \A a \in Acceptors : acc[a].maxBal >= acc[a].maxVBal
                 /\ prop \in [Ballots -> ProposerState]

vars == <<msgs, acc, prop>>

-----------------------------------------------------------------------------

Init == /\ msgs = {}
        /\ acc  = [a \in Acceptors |-> 
                    [maxVBal |-> -1, maxBal |-> -1, maxVal |-> << >> ]]
        /\ prop = [b \in Ballots |-> [val |-> << >>, valSelect |-> FALSE, committed |-> <<>>, hasCommitted |-> FALSE]]

Send(m) == msgs' = msgs \cup {m}

Phase1a(b) == 
  /\ ~\E m \in msgs: m.type = "1a" /\ m.bal = b
  /\ Send ([type |-> "1a", bal |-> b])
  /\ UNCHANGED << acc, prop >>

Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.bal > acc[a].maxBal
    /\ Send([type |-> "1b", acc |-> a, 
             bal |-> m.bal, maxVBal |-> acc[a].maxVBal, maxVal |-> acc[a].maxVal])
    /\ acc' = [acc EXCEPT ![a] = [acc[a] EXCEPT !.maxBal = m.bal]]
    /\ UNCHANGED << prop >>

ValueSelect(b) ==
  /\ ~ prop[b].valSelect
  /\ \E Q \in Quorums, S \in SUBSET {m \in msgs: (m.type = "1b") /\ (m.bal = b)}:
       /\ \A a \in Q: \E m \in S: m.acc = a
       /\ LET maxBalNum == Max(LAMBDA x,y: x <= y, {m.maxVBal: m \in S})
              maxValMsg == Max(LAMBDA x,y: Prefix(x.maxVal, y.maxVal), {m \in S: m.maxVBal = maxBalNum})
          IN  /\ prop' = [prop EXCEPT ![b] = 
	                          [prop[b] EXCEPT !.val = maxValMsg.maxVal, !.valSelect = TRUE]]
	      /\ UNCHANGED << acc, msgs >>

Phase2a(b) ==
  /\ prop[b].valSelect
  /\ \E v \in {<<>>} \cup {<<v>> : v \in Values \ Range(prop[b].val)}:
        LET val == prop[b].val \o v
            msg == [type |-> "2a", bal |-> b, val |-> val]
        IN 
        /\ ~\E m \in msgs: m.type = "2a" /\ m.bal = b /\ m.val = val
        /\ Send(msg)
        /\ prop' = [prop EXCEPT ![b] = [prop[b] EXCEPT !.val = val]]
  /\ UNCHANGED << acc >>

Phase2b(a) ==
  /\ \E m \in msgs :
      /\ m.type = "2a"
      /\ \/ m.bal > acc[a].maxBal
         \/ /\ m.bal = acc[a].maxBal
            /\ Prefix(acc[a].maxVal, m.val)
      /\ Send([type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a])
      /\ acc' = [acc EXCEPT ![a] = [maxBal |-> m.bal, maxVBal |-> m.bal, maxVal |-> m.val]]
  /\ UNCHANGED << prop >>

Commit(b) ==
  \E Q \in Quorums: 
  \E S \in SUBSET {m \in msgs: /\ m.type = "2b" 
                               /\ m.bal = b 
       		               /\ m.acc \in Q}:
     /\ \A a \in Q: \E m \in S: m.acc = a
     /\ LET val == Min(Prefix, {m.val: m \in S})
        IN /\ Prefix(prop[b].committed, val)
           /\ \A m \in S: \A m1 \in S \ {m}: m.acc /= m1.acc
           /\ prop' = [prop EXCEPT ![b] = [prop[b] EXCEPT !.committed = val, !.hasCommitted = TRUE]]
           /\ UNCHANGED << msgs, acc >>

Next == \/ \E b \in Ballots   : Phase1a(b) \/ ValueSelect(b) \/ Phase2a(b) \/ Commit(b)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

InterBalConsistency ==
  \A b1, b2 \in Ballots: 
  LET v1 == prop[b1].committed
      v2 == prop[b2].committed
  IN (b1 < b2 /\ prop[b1].hasCommitted /\ prop[b2].hasCommitted) => Prefix(v1, v2)

IntraBalConsistency ==
  \A b \in Ballots: Prefix(prop[b].committed, prop'[b].committed)
IntraBalConsistency_property ==
  [] [IntraBalConsistency]_prop

=============================================================================

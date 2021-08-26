----------------------------- MODULE MultiPaxos -----------------------------

EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS Ballots, Acceptors, Values, Quorums

VARIABLES   msgs,
            acc,
            prop,
            commits

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

ProposerState == [val : PossibleValues]

AcceptorState == [maxBal : Ballots \cup {-1},
                  maxVBal: Ballots \cup {-1},
                  maxVal : PossibleValues]

TypeInvariant == /\ msgs \in SUBSET Messages
                 /\ acc \in [Acceptors -> AcceptorState]
                 /\ \A a \in Acceptors : acc[a].maxBal >= acc[a].maxVBal
                 /\ prop \in [Ballots -> ProposerState]
                 /\ \A v \in Range(commits) : v \in [bal : Ballots, val : PossibleValues]

vars == <<msgs, acc, prop, commits>>

-----------------------------------------------------------------------------

Init == /\ msgs = {}
        /\ acc = [a \in Acceptors |-> 
                   [maxVBal |-> -1, maxBal |-> -1, maxVal |-> << >> ]]
        /\ prop = [b \in Ballots |-> [val |-> << >>]]
        /\ commits = << >>

Send(m) == msgs' = msgs \cup {m}

Phase1a(b) == 
  /\ ~\E m \in msgs: m.type = "1a" /\ m.bal = b
  /\ Send ([type |-> "1a", bal |-> b])
  /\ UNCHANGED << acc, prop, commits >>

Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.bal > acc[a].maxBal
    /\ Send([type |-> "1b", acc |-> a, 
             bal |-> m.bal, maxVBal |-> acc[a].maxVBal, maxVal |-> acc[a].maxVal])
    /\ acc' = [acc EXCEPT ![a] = [acc[a] EXCEPT !.maxBal = m.bal]]
    /\ UNCHANGED << prop, commits >>

QuorumExists(s, b, type) ==
  \E Q \in Quorums:
    \A a \in Q : \E m \in s : (m.type = type) /\ m.acc = a /\ (m.bal = b)

ValueSelect(b) ==
  LET ms == {m \in msgs : m.type = "1b" /\ m.bal = b}
      maxBalNum == Max(LAMBDA x,y: x <= y, {m.maxVBal: m \in ms})
      maxValMsg == Max(LAMBDA x,y: Prefix(x.maxVal, y.maxVal), {m \in ms: m.maxVBal = maxBalNum})
  IN maxValMsg.maxVal

Phase2a(b) ==
  /\ QuorumExists(msgs, b, "1b")
  /\ LET prefix == IF \E m \in msgs:
                        /\ m.type = "2a"
			/\ m.bal = b
		   THEN prop[b].val ELSE ValueSelect(b)
         postfixOptions == {<<>>} \cup {<<v>> : v \in Values \ Range(prefix)}
     IN \E v \in postfixOptions:
          LET val == prefix \o v
              msg == [type |-> "2a", bal |-> b, val |-> val]
          IN 
          /\ ~\E m \in msgs: m.type = "2a" /\ m.bal = b /\ m.val = val
          /\ Send(msg)
          /\ prop' = [prop EXCEPT ![b] = [val |-> val]]
  /\ UNCHANGED << acc, commits >>

Phase2b(a) ==
  /\ \E m \in msgs :
      /\ m.type = "2a"
      /\ m.bal >= acc[a].maxBal
      /\ Prefix(acc[a].maxVal, m.val)
      /\ Send([type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a])
      /\ acc' = [acc EXCEPT ![a] = [maxBal |-> m.bal, maxVBal |-> m.bal, maxVal |-> m.val]]
  /\ UNCHANGED << prop, commits >>

\* Commit the max value that has a quorum of responses which extend it
Commit(b) ==
  LET quorumExists(v) == \E q \in Quorums:
                         \A a \in q:
			 \E m \in msgs: 
			   /\ m.type = "2b" 
			   /\ m.bal = b 
			   /\ m.acc = a
			   /\ Prefix(v, m.val)
      commitable == {v \in PossibleValues: quorumExists(v)}
  IN \E v \in commitable:
       LET commit == [bal |-> b, val |-> v]
       IN
       /\ \A v1 \in commitable: Prefix(v1, v)
       /\ ~ commit \in Range(commits)
       /\ commits' = commits \o << commit >>
       /\ UNCHANGED << msgs, acc, prop >>

Next == \/ \E b \in Ballots   : Phase1a(b) \/ Phase2a(b) \/ Commit(b)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

Consistency ==
  \A i, j \in DOMAIN(commits):
    /\ i < j
    /\ commits[i].bal <= commits[j].bal
    => Prefix(commits[i].val, commits[j].val)

=============================================================================

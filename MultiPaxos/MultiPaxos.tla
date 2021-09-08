----------------------------- MODULE MultiPaxos -----------------------------

EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS BallotNumbers, Acceptors, Values, Quorums

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

BallotLeq(a, b) ==
  \/ a.bal < b.bal
  \/ a.bal = b.bal /\ Prefix(a.val, b.val)

PossibleBallots == [bal : BallotNumbers \cup {-1}, val : PossibleValues]

Messages ==      [type : {"1a"}, balNum : BallotNumbers]
            \cup [type : {"1b"}, acc : Acceptors, balNum : BallotNumbers, maxBal : PossibleBallots]
            \cup [type : {"2a"}, bal : PossibleBallots]
            \cup [type : {"2b"}, acc : Acceptors, bal : PossibleBallots]

ProposerState == [val : PossibleValues,
                  valSelect : {TRUE, FALSE},
		  committed : PossibleValues,
		  hasCommitted : {TRUE,FALSE}]

AcceptorState == [maxBalNum : BallotNumbers \cup {-1}, maxBal : PossibleBallots]

TypeInvariant == /\ msgs \in SUBSET Messages
                 /\ acc \in [Acceptors -> AcceptorState]
                 /\ prop \in [BallotNumbers -> ProposerState]

vars == <<msgs, acc, prop>>

-----------------------------------------------------------------------------

Init == /\ msgs = {}
        /\ acc  = [a \in Acceptors |-> [maxBalNum |-> -1, maxBal |-> [bal |-> -1, val |-> <<>>]]]
        /\ prop = [b \in BallotNumbers |-> [val |-> << >>, valSelect |-> FALSE, committed |-> <<>>, hasCommitted |-> FALSE]]

Send(m) == msgs' = msgs \cup {m}

Phase1a(b) == 
  /\ ~\E m \in msgs: m.type = "1a" /\ m.balNum = b
  /\ Send ([type |-> "1a", balNum |-> b])
  /\ UNCHANGED << acc, prop >>

Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.balNum > acc[a].maxBalNum
    /\ acc' = [acc EXCEPT ![a] = [acc[a] EXCEPT !.maxBalNum = m.balNum]]
    /\ Send([type |-> "1b", balNum |-> m.balNum, acc |-> a, maxBal |-> acc[a].maxBal])
    /\ UNCHANGED << prop >>

ValueSelect(b) ==
  /\ ~ prop[b].valSelect
  /\ \E Q \in Quorums, S \in SUBSET {m \in msgs: (m.type = "1b") /\ (m.balNum = b)}:
       /\ \A a \in Q: \E m \in S: m.acc = a
       /\ LET maxBal == Max(BallotLeq, {m.maxBal: m \in S})
          IN  /\ prop' = [prop EXCEPT ![b] = 
	                          [prop[b] EXCEPT !.val = maxBal.val, !.valSelect = TRUE]]
	      /\ UNCHANGED << acc, msgs >>

Phase2a(b) ==
  /\ prop[b].valSelect
  /\ \E v \in {<<>>} \cup {<<v>> : v \in Values \ Range(prop[b].val)}:
        LET bal == 
	  [bal |-> b, 
	   val |-> prop[b].val \o v]
        IN /\ Send([type |-> "2a", bal |-> bal])
           /\ prop' = [prop EXCEPT ![b] = [prop[b] EXCEPT !.val = bal.val]]
  /\ UNCHANGED << acc >>

Phase2b(a) ==
  /\ \E m \in msgs :
      /\ m.type = "2a"
      /\ m.bal.bal >= acc[a].maxBalNum
      /\ BallotLeq(acc[a].maxBal, m.bal)
      /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal])
      /\ acc' = [acc EXCEPT ![a] = [maxBalNum |-> m.bal.bal, maxBal |-> m.bal]]
  /\ UNCHANGED << prop >>

Commit(b) ==
  \E Q \in Quorums: 
  \E S \in SUBSET {m \in msgs: /\ m.type = "2b" 
                               /\ m.bal.bal = b 
       		               /\ m.acc \in Q}:
     /\ \A a \in Q: \E m \in S: m.acc = a
     /\ LET val == (Min(BallotLeq, {m.bal: m \in S})).val
        IN /\ Prefix(prop[b].committed, val)
           /\ \A m \in S: \A m1 \in S \ {m}: m.acc /= m1.acc
           /\ prop' = [prop EXCEPT ![b] = [prop[b] EXCEPT !.committed = val, !.hasCommitted = TRUE]]
           /\ UNCHANGED << msgs, acc >>

Next == \/ \E b \in BallotNumbers   : Phase1a(b) \/ ValueSelect(b) \/ Phase2a(b) \/ Commit(b)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
BetweenBallotConsistency ==
  \A b1, b2 \in BallotNumbers: 
  LET v1 == prop[b1].committed
      v2 == prop[b2].committed
  IN (b1 < b2 /\ prop[b1].hasCommitted /\ prop[b2].hasCommitted) => Prefix(v1, v2)

InsideBallotConsistency ==
  \A b \in BallotNumbers: Prefix(prop[b].committed, prop'[b].committed)
=============================================================================

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

ProposerState == [val : PossibleValues, valSelect : {TRUE, FALSE}]

AcceptorState == [maxBalNum : BallotNumbers \cup {-1}, maxBal : PossibleBallots]

TypeInvariant == /\ msgs \in SUBSET Messages
                 /\ acc \in [Acceptors -> AcceptorState]
                 /\ prop \in [BallotNumbers -> ProposerState]

vars == <<msgs, acc, prop>>

-----------------------------------------------------------------------------

Init == /\ msgs = {}
        /\ acc  = [a \in Acceptors |-> [maxBalNum |-> -1, maxBal |-> [bal |-> -1, val |-> <<>>]]]
        /\ prop = [b \in BallotNumbers |-> [val |-> << >>, valSelect |-> FALSE]]

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

Next == \/ \E b \in BallotNumbers   : Phase1a(b) \/ ValueSelect(b) \/ Phase2a(b)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
PossDecided(i, v) == 
  \E Q \in Quorums, b \in BallotNumbers:
     \A a \in Q: \E m \in msgs: 
        /\ m.type = "2b" 
	/\ m.acc = a 
	/\ m.bal.bal = b 
	/\ Len(m.bal.val) >= i 
	/\ m.bal.val[i] = v  

Consistency == 
  \A i, j \in 1..Cardinality(Values), vi, vj \in Values:
  PossDecided(i, vi) /\ PossDecided(j, vj) => 
     \/ i = j /\ vi = vj (* a slot is only ever filled with one value *)
     \/ i /= j /\ vi /= vj (* a value cannot be in two different slots *)
=============================================================================

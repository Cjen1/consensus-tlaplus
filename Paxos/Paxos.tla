----------------------------- MODULE Paxos -----------------------------

EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS BallotNumbers, Acceptors, Values, Quorums

VARIABLES   msgs,
            acc,
            prop

Range(s) == {s[i] : i \in DOMAIN s}

Max(Leq(_,_), s) == CHOOSE v \in s: \A v1 \in s: Leq(v1, v)
Min(Leq(_,_), s) == CHOOSE v \in s: \A v1 \in s: Leq(v, v1)

None == CHOOSE v : v \notin Values

PossibleValues == Values \cup {None}

BallotLeq(a, b) ==
  \/ a.bal < b.bal
  \/ a.bal = b.bal /\ a.val = b.val

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
        /\ acc  = [a \in Acceptors |-> [maxBalNum |-> -1, maxBal |-> [bal |-> -1, val |-> None]]]
        /\ prop = [b \in BallotNumbers |-> [val |-> None, valSelect |-> FALSE, committed |-> None, hasCommitted |-> FALSE]]

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
  /\ \E v \in IF prop[b].val = None THEN Values ELSE {prop[b].val}:
        LET bal == [bal |-> b, val |-> v]
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
        IN /\ \A m \in S: \A m1 \in S \ {m}: m.acc /= m1.acc
           /\ prop' = [prop EXCEPT ![b] = [prop[b] EXCEPT !.committed = val, !.hasCommitted = TRUE]]
           /\ UNCHANGED << msgs, acc >>

Next == \/ \E p \in BallotNumbers   : Phase1a(p) \/ ValueSelect(p) \/ Phase2a(p) \/ Commit(p)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
Consistency ==
  \A b1, b2 \in BallotNumbers: 
  LET v1 == prop[b1].committed
      v2 == prop[b2].committed
  IN (b1 < b2 /\ prop[b1].hasCommitted /\ prop[b2].hasCommitted) => v1 = v2

ProposerConsistency ==
  \A b \in BallotNumbers: 
     prop[b].hasCommitted => /\ prop'[b].hasCommitted
                             /\ prop[b].committed = prop'[b].committed 
=============================================================================

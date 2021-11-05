----------------------------- MODULE VectorPaxos -----------------------------

(* Adapated from the excellent Paxos example at 
 * https://github.com/tlaplus/Examples/blob/master/specifications/Paxos/Paxos.tla
 *)

EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS Proposers, Acceptors, Values, Quorums

VARIABLES   msgs,
            acc,
            prop,
	    committed

Bot == CHOOSE a : a \notin Acceptors

IsBalNum(b) ==
  \/ /\ b.acc = Bot
     /\ b.dep = {}
  \/ /\ b.acc \in Acceptors
     /\ \A b1 \in b[dep]: IsBalNum(b1)

BalNumLeq(a,b) ==
  \/ /\ a \in b.dep
     /\ a.dep \subseteq b.dep
  \/ a = b

Max(Leq(_,_), s) == CHOOSE v \in s: \A v1 \in s: Leq(v1, v)
Min(Leq(_,_), s) == CHOOSE v \in s: \A v1 \in s: Leq(v, v1)

None == CHOOSE v : v \notin Values

(* The comparison function used by acceptors to update acc[a].maxBal
 * It is also used by the ValueSelect function to choose the 'maximum' ballot
 * And by the proposer to commit the 'minimum' of the quorum responses. *)
BallotLeq(a, b) ==
  \/ BalNumLeq(a.bal, b.bal)
  \/ a.bal = b.bal /\ a.val = b.val

-----------------------------------------------------------------------------

InitBalNum == [acc |-> Bot, dep |-> {}]

(* Initial state of the the system. *)
Init == /\ msgs = {}
        /\ acc  = [a \in Acceptors |-> [maxBalNum |-> InitBalNum, maxBal |-> [bal |-> InitBalNum, val |-> None]]]
        /\ prop = [p \in Proposers |-> [balNum |-> [acc |-> p, dep |-> InitBalNum], val |-> None, valSelect |-> FALSE]]
	/\ committed = None

Send(m) == msgs' = msgs \cup {m}

RNack(p) ==
  \E m \in msgs:
    /\ m.type = "nack"
    /\ ~BallotNumLeq(prop[p].balNum, m.balNum]
    /\ prop' = [prop EXCEPT ![p] = [prop[p] EXCEPT !.balNum = [acc |-> p, dep |-> m.balNum.dep \cup m]]]
    /\ UNCHANGED << msgs, acc, committed >>

(* Phase 1a: A proposer for ballot number b sends a 1a message. *)
Phase1a(p) == 
  /\ ~\E m \in msgs: m.type = "1a" /\ m.balNum = b
  /\ Send ([type |-> "1a", balNum |-> b])
  /\ UNCHANGED << acc, prop, committed >>

(* Phase 1b: When an acceptor receives a 1a message, if that message is from 
 * a higher ballot number than the highest one heard of, then update the 
 * highest ballot number and respond with the stored highest ballot. *)
Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ \/ /\ BallotNumLeq(m.balNum, acc[a].maxBalNum) (* msg.bal > acc.maxBalNum *)
          /\ acc' = [acc EXCEPT ![a] = [acc[a] EXCEPT !.maxBalNum = m.balNum]]
	  /\ ~\E m1 \in msgs: m1.type = "1b" /\ m1.balNum = m.balNum
          /\ Send([type |-> "1b", balNum |-> m.balNum, acc |-> a, maxBal |-> acc[a].maxBal])
       \/ /\ ~ BallotNumLeq(m.balNum, acc[a].maxBalNUm)
          /\ Send([type |-> "nack", balNum |-> acc[a].maxBalNum])
	  /\ acc' = acc
    /\ UNCHANGED << prop, committed >>
    

(* ValueSelect: When a proposer receives a quorum of phase 1b responses, it sets
 * valSelect and its stored value to the value of the maximum ballot within 
 * those responses. This enables Phase2a. *)
ValueSelect(p) ==
  LET b = prop[p].balNum
  IN
  /\ ~ prop[p].valSelect
  /\ \E Q \in Quorums, S \in SUBSET {m \in msgs: (m.type = "1b") /\ (m.balNum = b)}:
       /\ \A a \in Q: \E m \in S: m.acc = a
       /\ LET maxBal == Max(BallotLeq, {m.maxBal: m \in S})
          IN  /\ prop' = [prop EXCEPT ![p] = 
	                          [prop[p] EXCEPT !.val = maxBal.val, !.valSelect = TRUE]]
	      /\ UNCHANGED << acc, msgs, committed >>

(* Phase2a: A proposer proposes a value. If its stored val is none, it chooses
 * a new value. It updates its stored value and sends the ballot. This ensures
 * that it will only propose one value. *)
Phase2a(p) ==
  LET b = prop[p].balNum
  IN
  /\ prop[p].valSelect
  /\ \E v \in IF prop[p].val = None THEN Values ELSE {prop[p].val}:
        LET bal == [bal |-> b, val |-> v]
        IN /\ Send([type |-> "2a", bal |-> bal])
           /\ prop' = [prop EXCEPT ![b] = [prop[b] EXCEPT !.val = bal.val]]
  /\ UNCHANGED << acc >>

(* Phase2b: An acceptor upon receiving a phase 2a message from ballot greater 
 * than or equal to its own, and which has a greater than or equal ballot than
 * its stored one updates its stored and responds with a vote for the new ballot. *)
Phase2b(a) ==
  /\ \E m \in msgs :
      /\ m.type = "2a"
      /\ m.bal.bal >= acc[a].maxBalNum
      /\ BallotLeq(acc[a].maxBal, m.bal)
      /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal])
      /\ acc' = [acc EXCEPT ![a] = [maxBalNum |-> m.bal.bal, maxBal |-> m.bal]]
  /\ UNCHANGED << prop >>

(* Commit: When a proposer receives a quorum of votes for a value it commits
 * that value. Since all the ballots are equal (Min(BallotLeq,...)).val selects
 * the value. *)
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

(* Next: a disjunction of all possible actions. Since each action asserts that
 * other states are unchanged only one is true at a time. *)
Next == \/ \E p \in BallotNumbers   : Phase1a(p) \/ ValueSelect(p) \/ Phase2a(p) \/ Commit(p)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

-----------------------------------------------------------------------------
(* Type checking invariant *)

PossibleValues == Values \cup {None}

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

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* The system is consistent if once a value is committed, any values committed
 * in greater ballots equal it. *)
Consistency ==
  \A b1, b2 \in BallotNumbers: 
  LET v1 == prop[b1].committed
      v2 == prop[b2].committed
  IN (b1 < b2 /\ prop[b1].hasCommitted /\ prop[b2].hasCommitted) => v1 = v2

(* Once the proposer commits a value it cannot commit any other values *)
ProposerConsistency ==
  \A b \in BallotNumbers: 
     prop[b].hasCommitted => /\ prop'[b].hasCommitted
                             /\ prop[b].committed = prop'[b].committed 
=============================================================================

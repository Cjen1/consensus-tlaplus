----------------------------- MODULE MultiPaxos -----------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Proposers, Acceptors, Values, Quorums

VARIABLES   msgs,
            acc,
            prop,
	    propBal

BallotNumbers == Nat \cup {-1}

(* Proposer numbering for ordering and ballot assignment *)
PropNum == CHOOSE f \in [Proposers -> 1..Cardinality(Proposers)]: \A p1, p2 \in Proposers: p1 /= p2 => f[p1] /= f[p2]

(* One log is a prefix of another if every item in the prefix is in the other.
 * ie Prefix([1,2,3], [1,2,3,4])
 *    Prefix([1,2,3], [1,2,3])
 *   ~Prefix([1,2,3], [1,2,4]) 
 *)
Prefix(a,b) ==
  /\ Len(a) =< Len(b)
  /\ \A i \in DOMAIN a: a[i] = b[i]

(* The set of all elements in the list. *)
Range(s) == {s[i] : i \in DOMAIN s}

Max(Leq(_,_), s) == CHOOSE v \in s: \A v1 \in s: Leq(v1, v)
Min(Leq(_,_), s) == CHOOSE v \in s: \A v1 \in s: Leq(v, v1)

(* The comparison function used by acceptors to update acc[a].maxBal
 * It is also used by the ValueSelect function to choose the 'maximum' ballot
 * And by the proposer to commit the 'minimum' of the quorum responses. *)
BallotLeq(a, b) ==
  \/ a.bal < b.bal
  \/ a.bal = b.bal /\ Prefix(a.val, b.val)

-----------------------------------------------------------------------------

(* Initial state of the the system. *)
Init == /\ msgs = {}
        /\ acc  = [a \in Acceptors |-> [maxBalNum |-> -1, maxBal |-> [bal |-> -1, val |-> <<>>]]]
        /\ prop = [p \in Proposers |-> [val |-> << >>, phase1Complete |-> FALSE]]
	/\ propBal = [p \in Proposers |-> PropNum[p]]

Send(m) == msgs' = msgs \cup {m}

ProposerBalNum(p, b) ==
  /\ b % Cardinality(Proposers) = PropNum[p]
  /\ propBal[p] <= b
  /\ propBal' = [propBal EXCEPT ![p] = b]

(* Phase 1a: A proposer for ballot number b sends a 1a message. *)
Phase1a(p, b) == 
  /\ ~\E m \in msgs: m.type = "1a" /\ m.balNum = b
  /\ Send ([type |-> "1a", balNum |-> b])
  /\ UNCHANGED << prop >>

(* Phase 1b: When an acceptor receives a 1a message, if that message is from 
 * a higher ballot number than the highest one heard of, then update the 
 * highest ballot number and respond with the stored highest ballot. *)
Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.balNum > acc[a].maxBalNum
    /\ acc' = [acc EXCEPT ![a] = [acc[a] EXCEPT !.maxBalNum = m.balNum]]
    /\ Send([type |-> "1b", balNum |-> m.balNum, acc |-> a, maxBal |-> acc[a].maxBal])

(* ValueSelect: When a proposer receives a quorum of phase 1b responses, it sets
 * phase1Complete and its stored value to the value of the maximum ballot within 
 * those responses. This enables Phase2a. *)
ValueSelect(p, b) ==
  /\ ~ prop[p].phase1Complete
  /\ \E Q \in Quorums, S \in SUBSET {m \in msgs: (m.type = "1b") /\ (m.balNum = b)}:
       /\ \A a \in Q: \E m \in S: m.acc = a
       /\ LET maxBal == Max(BallotLeq, {m.maxBal: m \in S})
          IN  /\ prop' = [prop EXCEPT ![p] = 
	                          [prop[p] EXCEPT !.val = maxBal.val, !.phase1Complete = TRUE]]
	      /\ UNCHANGED << msgs >>

(* Phase2a: A proposer appends a value to its stored log and sends out a 
 * phase2a message containing the new log. This ensures that all proposed logs
 * extend previous ones. *)
Phase2a(p, b) ==
  /\ prop[p].phase1Complete
  /\ \E v \in {<<>>} \cup {<<v>> : v \in Values \ Range(prop[p].val)}:
        LET bal == 
	  [bal |-> b, 
	   val |-> prop[p].val \o v]
        IN /\ Send([type |-> "2a", bal |-> bal])
           /\ prop' = [prop EXCEPT ![p] = [prop[p] EXCEPT !.val = bal.val]]

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

(* Next: a disjunction of all possible actions. Since each action asserts that
 * other states are unchanged only one is true at a time. *)
Next == \/ \E p \in Proposers, b \in BallotNumbers:
            /\ ProposerBalNum(p, b)
	    /\ UNCHANGED << acc >>
	    /\ Phase1a(p, b) \/ ValueSelect(p, b) \/ Phase2a(p, b)
        \/ \E a \in Acceptors :
	    /\ UNCHANGED << prop, propBal >>
	    /\ Phase1b(a) \/ Phase2b(a)

-----------------------------------------------------------------------------
(* Type checking invariant *)

(* All possible sequences from a set of items. *)
AllSeqFromSet(S) ==
  LET unique(f) == \A i,j \in DOMAIN f: i /= j => f[i] /= f[j]
      subseq(c) == {seq \in [1..c -> S]: unique(seq)}
  IN
  UNION {subseq(c): c \in 0..Cardinality(S)}

PossibleLogs == AllSeqFromSet(Values)

PossibleBallots == [bal : BallotNumbers, val : PossibleLogs]

Messages ==      [type : {"1a"}, balNum : BallotNumbers]
            \cup [type : {"1b"}, acc : Acceptors, balNum : BallotNumbers, maxBal : PossibleBallots]
            \cup [type : {"2a"}, bal : PossibleBallots]
            \cup [type : {"2b"}, acc : Acceptors, bal : PossibleBallots]

ProposerState == [val : PossibleLogs,
                  phase1Complete : {TRUE, FALSE}]

AcceptorState == [maxBalNum : BallotNumbers \cup {-1}, maxBal : PossibleBallots]

TypeInvariant == /\ msgs \in SUBSET Messages
                 /\ acc \in [Acceptors -> AcceptorState]
                 /\ prop \in [Proposers -> ProposerState]
		 /\ propBal \in [Proposers -> BallotNumbers]

vars == <<msgs, acc, prop, propBal>>

-----------------------------------------------------------------------------

Spec == Init /\ [][Next]_vars

=============================================================================

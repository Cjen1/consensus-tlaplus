----------------------------- MODULE MultiPaxos -----------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS NProposers, Acceptors, Values, Quorums

VARIABLES msgs, acc

BallotNumbers == Nat \cup {-1}

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

Send(m) == msgs' = msgs \cup {m}

SameProposer(b1, b2) == b1 % NProposers = b2 %NProposers

(* Phase 1a: A proposer for ballot number b sends a 1a message. *)
Phase1a(b) == 
  /\ ~\E m \in msgs: m.type = "1a" /\ m.balNum = b
  /\ Send ([type |-> "1a", balNum |-> b])

(* Phase 1b: When an acceptor receives a 1a message, if that message is from 
 * a higher ballot number than the highest one heard of, then update the 
 * highest ballot number and respond with the stored highest ballot. *)
Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.balNum > acc[a].maxBalNum
    /\ acc' = [acc EXCEPT ![a] = [acc[a] EXCEPT !.maxBalNum = m.balNum]]
    /\ Send([type |-> "1b", balNum |-> m.balNum, acc |-> a, maxBal |-> acc[a].maxBal])

(* Phase2a: A proposer appends a value to the previously maximum proposed ballot (or result from 1b)
 * So we check if there are any sent 2a messages, if so we take the maximum proposed ballot
 * Otherwise we pick one of all possibly selected 1b ballots (based on 1b messages)
 * *)
Phase2a(b) ==
  LET prev1b == {m \in msgs: m.type = "1b" /\ m.balNum = b}
      filledQuorums == {Q \in Quorums: \A a \in Q: \E m \in prev1b: m.acc = a}
      valueSelected(Q) == (Max(BallotLeq, {m.maxBal: m \in {m \in prev1b: m.acc \in Q}})).val
      prev2a == {m \in msgs: m.type = "2a" /\ m.bal.bal = b}
      valueOptions == 
        IF prev2a = {} (* Has not selected a value *)
        THEN {valueSelected(Q): Q \in filledQuorums}
        ELSE {(Max(BallotLeq, {m.bal: m \in prev2a})).val}
  IN \E prev \in valueOptions: \E v \in {<<>>} \cup {<<v>> : v \in Values \ Range(prev)}:
         Send([type |-> "2a", bal |-> [bal |-> b, val |-> prev \o v]])

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
Next == 
  \/ \E b \in BallotNumbers:
      /\ b > 0
      (* Proposers only increase their ballot *)
      /\ ~\E m \in msgs: 
             /\ \/ m.type = "1a" /\ SameProposer(b, m.balNum)  /\ m.balNum > b
	        \/ m.type = "2a" /\ SameProposer(b, m.bal.bal) /\ m.bal.bal > b 
      /\ Phase1a(b) \/ Phase2a(b)
      /\ UNCHANGED << acc >>
  \/ \E a \in Acceptors :
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

AcceptorState == [maxBalNum : BallotNumbers \cup {-1}, maxBal : PossibleBallots]

TypeInvariant == /\ msgs \in SUBSET Messages
                 /\ acc \in [Acceptors -> AcceptorState]

vars == <<msgs, acc >>

-----------------------------------------------------------------------------

Spec == Init /\ [][Next]_vars

=============================================================================

----------------------------- MODULE VectorPaxos -----------------------------

(* Adapated from the excellent Paxos example at 
 * https://github.com/tlaplus/Examples/blob/master/specifications/Paxos/Paxos.tla
 *)

EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS Proposers, Acceptors, Commands, Quorums

VARIABLES   msgs,
            acc,
            prop

----

Bot == CHOOSE a : a \notin Acceptors

InitBalNum == << Bot, {} >>

IncrementBallotNumber(b, b_dep) == << b[1], b[2] \cup {b_dep} >>

BalNumLeq(a,b) ==
  \/ a = b
  \/ a \in b[2]

Max(Leq(_,_), s) == CHOOSE v \in s: \A v1 \in s: Leq(v1, v)
Min(Leq(_,_), s) == CHOOSE v \in s: \A v1 \in s: Leq(v, v1)

None == CHOOSE v : v \notin Commands

(* The comparison function used by acceptors to update acc[a].maxBal
 * It is also used by the ValueSelect function to choose the 'maximum' ballot
 * And by the proposer to commit the 'minimum' of the quorum responses. *)
BallotLeq(a, b) ==
  \/ BalNumLeq(a.bal, b.bal)
  \/ a.bal = b.bal /\ a.val = b.val

-----------------------------------------------------------------------------

(* Initial state of the the system. *)
Init == /\ msgs = {}
        /\ acc  = [a \in Acceptors |-> [maxBalNum |-> InitBalNum, maxBal |-> [bal |-> InitBalNum, val |-> None]]]
        /\ prop = [p \in Proposers |-> [balNum |-> << p, {InitBalNum} >>]]

Send(m) == msgs' = msgs \cup {m}

RNack(p) ==
  \E m \in msgs:
    /\ m.type = "nack"
    /\ ~BalNumLeq(m.balNum, prop[p].balNum) (* p.bal < m.bal => ~ m.bal <= p.bal *)
    /\ prop' = [prop EXCEPT ![p] = [prop[p] EXCEPT !.balNum = IncrementBallotNumber(prop[p].balNum, m.balNum)]]
    /\ UNCHANGED << msgs, acc >>

(* Phase 1a: A proposer for ballot number b sends a 1a message. *)
Phase1a(p) == 
  /\ ~\E m \in msgs: m.type = "1a" /\ m.balNum = prop[p].balNum
  /\ Send ([type |-> "1a", balNum |-> prop[p].balNum])
  /\ UNCHANGED << acc, prop >>

(* Phase 1b: When an acceptor receives a 1a message, if that message is from 
 * a higher ballot number than the highest one heard of, then update the 
 * highest ballot number and respond with the stored highest ballot. *)
Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ \/ /\ BalNumLeq(acc[a].maxBalNum, m.balNum)
	  /\ ~\E m1 \in msgs: m1.type = "1b" /\ m1.balNum = m.balNum /\ m1.acc = a
          /\ Send([type |-> "1b", balNum |-> m.balNum, acc |-> a, maxBal |-> acc[a].maxBal])
          /\ acc' = [acc EXCEPT ![a] = [acc[a] EXCEPT !.maxBalNum = m.balNum]]
       \/ /\ ~ BalNumLeq(acc[a].maxBalNum, m.balNum)
          /\ Send([type |-> "nack", balNum |-> acc[a].maxBalNum])
	  /\ acc' = acc
    /\ UNCHANGED << prop >>

(* If the proposer has already sent a 2a for b, then resend *)
Phase2a(p) ==
  LET b == prop[p].balNum
      p2a_msgs == {m \in msgs: m.type = "2a" /\ m.bal.bal = b}
      all_p1b_msgs == {m \in msgs: m.type = "1b"/\ m.balNum = b}
      quorum(S) == \E Q \in Quorums: \A a \in Q: \E m \in S: m.acc = a
      p1b_msgs == {S \in SUBSET all_p1b_msgs: quorum(S)}
      prev_values == IF p2a_msgs = {}
                    THEN {Max(BallotLeq, {m.maxBal: m \in M}).val: M \in p1b_msgs}
		    ELSE {CHOOSE v \in {m.bal.val : m \in p2a_msgs}: TRUE}
  IN 
  /\ \E prev \in prev_values:
      IF prev = None
      THEN \E c \in Commands: Send([type |-> "2a", bal |-> [bal |-> b, val |-> c]])
      ELSE                    Send([type |-> "2a", bal |-> [bal |-> b, val |-> prev]])
  /\ UNCHANGED << prop, acc >>

(* Phase2b: An acceptor upon receiving a phase 2a message from ballot greater 
 * than or equal to its own, and which has a greater than or equal ballot than
 * its stored one updates its stored and responds with a vote for the new ballot. *)
Phase2b(a) ==
  /\ \E m \in msgs :
      /\ m.type = "2a"
      /\ BalNumLeq(acc[a].maxBalNum, m.bal.bal)
      /\ BallotLeq(acc[a].maxBal, m.bal)
      /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal])
      /\ acc' = [acc EXCEPT ![a] = [maxBalNum |-> m.bal.bal, maxBal |-> m.bal]]
  /\ UNCHANGED << prop >>

(* Next: a disjunction of all possible actions. Since each action asserts that
 * other states are unchanged only one is true at a time. *)
Next == /\ \/ \E p \in Proposers : RNack(p)   \/ Phase1a(p) \/ Phase2a(p)
           \/ \E a \in Acceptors :               Phase1b(a) \/ Phase2b(a)

-----------------------------------------------------------------------------
(* Type checking invariant *)

PossibleValues == Commands \cup {None}

RECURSIVE IsBalNum(_)
IsBalNum(b) ==
  \/ b = InitBalNum
  \/ /\ b[1] \in Proposers
     /\ \A b1 \in b[2]: IsBalNum(b1)

IsBallot(b) ==
  /\ DOMAIN b = {"bal", "val"}
  /\ IsBalNum(b.bal)
  /\ b.val \in PossibleValues

Is1a(m) == 
  /\ DOMAIN m = {"type", "balNum"}
  /\ m.type = "1a"
  /\ IsBalNum(m.balNum)

Is1b(m) ==
  /\ DOMAIN m = {"type", "acc", "balNum", "maxBal"}
  /\ m.type = "1b"
  /\ m.acc \in Acceptors
  /\ IsBalNum(m.balNum)
  /\ IsBallot(m.maxBal)

IsNack(m) ==
  /\ DOMAIN m = {"type", "balNum"}
  /\ m.type = "nack"
  /\ IsBalNum(m.balNum)

Is2a(m) ==
  /\ DOMAIN m = {"type", "bal"}
  /\ m.type = "2a"
  /\ IsBallot(m.bal)

Is2b(m) ==
  /\ DOMAIN m = {"type", "bal", "acc"}
  /\ m.type = "2b"
  /\ m.acc \in Acceptors
  /\ IsBallot(m.bal)

IsProposer(p) ==
  /\ DOMAIN p = {"balNum"}
  /\ IsBalNum(p.balNum)

IsAcceptor(a) ==
  /\ DOMAIN a = {"maxBalNum", "maxBal"}
  /\ IsBalNum(a.maxBalNum)
  /\ IsBallot(a.maxBal)

TypeInvariant == /\ \A m \in msgs: \/ Is1a(m)
                                   \/ Is1b(m)
				   \/ IsNack(m)
				   \/ Is2a(m)
				   \/ Is2b(m)
                 /\ \A p \in Proposers: IsProposer(prop[p])
                 /\ \A a \in Acceptors: IsAcceptor(acc[a])

vars == <<msgs, acc, prop>>

-----------------------------------------------------------------------------

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\*(* A ballot is commitable if there exists a proposer which could commit it *)
\*Commitable(v) ==
\*  \E p \in Proposers:
\*  \E Q \in Quorums:
\*  \A a \in Q: \E m \in msgs: 
\*    /\ m.type = "2b"
\*    /\ m.bal = [bal |-> prop[p].balNum, val |-> v]
\*    /\ m.acc = a
\*
\*Consistency == \A v \in Commands: [](Commitable(v) => [](\A v1 \in Commands: Commitable(v1) => v = v1))
=============================================================================

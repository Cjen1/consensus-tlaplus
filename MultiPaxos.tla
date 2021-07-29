----------------------------- MODULE MultiPaxos -----------------------------

EXTENDS Integers, Sequences

CONSTANTS Ballots, Acceptors, Values, Quorums

VARIABLES   msgs,
            maxBal,
            maxVBal,
            maxVal

PossibleValues == Seq(Values)

Messages ==      [type : {"1a"}, bal : Ballots]
            \cup [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
                    maxVal : PossibleValues, acc : Acceptors]
            \cup [type : {"2a"}, bal : Ballots, val : PossibleValues]
            \cup [type : {"2b"}, bal : Ballots, val : PossibleValues, acc : Acceptors]

TypeInvariant == /\ msgs \in SUBSET Messages
                 /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
                 /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
                 /\ maxVal \in [Acceptors -> PossibleValues]
                 /\ \A a \in Acceptors : maxBal[a] >= maxVBal[a]

vars == <<msgs, maxBal, maxVBal, maxVal>>

-----------------------------------------------------------------------------

Send(m) == msgs' = msgs \cup {m}

None == CHOOSE v : v \notin Values

Init == /\ msgs = {}
        /\ maxVBal = [a \in Acceptors |-> -1]
        /\ maxBal = [a \in Acceptors |-> -1]
        /\ maxVal = [a \in Acceptors |-> Seq({})]

Phase1a(b) == 
  /\ ~ \E m \in msgs : (m.type = "1a") /\ (m.bal = b)
  /\ Send ([type |-> "1a", bal |-> b])
  /\ UNCHANGED <<maxVBal, maxBal, maxVal>>


Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.bal > maxBal[a]
    /\ Send([type |-> "1b", bal |-> m.bal, maxVBal |-> maxVBal[a],
                maxVal |-> maxVal[a], acc |-> a])
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ UNCHANGED <<maxVBal, maxVal>>

\* a \subseteq b
Prefix(a,b) ==
  /\ Len(a) =< Len(b)
  /\ \A i \in DOMAIN a: a[i] = b[i]

ValueSelect(b) ==
  CHOOSE v :
    \E Q \in Quorums:
      \E S \in SUBSET {m \in msgs : (m.type = "1b") /\ (m.bal = b)} :
        /\ \A a \in Q : \E m \in S : m.acc = a
        \* S is a set of 1b messages from a quorum of acceptors
	/\ LET c == CHOOSE c \in 0..(b-1) : \A m \in S: m.maxVBal =< c 
	   IN 
	   \* Find a message which is from the highest maxVBal
	   \E m \in S :
	         /\ m.maxVBal = c
	         \* and forall m1 in S. m1.maxValue is a prefix of m.maxValue
		 /\ \A m1 \in S :
		       \/ m1.maxVBal \= c
		       \/ /\ m1.maxVBal = c
		          /\ Prefix(m1.maxValue, m.maxValue)
	 	 \* Thus v = m.maxValue
	         /\ v = m.maxValue

Phase2a(b) ==
  /\ LET prefix == ValueSelect(b)
     IN \E v \in Values :
           /\ ~ \E v1 \in prefix: v = v1
	   /\ LET val == prefix \o <<v>>
	      IN /\ ~ \E m \in msgs : (m.type = "2a") /\ (m.bal = b) /\ (m.val = val)
                 /\ Send([type |-> "2a", bal |-> b, val |-> val])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Phase2b(a) ==
  \E m \in msgs :
    /\ m.type = "2a"
    /\ m.bal >= maxBal[a]
    /\ Send([type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a])
    /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
    /\ maxBal'  = [maxBal EXCEPT ![a] = m.bal]
    /\ maxVal'  = [maxVal EXCEPT ![a] = m.val]

Next == \/ \E b \in Ballots   : Phase1a(b) \/ Phase2a(b)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

VotedForIn(a, v, b) == \E m \in msgs : /\ m.type = "2b"
                                       /\ Prefix(v, m.val)
                                       /\ m.bal = b
                                       /\ m.acc = a

ChosenIn(v, b) == \E Q \in Quorums :
                        \A a \in Q : VotedForIn(a, v, b)

Chosen(v) == \E b \in Ballots : ChosenIn(v, b)

Consistency == \A b1, b2 \in Ballots : 
		  /\ b1 =< b2
		  /\ \A v1, v2 \in PossibleValues : ChosenIn(b1, v1) /\ ChosenIn(b2, v2) => Prefix(v1, v2)

=============================================================================
\* Modification History
\* Last modified Wed Jul 28 18:26:38 BST 2021 by cjen1

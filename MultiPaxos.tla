----------------------------- MODULE MultiPaxos -----------------------------

EXTENDS Integers, Sequences

CONSTANTS Ballots, Acceptors, Values, Quorums

VARIABLES msgs,
            maxBal,
            maxVBal,
            maxVal

vars == <<msgs, maxBal, maxVBal, maxVal>>

Send(m) == msgs' = msgs \cup {m}

None == CHOOSE v : v \notin Values

Init == /\ msgs = {}
        /\ maxVBal = [a \in Acceptors |-> -1]
        /\ maxBal = [a \in Acceptors |-> -1]
        /\ maxVal = [a \in Acceptors |-> None]

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


ValueSelect(v, b) ==
  \E Q \in Quorums:
    \E S \in SUBSET {m \in msgs : (m.type = "1b") /\ (m.bal = b)} :
      /\ \A a \in Q : \E m \in S : m.acc = a
      /\ \/ \A m \in S : m.maxVBal = -1
         \/ \E c \in 0..(b-1) :
            /\ \A m \in S : m.maxVBal =< c
            /\ \E m \in S : /\ m.maxVBal = c
                            /\ m.maxVal = v

Phase2a(b) ==
  /\ ~ \E m \in msgs : (m.type = "2a") /\ (m.bal = b)
  /\ \E v \in Values :
    /\ ValueSelect(v, b)
    /\ Send([type |-> "2a", bal |-> b, val |-> v])
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
                                       /\ m.val = v
                                       /\ m.bal = b
                                       /\ m.acc = a

ChosenIn(v, b) == \E Q \in Quorums :
                        \A a \in Q : VotedForIn(a, v, b)

Chosen(v) == \E b \in Ballots : ChosenIn(v, b)

Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => (v1 = v2)

Messages ==      [type : {"1a"}, bal : Ballots]
            \cup [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
                    maxVal : Values \cup {None}, acc : Acceptors]
            \cup [type : {"2a"}, bal : Ballots, val : Values]
            \cup [type : {"2b"}, bal : Ballots, val : Values, acc : Acceptors]

TypeOk == /\ msgs \in SUBSET Messages
          /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
          /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
          /\ maxVal \in [Acceptors -> Values \cup {None}]
          /\ \A a \in Acceptors : maxBal[a] >= maxVBal[a]

=============================================================================
\* Modification History
\* Last modified Wed Jul 28 15:21:40 BST 2021 by cjen1
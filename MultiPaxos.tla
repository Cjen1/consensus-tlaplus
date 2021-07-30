----------------------------- MODULE MultiPaxos -----------------------------

EXTENDS TLC, Integers, Sequences

CONSTANTS Ballots, Acceptors, Values, Quorums

VARIABLES   msgs,
            maxBal,
            maxVBal,
            maxVal,
            propVal

\* a \subseteq b
Prefix(a,b) ==
  /\ Len(a) =< Len(b)
  /\ \A i \in DOMAIN a: a[i] = b[i]

\* The set of all possible insertions of x into s
Insert(x, s) == 
  LET insert(i,j) == CASE j < i -> s[j]
                       [] j = i -> x
                       [] j > i -> s[j-1]
  IN
  LET CreateSeq(i) == [j \in 1..(Len(s) + 1) |-> insert(i,j)]
      SearchSpace == DOMAIN s \cup {Len(s) + 1}
  IN {CreateSeq(i) :i \in SearchSpace}

RECURSIVE AllSeqFromSet(_)
AllSeqFromSet(S) ==
  IF S = {} THEN {<< >>}
  ELSE 
  LET _op(x) == 
    LET acc == AllSeqFromSet(S \ {x})
        ins == UNION {Insert(x, s): s \in acc}
    IN acc \union ins
  IN
  UNION { _op(x): x \in S}

PossibleValues == AllSeqFromSet(Values)

Messages ==      [type : {"1a"}, bal : Ballots]
            \cup [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
                    maxVal : PossibleValues, acc : Acceptors]
            \cup [type : {"2a"}, bal : Ballots, val : PossibleValues]
            \cup [type : {"2b"}, bal : Ballots, val : PossibleValues, acc : Acceptors]

TypeInvariant == /\ msgs \in SUBSET Messages
                 /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
                 /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
                 /\ maxVal \in [Acceptors -> PossibleValues]
                 /\ propVal \in [Ballots -> PossibleValues]
                 /\ \A a \in Acceptors : maxBal[a] >= maxVBal[a]

vars == <<msgs, maxBal, maxVBal, maxVal, propVal>>

-----------------------------------------------------------------------------

Init == /\ msgs = {}
        /\ maxVBal = [a \in Acceptors |-> -1]
        /\ maxBal = [a \in Acceptors |-> -1]
        /\ maxVal = [a \in Acceptors |-> << >>]
        /\ propVal = [b \in Ballots |-> << >>]

Send(m) == msgs' = msgs \cup {m}

Phase1a(b) == 
  /\ ~ \E m \in msgs : (m.type = "1a") /\ (m.bal = b)
  /\ Send ([type |-> "1a", bal |-> b])
  /\ UNCHANGED <<maxVBal, maxBal, maxVal, propVal>>

Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.bal > maxBal[a]
    /\ Send([type |-> "1b", bal |-> m.bal, maxVBal |-> maxVBal[a],
                maxVal |-> maxVal[a], acc |-> a])
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ UNCHANGED <<maxVBal, maxVal, propVal>>

QuorumExists(s, b) ==
  \E Q \in Quorums:
    \A a \in Q : \E m \in s : (m.type = "1b") /\ m.acc = a /\ (m.bal = b)

ValueSelect(b) ==
  LET S == CHOOSE s \in SUBSET {m \in msgs : (m.type = "1b") /\ (m.bal = b)} : QuorumExists(s, b)
      c == (CHOOSE mc \in S : \A m \in S: m.maxVBal =< mc.maxVBal).maxVBal
      r == {m \in S: m.maxVBal = c}
      m == CHOOSE m \in r : ~\E m1 \in r : ~Prefix(m1.maxVal, m.maxVal)
  IN m.maxVal

Phase2a(b) ==
  /\ QuorumExists(msgs, b)
  /\ LET prefix == ValueSelect(b)
     IN \E v \in Values :
           /\ ~ \E iv1 \in DOMAIN prefix: v = prefix[iv1]
           /\ LET val == prefix \o <<v>>
              IN /\ Prefix(propVal[b], val)
                 /\ ~ \E m \in msgs : (m.type = "2a") /\ (m.bal = b) /\ (m.val = val)
                 \* Requires a strong proposer
                 /\ propVal' = [propVal EXCEPT ![b] = val]
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
    /\ UNCHANGED <<propVal>>

Next == \/ \E b \in Ballots   : Phase1a(b) \/ Phase2a(b)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

VotedForIn(a, v, b) == 
    \E m \in msgs : /\ m.type = "2b"
                    /\ m.bal = b
                    /\ m.acc = a
                    /\ m.val = v

ChosenIn(b, v) == \E Q \in Quorums :
                        \A a \in Q : 
                          /\ VotedForIn(a, v, b)

Consistency == 
  \A b1, b2 \in Ballots : 
                  b1 < b2 => \A v1, v2 \in PossibleValues : 
                      (ChosenIn(b1, v1) /\ ChosenIn(b2, v2)) => Prefix(v1, v2)

=============================================================================
\* Modification History
\* Last modified Wed Jul 28 18:26:38 BST 2021 by cjen1

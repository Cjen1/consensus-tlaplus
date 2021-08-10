----------------------------- MODULE MultiPaxos -----------------------------

EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS Ballots, Acceptors, Values, Quorums

VARIABLES   msgs,
            maxBal,
            maxVBal,
            maxVal,
            propVal

\* a =< b
Prefix(a,b) ==
  /\ Len(a) =< Len(b)
  /\ \A i \in DOMAIN a: a[i] = b[i]

Range(s) == {s[i] : i \in DOMAIN s}

AllSeqFromSet(S) ==
  LET unique(f) == \A i,j \in DOMAIN f: i /= j => f[i] /= f[j]
      subseq(c) == {seq \in [1..c -> S]: unique(seq)}
  IN
  UNION {subseq(c): c \in 0..Cardinality(S)}

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

QuorumExists(s, b, type) ==
  \E Q \in Quorums:
    \A a \in Q : \E m \in s : (m.type = type) /\ m.acc = a /\ (m.bal = b)

ValueSelect(b) ==
  LET s == CHOOSE s \in SUBSET {m \in msgs : (m.type = "1b") /\ (m.bal = b)} : QuorumExists(s, b, "1b")
      c == (CHOOSE mc \in s : \A m \in s: m.maxVBal =< mc.maxVBal).maxVBal
      r == {m \in s: m.maxVBal = c}
      m == CHOOSE m \in r : ~\E m1 \in r : ~Prefix(m1.maxVal, m.maxVal)
  IN m.maxVal

Send2a(b, msg) ==
  /\ ~ \E m \in msgs : m = msg
  /\ Prefix(propVal[b], msg.val)
  /\ propVal' = [propVal EXCEPT ![b] = msg.val]
  /\ Send(msg)

ProposeNewValue(b, prefix) == 
  /\ \E v \in Values : ~ v \in Range(prefix)
  /\ LET v == CHOOSE v \in Values : ~ v \in Range(prefix)
         val == prefix \o <<v>>
         msg == [type |-> "2a", bal |-> b, val |-> val]
     IN Send2a(b, msg)

ProposePrefix(b, val) ==
  Send2a(b, [type |-> "2a", bal |-> b, val |-> val]) 

Phase2a(b) ==
  /\ QuorumExists(msgs, b, "1b")
  /\ LET prefix1a == ValueSelect(b)
         prefixProp == propVal[b]
         prefix == IF Prefix(prefix1a, prefixProp) THEN prefixProp ELSE prefix1a
     IN \/ ProposeNewValue(b, prefix)
        \/ ProposePrefix(b, prefix)
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Phase2b(a) ==
  \E m \in msgs :
    /\ m.type = "2a"
    /\ m.bal >= maxBal[a]
    /\ Prefix(maxVal[a], m.val)
    /\ Send([type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a])
    /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
    /\ maxBal'  = [maxBal EXCEPT ![a] = m.bal]
    /\ maxVal'  = [maxVal EXCEPT ![a] = m.val]
    /\ UNCHANGED <<propVal>>

Next == \/ \E b \in Ballots   : Phase1a(b) \/ Phase2a(b)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

\* A prefix is committed if a p2 quorum exists of responses where it is a prefix
\* Thus this is the set of values which could be committed within a ballot number
\*   Hence we form the set of possible quorums
\*   And find the largest prefix they could be used to commit (ie the smallest value in those messages)
ValueCommits(b) ==
  LET qms == LET ms == SUBSET {m \in msgs : (m.type = "2b") /\ (m.bal = b)}
             IN {s \in ms: QuorumExists(s, b, "2b")}
      minV(q) == LET vs == {m.val : m \in q} IN CHOOSE v \in vs: \A v1 \in vs: Prefix(v, v1)
  IN {minV(q): q \in qms}

\* Consistency is satisified if for all values that could be committed in a ballot,
\*   for each subsequent ballot, every value they could commit has the first value as a prefix
\* i.e. if you commit a list, it will be a prefix of all other committed lists
Consistency ==
  \A b1, b2 \in Ballots : 
    b1 < b2 => \A v1 \in ValueCommits(b1): 
               \A v2 \in ValueCommits(b2):
          	         Prefix(v1, v2)

=============================================================================

----------------------------- MODULE MultiPaxos -----------------------------

EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS Ballots, Acceptors, Values, Quorums

VARIABLES   msgs,
            acc,
            prop,
            commits

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

Messages ==      [type : {"1a"}, bal : Ballots]
            \cup [type : {"1b"}, bal : Ballots, 
                    maxVBal : Ballots \cup {-1}, maxVal : PossibleValues, maxTS : Nat,
                    acc : Acceptors]
            \cup [type : {"2a"}, bal : Ballots, val : PossibleValues, ts : Nat]
            \cup [type : {"2b"}, bal : Ballots, val : PossibleValues, acc : Acceptors, ts : Nat]

ProposerState == [val : PossibleValues, counter : Nat]

AcceptorState == [maxBal : Ballots \cup {-1},
                  maxVBal: Ballots \cup {-1},
                  maxVal : PossibleValues,
                  maxTS : Nat]

TypeInvariant == /\ msgs \in SUBSET Messages
                 /\ acc \in [Acceptors -> AcceptorState]
                 /\ \A a \in Acceptors : acc[a].maxBal >= acc[a].maxVBal
                 /\ prop \in [Ballots -> ProposerState]
                 /\ \A v \in Range(commits) : v \in [bal : Ballots, val : PossibleValues]

vars == <<msgs, acc, prop, commits>>

-----------------------------------------------------------------------------

Init == /\ msgs = {}
        /\ acc = [a \in Acceptors |-> 
                   [maxVBal |-> -1, maxBal |-> -1, maxVal |-> << >>, maxTS |-> 0]]
        /\ prop = [b \in Ballots |-> [val |-> << >>, counter |-> 0]]
        /\ commits = << >>

Send(m) == msgs' = msgs \cup {m}

Phase1a(b) == 
  /\ ~\E m \in msgs: m.type = "1a" /\ m.bal = b
  /\ Send ([type |-> "1a", bal |-> b])
  /\ UNCHANGED << acc, prop, commits >>

Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.bal > acc[a].maxBal
    /\ Send([type |-> "1b", acc |-> a, 
             bal |-> m.bal, maxVBal |-> acc[a].maxVBal, maxVal |-> acc[a].maxVal, maxTS |-> acc[a].maxTS])
    /\ acc' = [acc EXCEPT ![a] = [acc[a] EXCEPT !.maxBal = m.bal]]
    /\ UNCHANGED << prop, commits >>

QuorumExists(s, b, type) ==
  \E Q \in Quorums:
    \A a \in Q : \E m \in s : (m.type = type) /\ m.acc = a /\ (m.bal = b)

ValueSelect(b) ==
  LET s == {m \in msgs : (m.type = "1b") /\ (m.bal = b)}
      svb == {m.maxVBal: m \in s}
      c == Max(LAMBDA x,y: x <= y, svb)
      r == {m \in s: m.maxVBal = c}
      m == Max(LAMBDA x,y: x.maxTS <= y.maxTS, r)
  IN m.maxVal

Phase2a(b) ==
  /\ QuorumExists(msgs, b, "1b")
  /\ LET prefix == IF prop[b].val /= << >> THEN prop[b].val ELSE ValueSelect(b)
         postfixOptions == {<<>>} \cup {<<v>> : v \in Values \ Range(prefix)}
     IN \E v \in postfixOptions:
          LET val == prefix \o v
              ts == prop[b].counter + 1
              msg == [type |-> "2a", bal |-> b, val |-> val, ts |-> ts]
          IN 
          /\ ~\E m \in msgs: m.type = "2a" /\ m.bal = b /\ m.val = val
          /\ Send(msg)
          /\ prop' = [prop EXCEPT ![b] = [val |-> val, counter |-> ts]]
  /\ UNCHANGED << acc, commits >>

Phase2b(a) ==
  /\ \E m \in msgs :
      /\ m.type = "2a"
      /\ m.bal >= acc[a].maxBal
      /\ Prefix(acc[a].maxVal, m.val)
      /\ Send([type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a, ts |-> m.ts])
      /\ acc' = [acc EXCEPT ![a] = [maxBal |-> m.bal, maxVBal |-> m.bal, maxVal |-> m.val, maxTS |-> m.ts]]
  /\ UNCHANGED << prop, commits >>

\* Try and commit a prefix
\*   Take the maximum ts for each acceptor, for each subset of messages which form a quorum, 
\*   and then the largest common prefix of those msgs
Commit(b) ==
  /\ QuorumExists(msgs, b, "2b")
  /\ LET LeqTS(ma,mb) == ma.ts =< mb.ts
         \* Every phase 2b message for this ballot
         ms == {m \in msgs: m.type = "2b" /\ m.bal = b}
         \* The newest message for each acceptor
         ams == {Max(LeqTS, {m \in ms: m.acc = a}): a \in {a \in Acceptors: \E m \in ms: m.acc = a}}
         \* Index ams on acceptors
         fams(a) == CHOOSE m \in ams: m.acc = a
         relevantQuorums == {q \in Quorums: \A a \in q: \E m \in ams: m.acc = a}
         \* The messages for each quorum
         qams == {{fams(a): a \in q} : q \in relevantQuorums}
         \* The value decided in each quorum
         qvs == {Min(Prefix, {m.val: m \in qms}): qms \in qams}
         \* The largest decided value
         v == Max(Prefix, qvs)
         commit == [bal |-> b, val |-> v]
     IN /\ ~ commit \in Range(commits)
        /\ commits' = commits \o << commit >>
        /\ UNCHANGED << msgs, acc, prop >>

Next == \/ \E b \in Ballots   : Phase1a(b) \/ Phase2a(b) \/ Commit(b)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

Consistency ==
  \A i, j \in DOMAIN(commits):
    /\ i < j
    /\ commits[i].bal <= commits[j].bal
    => Prefix(commits[i].val, commits[j].val)

=============================================================================

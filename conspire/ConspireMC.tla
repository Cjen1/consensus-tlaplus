---- MODULE ConspireMC ----
EXTENDS Conspire

UsedBallotNumbers == 
  {m.num: m \in msg.req} \union
  {m.bal.num: m \in msg.ack} \union
  {m.balnum: m \in msg.ack} \union
  Range(prop_balnum) \union
  Range(acc_maxBal) \union
  {b.num : b \in Range(acc_maxVBal)}

\* A ballot can be committed in b if there exists a quorum of responses for larger values
\* This can be extended to the consecutive ballots thingy-mabob
Committable(v, b) ==
  \E Q \in Quorums:
  \A a \in Q: \E m \in msg.ack: 
    /\ m.src = a
    /\ m.bal.num = b
    /\ LEQ(v, m.bal.val)

Serialised ==
  \A v1, v2 \in UsedValues:
    /\ (/\ \E b \in UsedBallotNumbers: Committable(v1, b)
        /\ \E b \in UsedBallotNumbers: Committable(v2, b)
       ) => \/ LEQ(v1, v2)
            \/ LEQ(v2, v1)

Inv == 
 /\ Serialised 

Symmetry == Permutations(Proposers) \union Permutations(Acceptors)

====

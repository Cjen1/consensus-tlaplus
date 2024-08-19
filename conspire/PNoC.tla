---- MODULE PNoC ----

EXTENDS Apalache, TLC, FiniteSets, Integers

(*
@typeAlias: value = Str;
@typeAlias: vvalue = Set($value);
@typeAlias: rid = Str;
@typeAlias: vote = {term : Int, value: $vvalue};
*)
PNoCAliases == TRUE

CONSTANTS
  \* @type: Set($rid);
  RIDs,
  \* @type: Set($value);
  CliVals

VARIABLES
  \* @type: $rid -> $vote;
  Replicas,
  \* @type: Set({src: $rid, vote: $vote}); 
  Votes,
  \* @type: Set($vote);
  Proposals

vars == << Proposals, Replicas, Votes >>

MaxCommitQuorums == {s \in SUBSET RIDs: Cardinality(s) >= (Cardinality(RIDs) * 3) \div 4}
CommitQuorums == {q \in MaxCommitQuorums: ~\E s \in MaxCommitQuorums: s \subseteq q /\ s /= q}
ProposalQuorums == {s \in SUBSET RIDs: /\ \A q \in CommitQuorums: s \intersect q /= {}
                                       /\ Cardinality(s) >= (Cardinality(RIDs) \div 2) + 1}

Init == 
/\ Proposals := {[value |-> {v}, term |-> 0] : v \in CliVals}
/\ Votes := {}
/\ Replicas := [r \in RIDs |-> [value |-> {}, term |-> -1]] 

Vote(r) ==
\E p \in Proposals:
/\ p.term > Replicas[r].term
/\ Replicas' = [Replicas EXCEPT ![r] = p]
/\ Votes' = Votes \union {[src |-> r, vote |-> p]}
/\ UNCHANGED << Proposals >>

Terms == {p.term: p \in Proposals}
Values == { p.value: p \in Proposals}

ProposeVals ==
\E t \in Terms:
\* large number of possible subsets result in the same proposal => reduce explicit states here
LET term_votes == {v \in Votes: v.vote.term = t}
    vote_rel == [r \in {v.src : v \in term_votes} |-> CHOOSE v \in term_votes: v.src = r]
    usable_qs == {q \in ProposalQuorums: q \ DOMAIN vote_rel = {}}
    AllPNoC(q) ==
      LET qvotes == {v \in Votes: v.src \in q} IN
      \A v \in {v.vote.value: v \in qvotes}:
      \* Not committable
      \A cq \in CommitQuorums:
      \E r \in cq: r \in DOMAIN vote_rel /\ vote_rel[r].vote.value /= v
    all_pnoc_qs == {q \in usable_qs: AllPNoC(q)}
    propable_vs == {UNION {vote_rel[r].vote.value : r \in q}: q \in all_pnoc_qs}
IN \E v \in propable_vs:
   LET new_prop == [term |-> t + 1, value |-> v] IN
   /\ new_prop \notin Proposals
   /\ Proposals' = Proposals \union {new_prop} 
   /\ UNCHANGED << Replicas, Votes >>

Next == 
\/ ProposeVals
\/ \E r \in RIDs: Vote(r)

Spec == Init /\ [][Next]_vars

Symmetry == Permutations(RIDs) \union Permutations(CliVals)

\* There is at most one vote per term for each replica
InvOneVotePerTerm ==
\A t \in Terms:
LET term_votes == {v \in Votes: v.vote.term = t} IN
Cardinality(term_votes) = Cardinality({v.src : v \in term_votes})

IsCommittable(v) ==
\E t \in Terms:
\E q \in CommitQuorums:
{[src |-> r, vote |-> [term |-> t, value |-> v]] : r \in q} \subseteq Votes

Committable == {v \in Values: IsCommittable(v)}

InvSafety == Cardinality(Committable) <= 1

InvCommit == \A v \in Committable: Cardinality(v) = 3
InvTermLimit == \A p \in Proposals: p.term < Cardinality(Values) + 1

====

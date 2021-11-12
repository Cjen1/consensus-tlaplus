---- MODULE Finite ----

EXTENDS Safe

RECURSIVE RemoveDeps(_,_)
RemoveDeps(b, to_remove) ==
  IF b = InitBalNum
  THEN b
  ELSE << b[1], {RemoveDeps(b1, to_remove) : b1 \in b[2] \ to_remove} >>

GCMsgs(unused) ==
  LET pruned1a1bnack == {m \in msgs: 
                          /\ m.type \in {"1a", "1b", "nack"}
		          /\ m.balNum \notin unused}
      clean1a1bnack == {[m EXCEPT !.balNum = RemoveDeps(m.balNum, unused)] :m \in pruned1a1bnack}
      pruned2a2b == {m \in msgs:
                      /\ m.type \in {"2a", "2b"}
		      /\ m.bal.bal \notin unused}
      clean2a2b == {[m EXCEPT !.bal = [val |-> m.bal.val, bal |-> RemoveDeps(m.bal.bal, unused)]] :m \in pruned2a2b}
  IN clean1a1bnack \cup clean2a2b
                    

GC ==
  LET unusedBals == UNION {RepBals(b) : b \in MessageBallotNumbers} \ (NodeBallotNumbers \cup {InitBalNum})
  IN /\ msgs' = GCMsgs(unusedBals)
     /\ prop' = [p \in Proposers |-> [prop[p] EXCEPT !.balNum = RemoveDeps(prop[p].balNum, unusedBals)]]
     /\ acc' = [a \in Acceptors |-> [maxBalNum |-> RemoveDeps(acc[a].maxBalNum, unusedBals),
                                     maxBal |-> [val |-> acc[a].maxBal.val, bal |-> RemoveDeps(acc[a].maxBal.bal, unusedBals)]]]
     /\ commit' = commit

VARIABLES do_gc

GCNext == \/ /\ do_gc
             /\ GC
	     /\ do_gc' = FALSE
	  \/ /\ ~do_gc
	     /\ ConsNext
	     /\ do_gc' = TRUE

FiniteSpec == /\ Init
              /\ commit = None
	      /\ do_gc = FALSE
	      /\ [][GCNext]_(vars \o << commit, do_gc >>)

DepthInvariant ==
  MaxBallotDepth <= Cardinality(Proposers) + 2 * Cardinality(Acceptors)
                                                
=============================================================================

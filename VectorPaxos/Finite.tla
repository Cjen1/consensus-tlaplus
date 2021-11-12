---- MODULE Finite ----

EXTENDS Safe

RECURSIVE RemoveDeps(_,_)
RemoveDeps(b, to_remove) ==
  IF b = InitBalNum
  THEN b
  ELSE << b[1], {RemoveDeps(b1, to_remove) : b1 \in b[2] \ to_remove} >>

GCMsgs(unused) ==
  LET pruned1anack == {m \in msgs:
                          /\ m.type \in {"1a", "nack"}
			  /\ m.balNum \notin unused}
      clean1anack == {[m EXCEPT !.balNum = RemoveDeps(m.balNum, unused)] :m \in pruned1anack}
      pruned1b == {m \in msgs:
                       /\ m.type = "1b"
		       /\ m.balNum \notin unused
		       /\ m.maxBal.bal \notin unused}
      clean1b == {[m EXCEPT !.balNum = RemoveDeps(m.balNum, unused),
                              !.maxBal = [val |-> m.maxBal.val, bal |-> RemoveDeps(m.maxBal.bal, unused)]]:
		    m \in pruned1b}
      pruned2a2b == {m \in msgs:
                      /\ m.type \in {"2a", "2b"}
		      /\ m.bal.bal \notin unused}
      clean2a2b == {[m EXCEPT !.bal = [val |-> m.bal.val, bal |-> RemoveDeps(m.bal.bal, unused)]] :m \in pruned2a2b}
  IN clean1anack \cup clean1b \cup clean2a2b
                    

VARIABLES do_gc, removed

GC ==
  LET unusedBals == UNION {RepBals(b) : b \in MessageBallotNumbers} \ (NodeBallotNumbers \cup {InitBalNum})
  IN /\ removed' = unusedBals
     /\ msgs' = GCMsgs(unusedBals)
     /\ prop' = [p \in Proposers |-> [prop[p] EXCEPT !.balNum = RemoveDeps(prop[p].balNum, unusedBals)]]
     /\ acc' = [a \in Acceptors |-> [maxBalNum |-> RemoveDeps(acc[a].maxBalNum, unusedBals),
                                     maxBal |-> [val |-> acc[a].maxBal.val, bal |-> RemoveDeps(acc[a].maxBal.bal, unusedBals)]]]
     /\ commit' = commit

GCNext == \/ /\ do_gc
             /\ GC
	     /\ do_gc' = FALSE
	  \/ /\ ~do_gc
	     /\ ConsNext
	     /\ removed' = {}
	     /\ do_gc' = TRUE

FiniteSpec == /\ Init
              /\ commit = None
	      /\ do_gc = FALSE /\ removed = {}
	      /\ [][GCNext]_(vars \o << commit, do_gc, removed >>)

DepthInvariant ==
  MaxBallotDepth <= Cardinality(Proposers) + 2 * Cardinality(Acceptors)
                                                
=============================================================================

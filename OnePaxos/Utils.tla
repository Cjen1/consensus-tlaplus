---- MODULE Utils ----

EXTENDS Sequences, FiniteSets, Integers

max(LEQ(_,_), S) == CHOOSE v \in S: \A v1 \in S: LEQ(v1, v)

Range(seq) == {seq[i] : i \in DOMAIN(seq)}

(* All possible sequences from a set of items. *)
AllSeqFromSet(S) ==
  LET unique(f) == \A i,j \in DOMAIN f: i /= j => f[i] /= f[j]
      subseq(c) == {seq \in [1..c -> S]: unique(seq)}
  IN
  UNION {subseq(c): c \in 0..Cardinality(S)}

====

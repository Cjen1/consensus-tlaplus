---- MODULE AbstractMC ----

EXTENDS Apalache, Abstract

CInit ==
  /\ Nodes := {"a1", "a2", "a3", "a4"}
  /\ Values := {"x", "y", "z"}
  /\ None := "None"

Inv == 
 /\ Safety 

====

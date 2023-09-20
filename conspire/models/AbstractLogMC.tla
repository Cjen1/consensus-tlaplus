---- MODULE AbstractLogMC ----

EXTENDS AbstractLog

CInit ==
  /\ Nodes = {"a1", "a2", "a3", "a4"}
  /\ Values = {"x", "y", "z"}

Inv == 
 /\ Safety 

====

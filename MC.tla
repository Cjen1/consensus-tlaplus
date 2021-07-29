---- MODULE MC ----
EXTENDS MultiPaxos, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT definitions Acceptors
const_162756951828110000 == 
{a1, a2, a3}
----

\* SYMMETRY definition
symm_162756951828111000 == 
Permutations(const_162756951828110000)
----

\* CONSTANT definitions @modelParameterConstants:0Ballots
const_162756951828112000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1Quorums
const_162756951828113000 == 
{{a1,a2},{a2,a3},{a3,a1}}
----

\* CONSTANT definitions @modelParameterConstants:2Values
const_162756951828114000 == 
{1,2,3}
----

=============================================================================
\* Modification History
\* Created Thu Jul 29 15:38:38 BST 2021 by cjen1

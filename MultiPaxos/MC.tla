---- MODULE MC ----
EXTENDS MultiPaxos, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT definitions Values
const_16285966784012000 == 
{v1, v2}
----

\* MV CONSTANT definitions Acceptors
const_16285966784013000 == 
{a1, a2, a3}
----

\* SYMMETRY definition
symm_16285966784014000 == 
Permutations(const_16285966784012000) \union Permutations(const_16285966784013000)
----

\* CONSTANT definitions @modelParameterConstants:0Ballots
const_16285966784015000 == 
{1,2,3,4}
----

\* CONSTANT definitions @modelParameterConstants:1Quorums
const_16285966784016000 == 
{{a1,a2},{a2,a3},{a3,a1}}
----

=============================================================================
\* Modification History
\* Created Tue Aug 10 12:57:58 BST 2021 by cjen1

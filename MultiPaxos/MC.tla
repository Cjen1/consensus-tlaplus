---- MODULE MC ----
EXTENDS MultiPaxos, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT definitions Values
const_1629302032521219000 == 
{v1, v2}
----

\* MV CONSTANT definitions Acceptors
const_1629302032521220000 == 
{a1, a2, a3}
----

\* SYMMETRY definition
symm_1629302032521221000 == 
Permutations(const_1629302032521219000) \union Permutations(const_1629302032521220000)
----

\* CONSTANT definitions @modelParameterConstants:0Ballots
const_1629302032521222000 == 
{1,2}
----

\* CONSTANT definitions @modelParameterConstants:1Quorums
const_1629302032521223000 == 
{{a1,a2},{a2,a3},{a3,a1}}
----

=============================================================================
\* Modification History
\* Created Wed Aug 18 16:53:52 BST 2021 by cjen1

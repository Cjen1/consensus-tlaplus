---- MODULE MC ----
EXTENDS LogPaxos, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT definitions Values
const_1631037570427200000 == 
{v1, v2}
----

\* MV CONSTANT definitions Acceptors
const_1631037570427201000 == 
{a1, a2, a3}
----

\* SYMMETRY definition
symm_1631037570427202000 == 
Permutations(const_1631037570427200000) \union Permutations(const_1631037570427201000)
----

\* CONSTANT definitions @modelParameterConstants:0Quorums
const_1631037570427203000 == 
{{a1,a2},{a2,a3},{a3,a1}}
----

\* CONSTANT definitions @modelParameterConstants:3BallotNumbers
const_1631037570427204000 == 
{1,2}
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_1631037570427206000 ==
[][ProposerConsistency]_prop
----
=============================================================================
\* Modification History
\* Created Tue Sep 07 18:59:30 BST 2021 by cjjen

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
const_163102845479584000 == 
{v1, v2}
----

\* MV CONSTANT definitions Acceptors
const_163102845479585000 == 
{a1, a2, a3}
----

\* SYMMETRY definition
symm_163102845479586000 == 
Permutations(const_163102845479584000) \union Permutations(const_163102845479585000)
----

\* CONSTANT definitions @modelParameterConstants:0Ballots
const_163102845479587000 == 
{1,2}
----

\* CONSTANT definitions @modelParameterConstants:1Quorums
const_163102845479588000 == 
{{a1,a2},{a2,a3},{a3,a1}}
----

=============================================================================
\* Modification History
\* Created Tue Sep 07 16:27:34 BST 2021 by cjjen

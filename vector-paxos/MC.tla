---- MODULE MC ----
EXTENDS Paxos, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT definitions Values
const_163118455825621000 == 
{v1, v2}
----

\* MV CONSTANT definitions Acceptors
const_163118455825622000 == 
{a1, a2, a3}
----

\* SYMMETRY definition
symm_163118455825623000 == 
Permutations(const_163118455825621000) \union Permutations(const_163118455825622000)
----

\* CONSTANT definitions @modelParameterConstants:0Quorums
const_163118455825624000 == 
{{a1,a2}, {a2,a3}, {a3,a1}}
----

\* CONSTANT definitions @modelParameterConstants:1BallotNumbers
const_163118455825625000 == 
{1,2}
----

=============================================================================
\* Modification History
\* Created Thu Sep 09 11:49:18 BST 2021 by cjen1

---- MODULE TSafe ----

EXTENDS Tempo, TLC

CONSTANTS MaxRound, MaxTS

FiniteRounds == 0..MaxRound

FiniteTimeStamps == 1..MaxTS

Symmetry == Permutations(Commands) \union Permutations(Acceptors) 

====

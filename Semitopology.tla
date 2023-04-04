--------------------- MODULE Semitopology ---------------------

CONSTANTS
    P \* the set of points
  , Open \* the set of open sets

\* The set of opens is closed under arbitrary unions:
ASSUME \A O \in SUBSET Open : UNION O \in Open

\* The closure of a set S is the set of points whose open neighborhoods all intersect S:
Closure(S) ==
    {p \in P : \A O \in Open : p \in O => O \cap S # {}}

=============================================================================
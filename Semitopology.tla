--------------------- MODULE Semitopology ---------------------

CONSTANTS
    P \* the set of points
  , Open \* the set of open sets

\* {} and P are opens:
ASSUME {} \in Open /\ P \in Open
\* The set of opens is closed under arbitrary unions:
ASSUME \A O \in SUBSET Open : UNION O \in Open

\* The closure of a set S is the set of points whose open neighborhoods all intersect S:
Closure(S) ==
    {p \in P : \A O \in Open : p \in O => O \cap S # {}}
        
Transitive(S) == \A O1, O2 \in Open :
    /\ O1 \cap S # {}
    /\ O2 \cap S # {}
    => O1 \cap O2 # {}

Topen(S) == S \in Open /\ Transitive(S)

\* An important theorem for distributed algorithms:
THEOREM \A S \in SUBSET P, O \in Open :
    Topen(S) /\ S \cap O # {} => S \subseteq Closure(O)


=============================================================================
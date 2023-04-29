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

Closed(C) == Closure(C) = C

Transitive(S) == \A O1, O2 \in Open :
    /\ O1 \cap S # {}
    /\ O2 \cap S # {}
    => O1 \cap O2 # {}

StronglyTransitive(S) ==\A O1, O2 \in Open :
    /\ O1 \cap S # {}
    /\ O2 \cap S # {}
    => O1 \cap O2 \cap S # {}

Topen(S) == S \in Open /\ Transitive(S)

StrongTopen(S) == S \in Open /\ StronglyTransitive(S)

(**********************************************************************************)
(* Notion of resilient set discussed with Jamie on 4.28.2023                      *)
(*                                                                                *)
(* This is a set that remains topen despite malicious nodes crafting their slices *)
(* in the worse way possible as long as the failure assumptions of all the        *)
(* non-failed members of S are satisfied.                                         *)
(**********************************************************************************)
Resilient(U) == 
    /\ U \in Open 
    /\ \A C \in SUBSET P : Closed(C) => StrongTopen(U \ C)

\* A few conjectures

Conjecture1 == \A U1,U2 \in SUBSET P :
    Resilient(U1) /\ Resilient(U2) /\ U1 \cap U2 # {} =>
        Resilient(U1 \cup U2)

Conjecture2 == \A U \in SUBSET P, O \in Open :
    Resilient(U) /\ U \cap O # {} => U \subseteq Closure(O)


=============================================================================
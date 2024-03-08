---------------- MODULE TLCFastConsensus ------------------------

EXTENDS TLC, FiniteSets, Integers

CONSTANTS v1, v2, p1, p2, p3, p4

V == {v1, v2} 
P == {p1, p2, p3, p4}
Quorum == {Q \in SUBSET P : 3*Cardinality(Q) > 2*Cardinality(P)}
Blocking == {Bl \in SUBSET P : 3*Cardinality(Bl) > Cardinality(P)}
B == {p1}
Leader(r) == p2

Sym == Permutations(P\B) \cup Permutations(V)

VARIABLES votes, proposals, round

INSTANCE FastConsensus

=====================================================================
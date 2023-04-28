--------------------- MODULE BrachaBroadcastMC ----------------

\* TLC configuration for BrachaBroadcast

EXTENDS BrachaBroadcast, FiniteSets, Naturals, TLC

CONSTANTS p1, p2, p3, p4, v1, v2

P_MC == {p1,p2,p3,p4}
Open_MC == {O \in SUBSET P_MC : 3*Cardinality(O) > 2*Cardinality(P_MC)} \cup {{}}
l_MC == p1
V_MC == {v1,v2}
B_MC == {p4}
U_MC == P_MC

===============================================================
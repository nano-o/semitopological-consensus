--------------------- MODULE MCConsensusAlgo ---------------------

EXTENDS ConsensusAlgo

\* Model-checker setup for Voting.tla

CONSTANTS v1, v2, p1, p2, p3

V_MC == {v1, v2}
P_MC == {p1, p2, p3}
Quorum_MC == {{p1,p2}, {p2,p3}, {}, P}
T_MC == P
Round_MC == 0..2
Leader_MC(p, r) == p1

NoDecision == \A p \in P : decision[p] = {}

\* TODO: why does this not work? TypeOkay breaks
\* RoundConstraint == \A p \in P : round'[p] \in Round
RoundConstraint == \A p \in P : round[p] <= 1

=========================================================
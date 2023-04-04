--------------------- MODULE VotingMC ---------------------

EXTENDS Voting

\* Model-checker setup for Voting.tla

CONSTANTS v1, v2, p1, p2, p3

V_MC == {v1, v2}
P_MC == {p1, p2, p3}
Quorum_MC == {{p1,p2}, {p2,p3}, {}, P}
T_MC == P
Nat_MC == {0,1,2}
NoDecision == \A p \in P : decided[p] = {}
DecisionInRound2 == 
    /\ \E p \in P, v \in V : <<2,v>> \in decided[p]
    /\ \A p \in P, v \in V : <<1,v>> \notin decided[p]
NegDecisionInRound2 == \neg DecisionInRound2


RoundConstraint == \A p \in P : round'[p] \in Rounds

=========================================================
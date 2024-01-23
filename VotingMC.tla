--------------------- MODULE VotingMC ---------------------

EXTENDS Voting, TLC

\* Model-checker setup for Voting.tla

CONSTANTS v1, v2, p1, p2, p3, p4

V_MC == {v1, v2}
defaultV_MC == v1
P_MC == {p1, p2, p3, p4}
Quorum_MC == {{p1,p2,p3}, {p2,p3,p4}, {}, P}
T_MC == P
B_MC == {p1}
Nat_MC == 0..3

Sym == Permutations(P_MC) \cup Permutations(V_MC)

NoDecision == \A p \in P : decided[p] = {}
\* some process votes in phase 4 of round 0 but there is no decision in round 0;
\* then there is a decision in round 1:
DecisionInRound1 == 
    /\ \E p \in P, v \in V : <<1,v>> \in decided[p]
    /\ \A p \in P, v \in V : <<0,v>> \notin decided[p]
    /\ \E p \in P, v \in V : [round |-> 0, phase |-> 4, value |-> v] \in votes[p]
NegDecisionInRound1 == \neg DecisionInRound1
\* some process votes in phase 4 of round 0 but there is no decision in round 0;
\* then there is a decision in round 1 for a different value:
DecisionInRound1ConflictsVote3InRound2 == \E w1,w2 \in V :
    /\ w1 # w2
    /\ \E p \in P : <<1,w1>> \in decided[p]
    /\ \A p \in P, w \in V : <<0,w>> \notin decided[p]
    /\ \E p \in P : [round |-> 0, phase |-> 4, value |-> w2] \in votes[p]
NegDecisionInRound1ConflictsVote3InRound2 == \neg DecisionInRound1ConflictsVote3InRound2
VoteInRound1 ==
    \E p \in P, v \in V : [round |-> 1, value |-> v, phase |-> 4] \in votes[p]
NegVoteInRound1 == \neg VoteInRound1


RoundConstraint == \A p \in P : round'[p] \in Round

=========================================================
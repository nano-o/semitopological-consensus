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

NoDecision == \A p \in P : decided[p] = {}

Refinement == Voting!Spec

DecisionInRound1 == 
    /\ \E p \in P, v \in Value : <<1,v>> \in decided[p]
    /\ \A p \in P, v \in Value : <<0,v>> \notin decided[p]
    /\ \E p \in P, v \in Value : [round |-> 0, phase |-> 4, value |-> v] \in votes_[p]
NegDecisionInRound1 == \neg DecisionInRound1

DecisionInRound2 == \E w1,w2 \in Value :
    /\ w1 # w2
    /\ \E p \in P, v \in Value : <<2,w1>> \in decided[p]
    /\ \A p \in P, v \in Value : <<0,v>> \notin decided[p]
    /\ \A p \in P, v \in Value : <<1,v>> \notin decided[p]
    /\ \E p \in P, v \in Value : [round |-> 0, phase |-> 3, value |-> w1] \in votes_[p]
    /\ \E p \in P, v \in Value : [round |-> 1, phase |-> 3, value |-> w2] \in votes_[p]
NegDecisionInRound2 == \neg DecisionInRound2

DecisionInRound1ConflictsVote3InRound2 == \E w1,w2 \in Value :
    /\ w1 # w2
    /\ \E p \in P : <<1,w1>> \in decided[p]
    /\ \A p \in P, w \in Value : <<0,w>> \notin decided[p]
    /\ \E p \in P : [round |-> 0, phase |-> 3, value |-> w2] \in votes_[p] \* NOTE: if we require a vote4 then we can't have a quorum no reporting a vote 3 for w1
NegDecisionInRound1ConflictsVote3InRound2 == \neg DecisionInRound1ConflictsVote3InRound2

Test == \E w1,w2 \in Value :
    /\ w1 # w2
    \* /\ \E p \in P, v \in Value : <<1,v>> \in decided[p]
    /\ \E p \in P : round[p] = 1 /\ phase[p] = "propose"
    /\ \E Q \in Quorum : p1 \in Q /\ \A q \in Q : \E m \in network : m.src = q /\ m.type = "suggest"
    \* /\ \E m \in network : m.type = "proposal" /\ m.round = 1
    \* /\ \E p \in P, v \in Value : [round |-> 1, phase |-> 1, value |-> v] \in votes_[p]
    /\ \E p \in P, v \in Value : [round |-> 0, phase |-> 4, value |-> v] \in votes_[p]
NegTest == \neg Test

RoundConstraint == \A p \in P : round[p] <= 1

Debug ==
    IF \E Q \in Quorum :
        /\ p1 \in Q
        /\ \A q \in Q : round[q] = 1 /\ phase[q] = "vote1"
    THEN TRUE
    ELSE TRUE

=========================================================
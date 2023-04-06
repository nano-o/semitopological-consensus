--------------------- MODULE VotingLiveness ---------------------

EXTENDS Integers

CONSTANTS
    Value \* the set of values to decide on
  , P \* the set of processes
  , Quorum \* the set of quorums
  , T \* a topen
  , GoodRound \* A good round in which all processes should decide

VARIABLES votes, round, decided
vars == <<round, votes, decided>>

\* we instantiate the voting module:
Voting == INSTANCE Voting

ASSUME GoodRound \in Voting!Round

(***********************************************************************************)
(* To check liveness, we are going to assume that the round `GoodRound' lasts long *)
(* enough (i.e. forever) and all processes in `T' vote for the same value `v' and  *)
(* `v' satisfies the condition that the leader uses in the real algorithm to       *)
(* propose a value.                                                                *)
(***********************************************************************************)
GoodRoundSpec == \A p \in P :
    /\ round'[p] <= GoodRound
    /\ \A v \in votes'[p] : v.round = GoodRound /\ v.phase = 1 =>
        Voting!SafeAt(v.value, GoodRound, p, 3, 2)
    /\ \A p1,p2 \in P : \A v1 \in votes'[p1] : \A v2 \in votes'[p2] :
         v1.round = GoodRound /\ v2.round = GoodRound => v1.value = v2.value

Next == Voting!Next /\ GoodRoundSpec

Spec == 
    /\ Voting!Init 
    /\ [][Voting!Next]_vars
    \* fairness constraints:
    /\ \A p \in P, v \in Value, r \in Voting!Round :
        /\ WF_vars(Voting!Vote1(p,v,r))
        /\ WF_vars(Voting!Vote2(p,v,r))
        /\ WF_vars(Voting!Vote3(p,v,r))
        /\ WF_vars(Voting!Vote4(p,v,r))
        /\ WF_vars(Voting!Decide(p,v,r))
        /\ WF_vars(r < GoodRound /\ Voting!Timeout(p, r))

Liveness == \A p \in T : \E v \in Value : <>(<<GoodRound, v>> \in decided[p])

\* Liveness exhaustively checked with 3 processes, 2 non-trivial quorums of cardinatlity 2, and GoodRound=2.
\* Took 6 hours using 10 cores and 35GB of memory

=================================================================
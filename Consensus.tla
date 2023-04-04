--------------------- MODULE Consensus ---------------------

(**************************************************************************************************************)
(* This is a high-level specification of a consensus algorithm for a quorum system that forms a semitopology. *)
(* There is no network or messages at this level of abstraction.                                              *)
(**************************************************************************************************************)

EXTENDS Integers

CONSTANTS
    V \* the set of values to decide on
  , P \* the set of processes
  , Leader(_,_) \* Leader(p, r) is p's leader for round r
  , Quorum \* the set of quorums

INSTANCE Semitopology WITH
    P <- P,
    Open <- Quorum

\* The protocol starts at round 0 and the round number only increases. 
\* We use -1 as a special marker.
Rounds == Nat \union {-1}

Maximal(e, S) ==
    /\ e \in S
    /\ \A e1 \in S : Leq(e1,e)

\* A maximal element in the set S ordered by Leq(_,_), if such exists, and otherwise the default value provided:
Max(S, Leq(_,_), default) == 
    IF \E e \in S : Maximal(e, S)
    THEN CHOOSE e \in S : Maximal(e, S)
    ELSE default

Phases == 1..4
Vote == [rnd: Rounds, phase: Phases, val: V]
VoteArray == [P -> SUBSET Vote]
\* ordering on votes
Leq(v1, v2) ==
    \/ v1.round < v2.round
    \/ /\ v1.round = v2.round
       /\ v1.phase <= v2.phase

VARIABLES votes, round, decided

TypeOkay ==
    /\ votes \in VoteArray
    /\ round \in [P -> Nat]
    /\ decided \in SUBSET V

NotAVote == [round |-> -1] \* TODO: why not just a constant?

LargestVote(p, phase) ==
    LET vs == {v \in votes[p] : v.phase = phase} IN
      Max(vs, Leq, NotAVote)

SecondLargestVote(p, phase) ==
    LET vs == {v \in votes[p] : v.phase = phase} \ {LargestVote(p, phase)}
    IN Max(vs, Leq, NotAVote)

\* `v' is safe to vote for in round `r' according to the votes of process `p' in phase `phase':
ClaimsSafeAt(v, r, p, phase) ==
    \/ r = 0
    \/ LET mv == LargestVote(p, 1) IN
         /\ r <= mv.round
         /\ mv.val = v
    \/ r <= SecondLargestVote(p, 1).round

\* Whether value v is safe to vote for in round r by process p:
SafeAt(v, r, p) == \E Q \in Quorum :
    /\ p \in Q \* Q must be a quorum of p
    /\ \A q \in Q : round[q] > r
    /\ \/ \A q \in Q : LargestVote(q, 4).round

Init ==
    /\ votes = [p \in P |-> {}]
    /\ round = [p \in P |-> 0]
    /\ decided = {}

=============================================================================
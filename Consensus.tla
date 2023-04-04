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
  , NotAVote

INSTANCE Semitopology WITH
    P <- P,
    Open <- Quorum

\* The protocol starts at round 0 and the round number only increases.
Rounds == Nat
Phases == 1..4
\* A vote is case in a phase of a round and for a value:
Vote == [rnd: Rounds, phase: Phases, val: V]
ASSUME NotAVote \notin Vote
\* ordering on votes
Leq(v1, v2) ==
    \/ v1.round < v2.round
    \/ /\ v1.round = v2.round
       /\ v1.phase <= v2.phase

Maximal(e, S) ==
    /\ e \in S
    /\ \A e1 \in S : Leq(e1,e)

\* A maximal element in the set S ordered by Leq, if such exists, and otherwise the default value provided:
Max(S, default) == 
    IF \E e \in S : Maximal(e, S)
    THEN CHOOSE e \in S : Maximal(e, S)
    ELSE default

VARIABLES votes, round, decided

TypeOkay ==
    /\ votes \in [P -> SUBSET Vote]
    /\ round \in [P -> Nat]
    /\ decided \in SUBSET V

LargestVote(p, phase) ==
    LET vs == {v \in votes[p] : v.phase = phase} IN
      Max(vs, NotAVote)

SecondLargestVote(p, phase) ==
    LET vs == {v \in votes[p] : v.phase = phase} \ {LargestVote(p, phase)}
    IN Max(vs, NotAVote)

\* `v' is safe to vote for in round `r' according to the votes of process `p' in phase `phase':
ClaimsSafeAt(v, r, p, phase) ==
    \/ r = 0
    \/ LET mv == LargestVote(p, 1) IN
         /\ r <= mv.round
         /\ mv.val = v
    \/ r <= SecondLargestVote(p, 1).round

\* Whether value v is safe to vote for in round r by process p according to votes in phase `phase':
SafeAt(v, r, p) == \E Q \in Quorum :
    /\ p \in Q \* Q must be a quorum of p
    /\ \A q \in Q : round[q] > r
    /\ \/ \A q \in Q : LargestVote(q, 4).round

Init ==
    /\ votes = [p \in P |-> {}]
    /\ round = [p \in P |-> 0]
    /\ decided = {}

=============================================================================
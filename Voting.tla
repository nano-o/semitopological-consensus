--------------------- MODULE Voting ---------------------

(***********************************************************************************)
(* This is a high-level specification of a consensus algorithm for a quorum system *)
(* that forms a semitopology. There is no network, messages, or faults at this     *)
(* level of abstraction.                                                           *)
(***********************************************************************************)

EXTENDS Integers

CONSTANTS
    V \* the set of values to decide on
  , P \* the set of processes
  , Quorum \* the set of quorums
  , T \* a topen

INSTANCE Semitopology WITH
    P <- P,
    Open <- Quorum

\* We state the correctness properties of the algorithm with respect to an arbitrary topen `T':
ASSUME Topen(T)

\* The protocol starts at round 0 and the round number only increases:
Rounds == Nat
\* Each round consists of 4 phases:
Phases == 1..4
\* A vote is cast in a phase of a round and for a value:
Vote == [rnd: Rounds, phase: Phases, value: V]
\* `NotAVote' is a special constant that we use to indicate the absence of a vote.
\* Giving it a round field equal to -1 is convenient.
NotAVote == [rnd |-> -1]

\* `Leq' is a partial order on votes:
Leq(v1, v2) ==
    \/ v1.round < v2.round
    \/ /\ v1.round = v2.round
       /\ v1.phase <= v2.phase

\* Whether v is maximal in S
Maximal(v, S) ==
    /\ v \in S
    /\ \A v2 \in S : Leq(v2,v)

\* A maximal element in the set S ordered by Leq, if such exists, and otherwise the default value provided:
Max(S, default) == 
    IF \E e \in S : Maximal(e, S)
    THEN CHOOSE e \in S : Maximal(e, S)
    ELSE default

\* We now specify the behaviors of the algorithm:

VARIABLES votes, round, decided

TypeOkay ==
    /\ votes \in [P -> SUBSET Vote]
    /\ round \in [P -> Nat]
    /\ decided \in [P -> SUBSET V]

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
         /\ mv.value = v
    \/ r <= SecondLargestVote(p, 1).round

\* Whether value v is safe to vote for in round r by process p:
\* TODO: explain `phaseA' and `phaseB'
SafeAt(v, r, p, phaseA, phaseB) == \E Q \in Quorum :
    /\ p \in Q \* Q must be a quorum of p
    /\ \A q \in Q : round[q] >= r
    /\ \/ \A q \in Q : LargestVote(q, phaseA) = NotAVote \* members of Q never voted in phase 4 before round r
       \/ \E r2 \in Rounds :
         /\ r2 < r
         /\ \A q \in Q : LET lvq == LargestVote(q, phaseA) IN
           /\ lvq.round <= r2
           /\ lvq.round = r2 => lvq.value = v
         /\ \E S \in SUBSET P :
            /\ p \in Closure(S)
            /\ \A q \in S : ClaimsSafeAt(v, r, q, phaseB)

Init ==
    /\ votes = [p \in P |-> {}]
    /\ round = [p \in P |-> 0]
    /\ decided = [p \in P |-> {}]

Propose(p, v) ==
    TRUE

DoVote(p, v, r, phase) ==
    /\ votes' = [votes EXCEPT ![p] = @ \union [round |-> r, phase |-> phase, value |-> v]]
    /\ UNCHANGED <<decided, round>>
    
Vote1(p, v, r) ==
    /\ r = round[p]
    /\ SafeAt(v, r, p, 4, 1)
    /\ DoVote(p, v, r, 1)

\* whether v has been voted for by a quorum in phase `phase' of round `r':
Accepted(v, r, phase) ==
    /\ \E Q \in Quorum : \A q \in Q : [round |-> r, phase |-> phase, value |-> v] \in votes[q]

Vote2(p, v, r) ==
    /\ r = round[p]
    /\ Accepted(v, r, 1)
    /\ DoVote(p, v, r, 2)

Vote3(p, v, r) ==
    /\ r = round[p]
    /\ Accepted(v, r, 2)
    /\ DoVote(p, v, r, 3)

Vote4(p, v, r) ==
    /\ r = round[p]
    /\ Accepted(v, r, 3)
    /\ DoVote(p, v, r, 4)

Decide(p, v, r) ==
    /\ r = round[p]
    /\ Accepted(v, r, 4)
    /\ decided' = [decided EXCEPT ![p] = @ \union {v}]
    /\ UNCHANGED <<votes, round>>

Timeout(p) ==
    /\ round' = [round EXCEPT ![p] = @ + 1]

Next == \E p \in P, v \in V, r \in Rounds :
    \/ Vote1(p, v, r)
    \/ Vote2(p, v, r)
    \/ Vote3(p, v, r)
    \/ Vote4(p, v, r)
    \/ Decide(p, v, r)
    \/ Timeout(p)

vars == <<round, votes, decided>>

Spec == Init /\ [][Next]_vars

Safety == \A p,q \in T, v,w \in V :
    v \in decided[p] /\ w \in decided[q] => v = w

=============================================================================
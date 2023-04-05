--------------------- MODULE Voting ---------------------

(***********************************************************************************)
(* This is a high-level specification of a consensus algorithm for a quorum system *)
(* that forms a semitopology. There is no network, messages, or faults at this     *)
(* level of abstraction.                                                           *)
(***********************************************************************************)

EXTENDS Integers, FiniteSets

CONSTANTS
    V \* the set of values to decide on
  , P \* the set of processes
  , Quorum \* the set of quorums
  , T \* a topen
  , GoodRound \* A good round in which all processes should decide

INSTANCE Semitopology WITH
    P <- P,
    Open <- Quorum

\* We state the correctness properties of the algorithm with respect to an arbitrary topen `T':
ASSUME Topen(T)

\* The protocol starts at round 0 and the round number only increases:
Round == Nat
ASSUME GoodRound \in Round
\* Each round consists of 4 phases:
Phase == 1..4
\* A vote is cast in a phase of a round and for a value:
Vote == [round: Round, phase: Phase, value: V]
\* `NotAVote' is a special constant that we use to indicate the absence of a vote.
\* Giving it a round field equal to -1 is convenient.
NotAVote == [round |-> -1]

\* `Leq' is a partial order on votes:
Leq(v1, v2) ==
    \/ v1.round < v2.round
    \/ /\ v1.round = v2.round
        \* TODO: we probably don't need this second part:
       /\ v1.phase <= v2.phase

\* Whether v is maximal in S
Maximal(v, S) ==
    /\ v \in S
    /\ \A v2 \in S : Leq(v2,v)

(* `^\newpage^' *)

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
    /\ decided \in [P -> SUBSET (Round\times V)]

\* largest vote of p in phase `phase' before round r
LargestVote(p, phase, r) ==
    LET vs == {v \in votes[p] : v.phase = phase /\ v.round < r} IN
      Max(vs, NotAVote)

\* second largest vote of p in phase `phase' before round r
SecondLargestVote(p, phase, r) ==
    LET largest == LargestVote(p, phase, r)
        vs == {v \in votes[p] : v.phase = phase /\ v.round < r /\ v.value # largest.value}
    IN Max(vs, NotAVote)

\* `v' is safe in round `r2' according to the votes of process `p' in phase `phase' before round r:
ClaimsSafeAt(v, r, r2, p, phase) ==
    \/ r = 0
    \/ LET mv == LargestVote(p, 1, r) IN
         /\ r2 <= mv.round
         /\ mv.value = v
    \/ r2 <= SecondLargestVote(p, 1, r).round

\* continued on the next page...
(* `^\newpage^' *)

\* Whether value v is safe to vote for in round r by process p:
\* TODO: explain `phaseA' and `phaseB'
SafeAt(v, r, p, phaseA, phaseB) ==
    \/ r = 0
    \/ \E Q \in Quorum : 
        /\ p \in Q \* Q must be a quorum of p
        /\ \A q \in Q : round[q] >= r \* every member of Q is in round at least r
        /\  \/ \A q \in Q : LargestVote(q, phaseA, r) = NotAVote \* members of Q never voted before r
            \/ \E r2 \in Round :
                /\ r2 < r
                /\ \E q \in Q : LargestVote(q, phaseA, r).round = r2
                /\ \A q \in Q : LET lvq == LargestVote(q, phaseA, r) IN
                    /\ lvq.round <= r2
                    /\ lvq.round = r2 => lvq.value = v
                /\ \E S \in SUBSET P :
                    /\ p \in Closure(S)
                    /\ \A q \in S : ClaimsSafeAt(v, r, r2, q, phaseB)

Init ==
    /\ votes = [p \in P |-> {}]
    /\ round = [p \in P |-> 0]
    /\ decided = [p \in P |-> {}]

DoVote(p, v, r, phase) ==
    /\ \A w \in V : [round |-> r, phase |-> phase, value |-> w] \notin votes[p]
    /\ votes' = [votes EXCEPT ![p] = @ \union {[round |-> r, phase |-> phase, value |-> v]}]
    /\ UNCHANGED <<decided, round>>

Vote1(p, v, r) ==
    /\ r = round[p]
    /\ SafeAt(v, r, p, 4, 1)
    /\ DoVote(p, v, r, 1)

\* whether v has been voted for by a quorum of p in phase `phase' of round `r':
Accepted(p, v, r, phase) == \E Q \in Quorum :
    /\ p \in Q
    /\ \A q \in Q : [round |-> r, phase |-> phase, value |-> v] \in votes[q]

Vote2(p, v, r) ==
    /\ r = round[p]
    /\ Accepted(p, v, r, 1)
    /\ DoVote(p, v, r, 2)

(* `^\pagebreak^' *)

Vote3(p, v, r) ==
    /\ r = round[p]
    /\ Accepted(p, v, r, 2)
    /\ DoVote(p, v, r, 3)

Vote4(p, v, r) ==
    /\ r = round[p]
    /\ Accepted(p, v, r, 3)
    /\ DoVote(p, v, r, 4)

Decide(p, v, r) ==
    /\ r = round[p]
    /\ Accepted(p, v, r, 4)
    /\ \A w \in V : <<r, w>> \notin decided[p]
    /\ decided' = [decided EXCEPT ![p] = @ \union {<<r, v>>}]
    /\ UNCHANGED <<votes, round>>

Timeout(p, r) ==
    /\ r = round[p]
    /\ round' = [round EXCEPT ![p] = r + 1]
    /\ UNCHANGED <<votes, decided>>

(***********************************************************************************)
(* To check liveness, we are going to assume that the round `GoodRound' lasts long *)
(* enough (i.e. forever) and all processes in `T' vote for the same value `v' and  *)
(* `v' satisfies the condition that the leader uses in the real algorithm to       *)
(* propose a value.                                                                *)
(***********************************************************************************)
GoodRoundSpec == \A p \in P :
    /\ round'[p] <= GoodRound
    /\ \A v \in votes'[p] : v.round = GoodRound /\ v.phase = 1 =>
        SafeAt(v.value, GoodRound, p, 3, 2)
    /\ \A p1,p2 \in P : \A v1 \in votes'[p1] : \A v2 \in votes'[p2] :
         v1.round = GoodRound /\ v2.round = GoodRound => v1.value = v2.value

Next == 
    /\ \E p \in P, v \in V, r \in Round :
        \/ Vote1(p, v, r)
        \/ Vote2(p, v, r)
        \/ Vote3(p, v, r)
        \/ Vote4(p, v, r)
        \/ Decide(p, v, r)
        \/ Timeout(p, r)
    /\ GoodRoundSpec

vars == <<round, votes, decided>>

(* `^\newpage^' *)

Spec == 
    /\ Init 
    /\ [][Next]_vars
    \* fairness constraints:
    /\ \A p \in P, v \in V, r \in Round :
        /\ WF_vars(Vote1(p,v,r))
        /\ WF_vars(Vote2(p,v,r))
        /\ WF_vars(Vote3(p,v,r))
        /\ WF_vars(Vote4(p,v,r))
        /\ WF_vars(Decide(p,v,r))
        /\ WF_vars(r < GoodRound /\ Timeout(p, r))

Safety == \A p,q \in T, v,w \in V, r1,r2 \in Round :
    <<r1,v>> \in decided[p] /\ <<r2,w>> \in decided[q] => v = w

Liveness == \A p \in T : \E v \in V : <>(<<GoodRound, v>> \in decided[p])
\* Liveness exhaustively checked with 3 processes, 2 non-trivial quorums of cardinatlity 2, and GoodRound=2.
\* Took 6 hours using 10 cores and 35GB of memory

=============================================================================
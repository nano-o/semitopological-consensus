--------------------- MODULE Voting ---------------------

(***********************************************************************************)
(* This is a high-level specification of a consensus algorithm for a quorum system *)
(* that forms a semitopology. There is no network, messages, or faults at this     *)
(* level of abstraction.                                                           *)
(***********************************************************************************)

EXTENDS Integers

CONSTANTS
    V \* the set of values to decide on
,   P \* the set of processes
,   Quorum \* the set of quorums
,   Blocking \* blocking sets
,   B \* the set of malicious nodes
,   Round


\* Each round consists of 4 phases:
Phase == 1..4
\* A vote is cast in a phase of a round and for a value:
\* @typeAlias: voteType = {round : Int, value : V, phase : Int};
Vote == [round: Round, phase: Phase, value: V]

NotAVote == [round |-> -1, phase |-> 1, value |-> CHOOSE v \in V : TRUE]

\* Whether vote v is maximal in S
\* @type: ({round : Int, value : V, phase : Int}, Set({round : Int, value : V, phase : Int})) => Bool;
Maximal(vt, S) ==
    /\ vt \in S
    /\ \A vt2 \in S : vt2.round <= vt.round

\* A maximal element in the set S, if such exists, and otherwise the default value provided:
Max(S, default) ==
    IF \E e \in S : Maximal(e, S)
    THEN CHOOSE e \in S : Maximal(e, S) \* Is this going to be a problem with Apalache semantics?
    ELSE default

\* We now specify the behaviors of the algorithm:

VARIABLES votes, round, proposal
vars == <<round, votes, proposal>>

TypeOK ==
    /\ votes \in [P -> SUBSET Vote]
    /\ round \in [P -> Round]
    /\ proposal \in [Round -> SUBSET V]
TypeOK_ == TypeOK

decided == {v \in V : \E Q \in Quorum, r \in Round : \A p \in Q \ B :
    [round |-> r, phase |-> 4, value |-> v] \in votes[p] }

\* largest vote of p in phase `phase' before round r
HighestVote(p, phase, r) ==
    LET vs == {v \in votes[p] : v.phase = phase /\ v.round < r} IN
      Max(vs, NotAVote)

\* second largest vote (for a value different from the highest vote) of p in phase `phase' before round r
SecondHighestVote(p, phase, r) ==
    LET largest == HighestVote(p, phase, r)
        vs == {v \in votes[p] : v.phase = phase /\ v.round < r /\ v.value # largest.value}
    IN Max(vs, NotAVote)

\* `v' is safe in round `r2' according to the votes of process `p' in phase `phase' before round r:
ClaimsSafeAt(v, r, r2, p, phase) ==
    \/ r2 = 0
    \/ LET mv == HighestVote(p, 1, r) IN \* Highest vote of p in phase 1 before round r
         /\ r2 <= mv.round
         /\ mv.value = v
    \/ r2 <= SecondHighestVote(p, 1, r).round

\* Whether value v is safe to vote for/propose in round r by process p
\* In case of a vote, we'll use phaseA=4 and phaseB=1
\* In case of a proposal, we'll use phaseA=3 and phaseB=2
SafeAt(v, r, p, phaseA, phaseB) ==
    \/ r = 0
    \/ \E Q \in Quorum :
        /\ \A q \in Q : round[q] >= r \* every member of Q is in round at least r
        /\  \/ \A q \in Q : HighestVote(q, phaseA, r).round = -1 \* members of Q never voted in phaseA before r
            \/ \E r2 \in 0..(r-1) :
                \* no member of Q voted in phaseA in round r2 or later, and
                \* all members of Q that voted in r2 voted for v:
                /\ \A q \in Q : LET hvq == HighestVote(q, phaseA, r) IN
                    /\ hvq.round <= r2
                    /\ hvq.round = r2 => hvq.value = v
                /\ \* v must be safe at r2
                    \/ \E S \in Blocking : \A q \in S : ClaimsSafeAt(v, r, r2, q, phaseB)
                    \/ \E S1,S2 \in Blocking : \E v1,v2 \in V :
                            \E r3 \in r2..(r-1) :
                            \E r4 \in (r3+1)..(r-1) :
                        /\ v1 # v2
                        /\ \A q \in S1 : ClaimsSafeAt(v1, r, r3, q, phaseB)
                        /\ \A q \in S2 : ClaimsSafeAt(v2, r, r4, q, phaseB)

Init ==
    /\ votes = [p \in P |-> {}]
    /\ round = [p \in P |-> 0]
    /\ proposal = [r \in Round |-> {}]

DoVote(p, v, r, phase) ==
    \* never voted before in this round and phase:
    /\ \A w \in V : [round |-> r, phase |-> phase, value |-> w] \notin votes[p]
    \* cast the vote:
    /\ votes' = [votes EXCEPT ![p] = @ \union {[round |-> r, phase |-> phase, value |-> v]}]
    /\ UNCHANGED <<round, proposal>>

HonestProposal(p, r, v) ==
    /\ proposal[r] = {}
    /\ SafeAt(v, r, p, 4, 1)
    /\ proposal' = [proposal EXCEPT ![r] = @ \union {v}]
    /\ UNCHANGED <<votes, round>>

Proposal(r, v) ==
    /\ proposal' = [proposal EXCEPT ![r] = @ \union {v}]
    /\ UNCHANGED <<votes, round>>

Vote1(p, v, r) ==
    /\ r = round[p]
    /\ v \in proposal[r]
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

Vote3(p, v, r) ==
    /\ r = round[p]
    /\ Accepted(p, v, r, 2)
    /\ DoVote(p, v, r, 3)

Vote4(p, v, r) ==
    /\ r = round[p]
    /\ Accepted(p, v, r, 3)
    /\ DoVote(p, v, r, 4)

StartRound(p, r) ==
    /\ round[p] < r
    /\ round' = [round EXCEPT ![p] = r]
    /\ UNCHANGED <<votes, proposal>>

\* This models malicious behavior
\* TLC cannot handle it well though
ByzantineHavoc ==
    \E new_votes \in [P -> SUBSET Vote] :
    \E new_round \in [P -> Round] :
    \E new_proposal \in [Round -> SUBSET V] :
        /\  votes' = [p \in P |-> IF p \in B THEN new_votes[p] ELSE votes[p]]
        /\  round' = [p \in P |-> IF p \in B THEN new_round[p] ELSE round[p]]
        /\  proposal' = new_proposal \* this we havoc completely as safety does not depend on it.

Next ==
    (* \/  ByzantineHavoc *)
    \/  \E p \in P, v \in V, r \in Round :
        \/ Vote1(p, v, r)
        \/ Vote2(p, v, r)
        (* \/ Vote3(p, v, r) *)
        (* \/ Vote4(p, v, r) *)
        \/ StartRound(p, r)
        \* \/ HonestProposal(p, r, v)
        \* \/ Proposal(r, v)

Spec == Init /\ [][Next]_vars

Safety == \A v1,v2 \in decided : v1 = v2

\* Simple properties
Invariant1 == \A p \in P \ B : \A vt \in votes[p] :
    /\  vt.round <= round[p]
    /\  \A vt2 \in votes[p] : vt2.round = vt.round /\ vt2.phase = vt.phase => vt2.value = vt.value
    /\  vt.phase < 3
    /\  vt.phase > 1 => \E Q \in Quorum : \A q \in Q \ B : [round |-> vt.round, phase |-> (vt.phase)-1, value |-> vt.value] \in votes[q]
Invariant1_ == TypeOK /\ Invariant1

=============================================================================

------------ MODULE FastConsensus -------------------

EXTENDS Integers, FiniteSets

CONSTANTS
    V \* the set of values to decide on
,   P \* the set of processes (typically 3f+1 nodes)
,   Quorum \* the set of quorums (typically sets of 2f+1 nodes out of 3f+1)
,   Blocking \* the set of blocking sets (typically sets f+1 nodes out of 3f+1)
,   B \* the set of malicious nodes (typically f nodes)
,   Leader(_) \* assigns a leader to each round

Round == Nat \* the set of rounds

\* Each round consists of 3 voting phases:
Phase == 1..3
\* A votes is cast in a phase of a round and for a value:
Vote == [round: Round, phase: Phase, value: V]
\* A proposal is for a round and a value:
Proposal == [round: Round, value: V]

(*--algorithm FastConsensus {
    variables
        proposals = {};
        votes = [p \in P |-> {}];
        round = [p \in P |-> 0];
    define {
        Decided == {v \in V : \E Q \in Quorum, r \in Round : \A p \in Q \ B :
            [round |-> r, phase |-> 3, value |-> v] \in votes[p] }
        Safety == Cardinality(Decided) <= 1
        Proposable(v, r, HO) == \* HO is intended to be the set of processes the leader hears of
            \/  r = 0 \* no constraint if it's round 0
            \/  /\  \A p \in HO \ B : round[p] >= r
                /\  \E Q \in Quorum : Q \subseteq HO
                /\  \E r2 \in 0..(r-1) : \A p \in HO \ B : \A vt \in votes[p] :
                        vt.round < r /\ vt.phase = 3 =>
                            /\  vt.round <= r2
                            /\  vt.round = r2 => vt.value = v
                            /\  \E Bl \in Blocking :
                                /\  Bl \subseteq HO
                                /\  \A p2 \in Bl \ B : \E vt2 \in votes[p2] : 
                                        /\  vt2.round = r2
                                        /\  vt2.phase = 2
                                        /\  vt2.value = v
        (* `^\newpage^' *)
        Safe(v, r) == 
            \/  r = 0
            \/  \E r2 \in 0..(r-1) : \E Q \in Quorum :
                    \A p \in Q \ B : \A vt \in votes[p] :
                        vt.round < r /\ vt.phase = 3 =>
                            /\  vt.round <= r2
                            /\  vt.round = r2 => vt.value = v
                            /\  \E Bl \in Blocking : \A p2 \in Bl \ B : \E vt2 \in votes[p2] : 
                                    /\  vt2.round = r2
                                    /\  vt2.phase = 1
                                    /\  vt2.value = v
    }
    macro vote(p, v, r, ph) {
        votes[p] := votes[p] \union { [round |-> r, phase |-> ph, value |-> v] };
    }
    process (proc \in (P \ B)) {
l0:     while (TRUE)
            either {
                when Leader(round[self]) = self;
                with (v \in V) {
                    if (self \notin B)
                        with (HO \in SUBSET P)
                            when Proposable(v, round[self], HO);
                    proposals := proposals \cup { [round |-> round[self], value |-> v]}
                }
            }
            or with (v \in V, Q \in Quorum) {
                when Leader(round[self]) \notin B => [round |-> round[self], value |-> v] \in proposals;
                when Safe(v, round[self]);
                when \A vt \in votes[self] : \neg (vt.round = round[self]);
                vote(self, v, round[self], 1);
            }
            or with (v \in V, Q \in Quorum) {
                when \A p \in Q \ B :
                    [round |-> round[self], phase |-> 1, value |-> v] \in votes[p];
                when \A vt \in votes[self] : \neg (vt.round = round[self] /\ vt.phase >= 2);
                vote(self, v, round[self], 2);
            }
            or with (v \in V, Q \in Quorum, Bl \in Blocking) {
                when \A vt \in votes[self] : \neg (vt.round = round[self] /\ vt.phase = 3);
                when 
                    \/  \A p \in Q \ B :
                            [round |-> round[self], phase |-> 2, value |-> v] \in votes[p]
                    \/  \A p \in Bl \ B :
                            [round |-> round[self], phase |-> 3, value |-> v] \in votes[p];
                vote(self, v, round[self], 3);
            }
            or {
                round[self] := round[self] + 1;
            }
    }
}*)
=====================================================

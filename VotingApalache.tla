------------------ MODULE VotingApalache ------------------

EXTENDS Integers

P == {"P1_OF_P", "P2_OF_P", "P3_OF_P", "P4_OF_P"}
(* P == {"P1_OF_P"} *)
V == {"V1_OF_V", "V2_OF_V"}
Quorum == {{"P1_OF_P", "P2_OF_P", "P3_OF_P"}, {"P1_OF_P", "P2_OF_P", "P4_OF_P"}, {"P1_OF_P", "P3_OF_P", "P4_OF_P"}, {"P2_OF_P", "P3_OF_P", "P4_OF_P"}}
Blocking == {{"P1_OF_P","P2_OF_P"}, {"P1_OF_P","P3_OF_P"}, {"P1_OF_P","P4_OF_P"}, {"P2_OF_P","P3_OF_P"}, {"P2_OF_P","P4_OF_P"}, {"P3_OF_P","P4_OF_P"}}
(* Quorum == {{"P1_OF_P"}} *)
(* B == {"P1_OF_P"} *)
B == {}
MaxRound == 1
Round == 0..MaxRound

VARIABLES
    \* @type: P -> Int;
    round,
    \* Looks like Apalache does not like this:
    \* @type: P -> Set({round : Int, value : V, phase : Int});
    votes,
    \* @type: Int -> Set(V);
    proposal

INSTANCE Voting


===========================================================

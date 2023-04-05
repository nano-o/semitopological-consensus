----- MODULE ConsensusAlgo ----

EXTENDS Integers, FiniteSets

CONSTANTS
    Value \* the set of values to decide on
  , P \* the set of processes
  , Quorum \* the set of quorums
  , T \* a topen

\* The protocol starts at round 0 and the round number only increases:
Round == Nat
\* Each round consists of 5 phases 0 to 4 and the special marker -1
Phase == 0..4 \cup {-1}
\* The phases in which votes are cast:
VotePhase == 1..4
\* We use -1 in place of a round as a special marker
RoundOrNone == Round \cup {-1}

Message ==
     [type : {"vote"}, round : Round, phase : VotePhase, value : Value]
\cup [type : {"suggest"},
      round : Round, 
      h2 : [round : RoundOrNone, value : Value], 
      sh2 : RoundOrNone,
      h3 : [round : RoundOrNone, value : Value]]  
\cup [type : {"proof"}, 
      round : RoundOrNone,
      h1 : [round : RoundOrNone, value : Value], 
      sh1 : RoundOrNone,
      h4 : [round : RoundOrNone, value : Value]]

VARIABLES
    network \* the content of the network
,   round \* map from process to current round
,   phase \* map from process to curent phase
,   highest \* map from process to highest vote in each phase
,   secondHighest \* map from process to second highest voted round (phase 1 and 2)

vars == <<network, round, phase, highest, secondHighest>>

TypeOkay ==
    /\ network \subseteq Message
    /\ round \in [P -> Round]
    /\ phase \in [P -> Phase]
    /\ highest \in [P -> [VotePhase -> [round : RoundOrNone, value : Value]]]
    /\ secondHighest \in [P -> [{1,2} -> RoundOrNone]]

SomeValue == CHOOSE v \in Value : TRUE

Init ==
    /\ network = {}
    /\ round = [p \in P |-> 0]
    /\ phase = [p \in P |-> 1] \* Not 0 on purpose
    /\ highest = [p \in P |-> [i \in VotePhase |-> [round |-> -1, Value |-> SomeValue]]]
    /\ secondHighest = [p \in P |-> [i \in {1,2} |-> -1]]

Send(msgs) == network' = network \cup msgs

SuggestMsg(p) ==
    [type |-> "suggest",
     round |-> round[p],
     h2 |-> highest[p][2],
     sh2 |-> secondHighest[p][2],
     h3 |-> highest[p][3]]

ProofMsg(p) ==
    [type |-> "proof",
     round |-> round[p],
     h1 |-> highest[p][1],
     sh1 |-> secondHighest[p][1],
     h4 |-> highest[p][4]]

Phase0(p, r) ==
    /\ round[p] = r
    /\ phase[p] = 0
    /\ Send({SuggestMsg(p), ProofMsg(p)})
    /\ phase' = [phase EXCEPT ![p] = 1]
    /\ UNCHANGED <<round, highest, secondHighest>>

Phase1(p, r, v) ==
    /\ round[p] = r
    /\ phase[p] = 1
    /\ TRUE \* TODO: condition on proof messages
    /\ phase' = [phase EXCEPT ![p] = 1]
    /\ TRUE \* TODO: update highest and second highest
    /\ UNCHANGED <<round>>

Phase2(p, r, v) ==
    /\ round[p] = r
    /\ phase[p] = 2
    /\ TRUE \* TODO: quorum in previous round
    /\ phase' = [phase EXCEPT ![p] = 3]
    /\ TRUE \* TODO: update highest and second highest
    /\ UNCHANGED <<round>>

Phase3(p, r, v) ==
    /\ round[p] = r
    /\ phase[p] = 3
    /\ TRUE \* TODO: quorum in previous round
    /\ TRUE \* TODO: update highest
    /\ phase' = [phase EXCEPT ![p] = 4]
    /\ UNCHANGED <<round, secondHighest>>

Phase4(p, r, v) ==
    /\ round[p] = r
    /\ phase[p] = 4
    /\ TRUE \* TODO: quorum in previous round
    /\ TRUE \* TODO maybe decide
    /\ phase' = [phase EXCEPT ![p] = -1]
    /\ UNCHANGED <<round, secondHighest>>

Timeout(p, r) ==
    /\ round[p] = r
    /\ round' = [round EXCEPT ![p] = r+1]
    /\ phase' = [phase EXCEPT ![p] = 0]
    /\ UNCHANGED <<network, highest, secondHighest>>

VARIABLES votes_, round_, decided_

Voting == INSTANCE Voting WITH 
    votes <- votes_
,   round <- round_
,   decided <- decided_
,   GoodRound <- 0

===============================
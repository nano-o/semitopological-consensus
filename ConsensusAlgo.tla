----- MODULE ConsensusAlgo ----

EXTENDS Integers, FiniteSets

CONSTANTS
    Value \* the set of values to decide on
,   P \* the set of processes
,   Quorum \* the set of quorums
,   T \* a topen
,   Leader(_,_) \* Leader(p, r)

INSTANCE Semitopology WITH
    P <- P,
    Open <- Quorum

\* The protocol starts at round 0 and the round number only increases:
Round == Nat
\* Each round consists of 6 phases "suggest/proof", "propose", "vote1", "vote2", "vote3", and "vote4"
\* "finished" is there to indicate that all phases have been completed
Phase == {"suggest/proof", "propose", "vote1", "vote2", "vote3", "vote4", "finished"}
\* The phases in which votes are cast:
VotePhase == 1..4
\* We use -1 in place of a round as a special marker
RoundOrNone == Round \cup {-1}

Message ==
     [type : {"vote"},
      src: P,
      round : Round, 
      phase : VotePhase, 
      value : Value]
\cup [type : {"proposal"},
      src: P,
      round : Round, 
      value : Value]
\cup [type : {"suggest"},
      src: P,
      round : Round, 
      h2 : [round : RoundOrNone, value : Value], 
      sh2 : RoundOrNone,
      h3 : [round : RoundOrNone, value : Value]]
\cup [type : {"proof"}, 
      src: P,
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
,   decided

vars == <<network, round, phase, highest, secondHighest, decided>>

TypeOkay ==
    /\ network \subseteq Message
    /\ round \in [P -> Round]
    /\ phase \in [P -> Phase]
    /\ highest \in [P -> [VotePhase -> [round : RoundOrNone, value : Value]]]
    /\ secondHighest \in [P -> [{1,2} -> RoundOrNone]]
    /\ decided \in [P -> SUBSET (Round\times Value)]

SomeValue == CHOOSE v \in Value : TRUE

Init ==
    /\ network = {}
    /\ round = [p \in P |-> 0]
    /\ phase = [p \in P |-> "propose"]
    /\ highest = [p \in P |-> [i \in VotePhase |-> [round |-> -1, value |-> SomeValue]]]
    /\ secondHighest = [p \in P |-> [i \in {1,2} |-> -1]]
    /\ decided = [p \in P |-> {}]

Send(msgs) == network' = network \cup msgs

SuggestMsg(p) ==
    [type |-> "suggest",
     src |-> p,
     round |-> round[p],
     h2 |-> highest[p][2],
     sh2 |-> secondHighest[p][2],
     h3 |-> highest[p][3]]

ProofMsg(p) ==
    [type |-> "proof",
     src |-> p,
     round |-> round[p],
     h1 |-> highest[p][1],
     sh1 |-> secondHighest[p][1],
     h4 |-> highest[p][4]]

SuggestAndProve(p, r) ==
    /\ round[p] = r
    /\ phase[p] = "suggest/proof"
    /\ Send({SuggestMsg(p), ProofMsg(p)})
    /\ phase' = [phase EXCEPT ![p] =
        IF Leader(p, r) = p THEN "propose" ELSE "vote1"]
    /\ UNCHANGED <<round, highest, secondHighest, decided>>

ClaimsSafeAt(v, r, m) == 
    LET h == IF m.type = "proof" THEN "h1" ELSE "h2"
        sh == IF m.type = "proof" THEN "sh1" ELSE "sh2"
    IN
        \/ r = 0
        \/ r <= m[h].round /\ v = m[h].value
        \/ r <= m[sh]

SafeAt(v, r, p, type) ==
    \/ r = 0
    \/ \E Q \in Quorum :
        /\ p \in Q \* Q must be a quorum of p
        \* every member of Q has joined the current round and sent a message of the right type:
        /\ \A q \in Q : \E m \in network : 
            m.type = type /\ m.src = q /\ m.round = r
        /\ LET h == IF type = "proof" THEN "h4" ELSE "h3"
               m == [q \in Q |-> CHOOSE m \in network :
                m.type = type /\ m.src = q /\ m.round = r] IN
            /\  \/ \A q \in Q : m[q][h].round = -1
                \/ \E r2 \in Round :
                    /\ r2 < r
                    /\ \E q \in Q : m[q][h].round = r2
                    /\ \A q \in Q : LET hvq == m[q][h] IN
                        /\ hvq.round <= r2
                        /\ hvq.round = r2 => hvq.value = v
                    /\ \E S \in SUBSET P :
                        /\ p \in Closure(S)
                        /\ \A q \in S : \E m2 \in network : 
                            m2.type = type /\ m2.src = q /\ m2.round = r
                        /\ LET m2 == [q \in S |-> CHOOSE m2 \in network :
                                m2.type = type /\ m2.src = q /\ m2.round = r] IN
                            \A q \in S : ClaimsSafeAt(v, r2, m2[q])  

Propose(p, r, v) ==
    /\ round[p] = r
    /\ phase[p] = "propose"
    /\ SafeAt(v, r, p, "suggest")
    /\ Send({[type |-> "proposal", src |-> p, round |-> r, value |-> v]})
    /\ phase' = [phase EXCEPT ![p] = "vote1"]
    /\ UNCHANGED <<round, highest, secondHighest, decided>>

UpdateHighest(p, r, v, i) ==
    highest' = [highest EXCEPT ![p] = [@ EXCEPT ![i] = [round |-> r, value |-> v]]]

UpdateSecondHighest(p, i) ==
    IF highest[p][i].round # -1 /\ highest[p][i].value # highest'[p][i]
      THEN secondHighest' = [secondHighest EXCEPT ![p] = [@ EXCEPT ![1] = highest[p][1].round]]
      ELSE UNCHANGED secondHighest

SendVote(p, r, i, v) ==
    Send({[type |-> "vote", src |-> p, round |-> r, phase |-> i, value |-> v]})

Vote1(p, r, v) ==
    /\ round[p] = r
    /\ phase[p] = "vote1"
    /\ [type |-> "proposal", src |-> Leader(p,r), round |-> r, value |-> v] \in network
    /\ SafeAt(v, r, p, "proof")
    /\ phase' = [phase EXCEPT ![p] = "vote2"]
    /\ SendVote(p, r, 1, v)
    /\ UpdateHighest(p, r, v, 1)
    /\ UpdateSecondHighest(p, 1)
    /\ UNCHANGED <<round, decided>>

UnanimousQuorum(p, r, i, v) == \E Q \in Quorum :
    /\ p \in Q
    /\ \A q \in Q : 
        [type |-> "vote", src |-> q, round |-> r, phase |-> i, value |-> v] \in network

Vote2(p, r, v) ==
    /\ round[p] = r
    /\ phase[p] = "vote2"
    /\ UnanimousQuorum(p, r, 1, v)
    /\ phase' = [phase EXCEPT ![p] = "vote3"]
    /\ SendVote(p, r, 2, v)
    /\ UpdateHighest(p, r, v, 2)
    /\ UpdateSecondHighest(p, 2)
    /\ UNCHANGED <<round, decided>>

Vote3(p, r, v) ==
    /\ round[p] = r
    /\ phase[p] = "vote3"
    /\ UnanimousQuorum(p, r, 2, v)
    /\ SendVote(p, r, 3, v)
    /\ UpdateHighest(p, r, v, 3)
    /\ phase' = [phase EXCEPT ![p] = "vote4"]
    /\ UNCHANGED <<round, secondHighest, decided>>

Vote4(p, r, v) ==
    /\ round[p] = r
    /\ phase[p] = "vote4"
    /\ UnanimousQuorum(p, r, 3, v)
    /\ SendVote(p, r, 4, v)
    /\ UpdateHighest(p, r, v, 4)
    /\ phase' = [phase EXCEPT ![p] = "finished"]
    /\ UNCHANGED <<round, secondHighest, decided>>

Decide(p, r, v) ==
    /\ round[p] = r
    /\ UnanimousQuorum(p, r, 4, v)
    /\ decided' = [decided EXCEPT ![p] = @ \cup {<<r,v>>}]
    /\ UNCHANGED <<network, round, phase, highest, secondHighest>>

StartRound(p, r) ==
    /\ round[p] < r
    /\ round' = [round EXCEPT ![p] = r]
    /\ phase' = [phase EXCEPT ![p] = "suggest/proof"]
    /\ UNCHANGED <<network, highest, secondHighest, decided>>
    /\ round'[p] \in Round \* for TLC

Next == \E p \in P, r \in Round, v \in Value :
    \/ SuggestAndProve(p, r)
    \/ Propose(p, r, v)
    \/ Vote1(p, r, v)
    \/ Vote2(p, r, v)
    \/ Vote3(p, r, v)
    \/ Vote4(p, r, v)
    \/ Decide(p, r, v)
    \/ NewRound(p, r)

Spec == Init /\ [][Next]_vars

Safety == \A p,q \in P, v,w \in Value, r1,r2 \in Round :
    <<r1,v>> \in decided[p] /\ <<r2,w>> \in decided[q] => v = w

\* Next we instantiate the Voting specification

votes_ == [p \in P |-> 
    LET VoteMsgs == {m \in network : m.src = p /\ m.type = "vote"} IN
      {[round |-> v.round, phase |-> v.phase, value |-> v.value] : v \in VoteMsgs}]

Voting == INSTANCE Voting WITH 
    votes <- votes_
,   round <- round
,   decided <- decided

THEOREM Spec => Voting!Spec

===============================
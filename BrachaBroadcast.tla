--------------------- MODULE BrachaBroadcast ------------------

(**************************************************************************************************************)
(* This is a specification of a semitopological version of `^Bracha's broadcast^'                             *)
(* algorithm following                                                                                        *)
(* `^https://decentralizedthoughts.github.io/2020-09-19-living-with-asynchrony-brachas-reliable-broadcast/.^' *)
(*                                                                                                            *)
(* We do not model the network but we do model malicious failures. For example, in                            *)
(* step Vote below, a party votes for v when the non-faulty portion of a quorum                               *)
(* votes for v. Note that this places no requirement on the faulty portion of the                             *)
(* quorum, which models that the faulty parties are free to lie in whichever way                              *)
(* they want in order to make a non-faulty party take a step.                                                 *)
(*                                                                                                            *)
(* One thing that might seem strange is that faulty parties take steps like everyone                          *)
(* else. This does not matter since we place no requirements on the faulty parties                            *)
(* in the steps of non-faulty parties, but it is convenient in order to avoid                                 *)
(* conditionals everywhere (including in the statements of the properties like                                *)
(* Agreement: we can assert that all members of U agree instead of all non-faulty                             *)
(* members of U).                                                                                             *)
(**************************************************************************************************************)

EXTENDS Semitopology

CONSTANTS
    l \* the leader
,   V \* the set of values that the leader may broadcast
,   Bot \* a special default value not in V
,   B \* the set of faulty parties (the baddies)
,   U \* a resilient set

ASSUME Resilient(U)
ASSUME Bot \notin V

VARIABLES sent, echo, vote, output
vars == <<sent, echo, vote, output>>

TypeOkay == \A p \in P :
    /\ sent \in V
    /\ echo[p] \in V\cup {Bot}
    /\ vote[p] \in V\cup {Bot}
    /\ output[p] \in V\cup {Bot}

(*****************************************************************)
(* We start with the properties we want the protocol to satisfy. *)
(*****************************************************************)

(**********************************************************************************)
(* If the leader is non-faulty, then eventually all members of U output the value *)
(* sent by the leader:                                                            *)
(**********************************************************************************)
Validity == 
    l \notin B => <>(\A p \in U : output[p] = sent)

(*************************************************************************************)
(* If a non-faulty member of U outputs v, then eventually all members of U output v: *)
(*************************************************************************************)
Agreement == \A v \in V : \A p1,p2 \in U :
    [](output[p1] = v => <>(output[p2] = v))

(* `^\newpage^' *)

(********************************************************)
(* We should also require that a party decide only once. *)
(********************************************************)
OutputOnce == \A v \in V, p \in P :
    [](output[p] = v => [](output[p] = v))

(*******************************************)
(* Next we state some important invariants *)
(*******************************************)

(*********************************************************************************)
(* If the leader is non-faulty, then every parties that echoes a value echoes the *)
(* value that the leader sent:                                                   *)
(*********************************************************************************)
Invariant0 == \A p \in P : l \notin B /\ echo[p] # Bot => echo[p] = sent

(*******************************************************************************)
(* If a member of U votes for v, then there is an open neighborhood of U whose *)
(* non-faulty members echoed v:                                                *)
(*******************************************************************************)
Invariant1 == \A p \in U : vote[p] # Bot =>
    \E O \in Open : 
        /\ O \cap U # {} 
        /\ \A q \in O \ B : echo[q] = vote[p]

(*********************************************************************************)
(* If a party p outputs v, then there is an open of p whose non-faulty members   *)
(* voted for v. Together with the Vote step below and Conjecture2, this implies  *)
(* that, once a member of U has output v, every member of U eventually votes for *)
(* v, and thus, because U is an open, byt step Output below, all members of U    *)
(* eventually output v                                                           *)
(*********************************************************************************)
Invariant2 == \A p \in P : output[p] # Bot =>
    \E O \in Open :
        /\ p \in O 
        /\ \A q \in O \ B : vote[q] = output[p]

(************************************************)
(* Next we specify the behavior of the protocol *)
(************************************************)

Init == 
    /\ echo = [p \in P |-> Bot]
    /\ vote = [p \in P |-> Bot]
    /\ output = [p \in P |-> Bot]
    /\ sent \in V \* initially, the leader sends an arbitrary value

(**********************************************************************************)
(* If the leader is non-faulty, then p echoes for the value that the leader sent. *)
(* Otherwise, we let p echo any value to model the fact that the leader can lie.  *)
(**********************************************************************************)
Echo(p, v) ==
    /\ l \notin B => v = sent
    /\ echo[p] = Bot
    /\ echo' = [echo EXCEPT ![p] = v]
    /\ UNCHANGED <<sent, vote, output>>

(* `^\newpage^' *)
(************************************************************************************)
(* A party p votes for v when either a) p receives echoes for v from an all members *)
(* of one of its open neighborhoods or b) p receives votes for v from from a set S  *)
(* and all open neighborhoods of p intersect S (i.e. p is in the closure of S). We  *)
(* model the fact that faulty parties may lie by requiring only that the non-faulty *)
(* portion of O, or the non-faulty portion of the set S, voted for v.               *)
(************************************************************************************)
Vote(p, v) ==
    /\ vote[p] = Bot
    /\ \/ \E O \in Open : p \in O /\ \forall q \in O \ B : echo[q] = v
       \/ \E S \in SUBSET (P \ {p}): 
            /\ p \in Closure(S)
            /\ \forall q \in S \ B : vote[q] = v
    /\ vote' = [vote EXCEPT ![p] = v]
    /\ UNCHANGED <<sent, echo, output>>

(******************************************************************************)
(* A party outputs when it receives echo messages for the same value from all *)
(* members of one of its open neighborhoods.                                  *)
(******************************************************************************)
Output(p, v) ==
    /\ output[p] = Bot
    /\ \/ \E O \in Open : p \in O /\ \forall q \in O \ B : vote[q] = v
    /\ output' = [output EXCEPT ![p] = v]
    /\ UNCHANGED <<sent, vote, echo>>

\* The full transition relation:
Next == \E p \in P, v \in V :
    Echo(p, v) \/ Vote(p, v) \/ Output(p, v)

(*********************************************************************************)
(* We additionally require that every member of U eventually take a step when it *)
(* can. We formalize this with fairness requirements:                            *)
(*********************************************************************************)
Fairness == \A p \in U, v \in V :
    /\ WF_vars(Echo(p,v))
    /\ WF_vars(Vote(p,v))
    /\ WF_vars(Output(p,v))

(*****************************************************************)
(* Finally, this formula specifies the behavior of the protocol: *)
(*****************************************************************)
Spec == 
    /\ Init 
    /\ [][Next]_vars
    /\ Fairness

===============================================================
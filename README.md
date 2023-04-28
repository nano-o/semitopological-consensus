This repository contains specifications of algorithms for semitopologies
(semitopologies are an abstract model of federated Byzaninte agreement
systems).

Files with `MC` in their name are setup files for the TLC model-checker and can
be used with the TLA+ extension for VS Code.

[Semitopology.tla](./Semitopology.tla) specifies relevant notions of semitopology.

[BrachaBroadcast.tla](./BrachaBroadcast.tla) is a specification of Bracha's
broadcast algorithm adapted to our semitopological context.

The following two specifications are work in progress:

[ConsensusAlgo.tla](./ConsensusAlgo.tla) specifies a consensus algorithm that
is essentially a semitopological version of Paxos.

[Voting.tla](./Voting.tla) is a more abstract specification of the consensus algorithm.
[VotingLivness.tla](./VotingLiveness.tla) specifies liveness properties.


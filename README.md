This repository contains specifications of algorithms for semitopologies.
Semitopologies are an abstract model of federated Byzantine agreement systems
(FBA). Classic Byzantine quorum systems are also a special case of
semitopologies.

Files with `MC` in their name are setup files for the TLC model-checker and can
be used with the TLA+ extension for VS Code.

[Semitopology.tla](./Semitopology.tla) specifies relevant notions of semitopology.

[BrachaBroadcast.tla](./BrachaBroadcast.tla) is a specification of Bracha's
broadcast algorithm adapted to our semitopological context.

The following two specifications are work in progress:

[ConsensusAlgo.tla](./ConsensusAlgo.tla) specifies a consensus algorithm that
is essentially a semitopological version of Paxos. This algorithm is also
briefly described in [6-phases-algo.pdf](./6-phases-algo.pdf) in the context of
a classic quorum system with 3f+1 nodes.

[Voting.tla](./Voting.tla) is a more abstract specification of the consensus algorithm.
[VotingLivness.tla](./VotingLiveness.tla) specifies liveness properties.


This repository contains specifications related to a new consensus algorithm.
This algorithm is suitable to solve consensus in a semitopology.

[Semitopology.tla](./Semitopology.tla) specifies relevant notions of semitopology.

[ConsensusAlgo.tla](./ConsensusAlgo.tla) specifies the consensus algorithm.

[Voting.tla](./Voting.tla) is a more abstract specification of the algorithm.
[VotingLivness.tla](./VotingLiveness.tla) specifies liveness properties.

Finally, files with `MC` in their name are setup files for the TLC model-checker.

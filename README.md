# Ben-Or-Pluscal
Implementation of [Ben Or algorithm](http://disi.unitn.it/~montreso/ds/syllabus/papers/AguileraToeug-CorrecnessBenOr),
a binary consensus algorithm, in PlusCal using Shared pool messaging.

Also referred Lamport's C-Syntax [User Manual](https://lamport.azurewebsites.net/tla/c-manual.pdf) and Hillel Wayne's [Practical TLA+](https://lamport.azurewebsites.net/tla/practical-tla.html).

#### Specification Variables:
* p1Msg: name of the phase1 message-board
* p2Msg: name of the phase2 message-board
* Messages format: [nodeid, round, value]
* N denotes the number of nodes
* F denotes the maximum number of processes that may fail, such that F<N
* MAXROUND bounds the number of rounds a node can try
* INPUT denotes initial values to nodes.
* "p1v" denotes the value the process will broadcast in phase 1 of a round. Initialize p1v=INPUT[self]
* "p2v" denotes the value the process will broadcast in phase 2 of a round. Initialize p2v=-1
* -1 denotes "⊥" or "?" value.
* "decided" variable at each node stores the final/terminal decision a node makes for consensus.
    Initially decided=-1, and when the process decides, decided is set to 0 or 1.
* r denotes number of rounds. Bounded by Maxround, initialized r=1
* Suggested Model Execution:
    * F <- 1, N <- 4, INPUT <- <<0,1,1,>>, MAXROUND <-1

#### Model Checking
* Write and test a property to capture the Agreement property of the
consensus protocol. Agreement should always be satisfied, even when
F is more than N/2. Test with N<5 and F < 5, with different values.
Agreement should never be violated. Even when F is more than majority
of processes, Agreement should still hold.
* Write and test a property to capture the Progress property of the
consensus protocol. If you start with all same preference value at all
nodes, this should terminate.
When INPUT=«1,1,1,1» or when INPUT=«0,0,0,0» Progress should
not be violated. That is, every process eventually will have
"decided != -1".
* Write and test a BaitProgress condition which claims that it is not
possible for all processes to decide (written as a safety property), and
watch the model checker come up with ways progress can happen and
show you that consensus can be solved for some runs.
The model checker should find some computations where all
processes will have "decided != -1" , even when Progress does not hold
(i.e., it is not the case that all computations have "decided 6= -1" for
all processes).
* If N=4 and INPUT=«0,1,1,1», is it possible to have 0 decided for a run?
Write a safety property called MinorityReport which claims that it
is not possible for all the nodes to finalize with "0" as the consensus
value. The model checker will try to prove you wrong by producing a
counterexample when possible. Check this with F=0, F=1, and F=2.
------------------------------- MODULE benor -------------------------------
(*\* Ben-Or algorithm *)
EXTENDS Integers, Sequences, FiniteSets
\* N nodes; F possible failure; MAXROUND iteration of rounds
CONSTANT N, F, INPUT, MAXROUND
ASSUME N \in Nat /\ F < N
Rounds == 1..MAXROUND
Procs == 1..N
(*
--algorithm benor
{
    variable p1Msg = {}, p2Msg = {}; \* Message Boards for phase1 and phase2
    define
    {
        SentPhase1Msgs(r) == {m \in p1Msg: (m.round=r)}
        SentPhase1ValMsgs(r,b) == {m \in p1Msg: (m.round=r) /\ (m.val=b)}

        SentPhase2Msgs(r) == {m \in p2Msg: (m.round=r)}
        SentPhase2ValMsgs(r,b) == {m \in p2Msg: (m.round=r) /\ (m.val=b)}
    }

    \* \* Node calls this to send p1v msg to other nodes
    macro SendP1 (n,r,b)
    {
        p1Msg := p1Msg \union {[node_id |-> n, round |-> r, val |-> b]};
    }

    \* \* Node calls this after collecting p1v msgs
    macro CollectP1 (n,r)
    {
        \* wait until p1v msgs is greater/equal than N-F
        await (Cardinality(SentPhase1Msgs(r)) >= (N-F));

    	\* if received more than n/2 messages(p1v),
    	\* then set next phase's value to that otherwise set it to -1
		if(Cardinality(SentPhase1ValMsgs(r,0))*2 > (N)){
            p2v := 0;
        }
        else if (Cardinality(SentPhase1ValMsgs(r,1))*2 > (N)){
            p2v := 1;
        }
        else{
            p2v := -1;
        };
    }


    \* \* Node calls this to send p2v msg to other nodes
    macro SendP2 (n,r,b)
    {
        p2Msg:=p2Msg \union {[node_id |-> n, round |-> r, val |-> b]};
    }

    \* \* Node calls this after collecting p2v msgs
    macro CollectP2 (n,r)
    {
        \* wait until p2v msgs is greater/equal to N-F
        await (Cardinality(SentPhase2Msgs(r)) >= (N-F));

    	\* if received more than n/2 messages(p2v),
    	\* then set "v" value to that otherwise set it to -1
    	if (Cardinality(SentPhase2ValMsgs(r,0)) >= (F + 1)){
            v := 0;
        }
        else if(Cardinality(SentPhase2ValMsgs(r,1)) >= (F + 1)){
            v := 1;
        };
    }

    macro SetNextRoundVal(n,r)
    {
        if (SentPhase2ValMsgs(r,1) # {}){
            p1v := 1;
        }
        else if(SentPhase2ValMsgs(r,0) # {}){
            p1v := 0;
        }
        else{
            with (y \in {0,1})
                p1v := y;
        };
    }

    \* \* Node process
    fair process (p \in Procs)
    variable node_id=self, r=0, p1v = INPUT[self], p2v = -1, decided = -1, v = -1;
    {
        R: while (r < MAXROUND) {
            r:=r+1;

            \*\*  Start Phase 1
            P1: SendP1(node_id, r, p1v);
			CP1:  CollectP1(node_id, r);

            \*\* Start Phase 2
            P2:  SendP2(node_id, r, p2v);
			CP2: CollectP2(node_id, r);

            \*\* Decide
            P2N: if (v \in {0,1}){
					decided := v;
			};

			\* Proceed, Set Next rounds broadcasting values
			SetNextRoundVal(node_id,r);
        }
    }
}
*)
\* BEGIN TRANSLATION
VARIABLES p1Msg, p2Msg, pc

(* define statement *)
SentPhase1Msgs(r) == {m \in p1Msg: (m.round=r)}
SentPhase1ValMsgs(r,b) == {m \in p1Msg: (m.round=r) /\ (m.val=b)}

SentPhase2Msgs(r) == {m \in p2Msg: (m.round=r)}
SentPhase2ValMsgs(r,b) == {m \in p2Msg: (m.round=r) /\ (m.val=b)}

VARIABLES node_id, r, p1v, p2v, decided, v

vars == << p1Msg, p2Msg, pc, node_id, r, p1v, p2v, decided, v >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ p1Msg = {}
        /\ p2Msg = {}
        (* Process p *)
        /\ node_id = [self \in Procs |-> self]
        /\ r = [self \in Procs |-> 0]
        /\ p1v = [self \in Procs |-> INPUT[self]]
        /\ p2v = [self \in Procs |-> -1]
        /\ decided = [self \in Procs |-> -1]
        /\ v = [self \in Procs |-> -1]
        /\ pc = [self \in ProcSet |-> "R"]

R(self) == /\ pc[self] = "R"
           /\ IF r[self] < MAXROUND
                 THEN /\ r' = [r EXCEPT ![self] = r[self]+1]
                      /\ pc' = [pc EXCEPT ![self] = "P1"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ r' = r
           /\ UNCHANGED << p1Msg, p2Msg, node_id, p1v, p2v, decided, v >>

P1(self) == /\ pc[self] = "P1"
            /\ p1Msg' = (p1Msg \union {[node_id |-> node_id[self], round |-> r[self], val |-> p1v[self]]})
            /\ pc' = [pc EXCEPT ![self] = "CP1"]
            /\ UNCHANGED << p2Msg, node_id, r, p1v, p2v, decided, v >>

CP1(self) == /\ pc[self] = "CP1"
             /\ (Cardinality(SentPhase1Msgs(r[self])) >= (N-F))
             /\ IF Cardinality(SentPhase1ValMsgs(r[self],0))*2 > (N)
                   THEN /\ p2v' = [p2v EXCEPT ![self] = 0]
                   ELSE /\ IF Cardinality(SentPhase1ValMsgs(r[self],1))*2 > (N)
                              THEN /\ p2v' = [p2v EXCEPT ![self] = 1]
                              ELSE /\ p2v' = [p2v EXCEPT ![self] = -1]
             /\ pc' = [pc EXCEPT ![self] = "P2"]
             /\ UNCHANGED << p1Msg, p2Msg, node_id, r, p1v, decided, v >>

P2(self) == /\ pc[self] = "P2"
            /\ p2Msg' = (p2Msg \union {[node_id |-> node_id[self], round |-> r[self], val |-> p2v[self]]})
            /\ pc' = [pc EXCEPT ![self] = "CP2"]
            /\ UNCHANGED << p1Msg, node_id, r, p1v, p2v, decided, v >>

CP2(self) == /\ pc[self] = "CP2"
             /\ (Cardinality(SentPhase2Msgs(r[self])) >= (N-F))
             /\ IF Cardinality(SentPhase2ValMsgs(r[self],0)) >= (F + 1)
                   THEN /\ v' = [v EXCEPT ![self] = 0]
                   ELSE /\ IF Cardinality(SentPhase2ValMsgs(r[self],1)) >= (F + 1)
                              THEN /\ v' = [v EXCEPT ![self] = 1]
                              ELSE /\ TRUE
                                   /\ v' = v
             /\ pc' = [pc EXCEPT ![self] = "P2N"]
             /\ UNCHANGED << p1Msg, p2Msg, node_id, r, p1v, p2v, decided >>

P2N(self) == /\ pc[self] = "P2N"
             /\ IF v[self] \in {0,1}
                   THEN /\ decided' = [decided EXCEPT ![self] = v[self]]
                   ELSE /\ TRUE
                        /\ UNCHANGED decided
             /\ IF SentPhase2ValMsgs(r[self],1) # {}
                   THEN /\ p1v' = [p1v EXCEPT ![self] = 1]
                   ELSE /\ IF SentPhase2ValMsgs(r[self],0) # {}
                              THEN /\ p1v' = [p1v EXCEPT ![self] = 0]
                              ELSE /\ \E y \in {0,1}:
                                        p1v' = [p1v EXCEPT ![self] = y]
             /\ pc' = [pc EXCEPT ![self] = "R"]
             /\ UNCHANGED << p1Msg, p2Msg, node_id, r, p2v, v >>

p(self) == R(self) \/ P1(self) \/ CP1(self) \/ P2(self) \/ CP2(self)
              \/ P2N(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
-------------------------------------------------------------------------------
\*AGREEMENT
Agreement == (\A j,k \in Procs: decided[j] # -1 /\ decided[k] # -1
            => decided[j]=decided[k])

\*PROGRESS
Progress == <>(\A d \in Procs: decided[d] # -1)

\*BAIT PROGRESS
BaitProgress == \A a1 \in Procs: \A k \in Rounds:
                Cardinality(SentPhase1ValMsgs(k,0)) = Cardinality(SentPhase1ValMsgs(k,1))
                => decided[a1] = -1

\* Util Variables: Count number of 0s and 1s in INPUT
m0 == (Cardinality({i \in Procs: (INPUT[i]=0)}))
m1 == (Cardinality({i \in Procs: (INPUT[i]=1)}))

\*MINORITY REPORT
MinorityReport0 == (\A p1 \in Procs: m1 > m0 => decided[p1] # 0)
MinorityReport1 == (\A p1 \in Procs: m1 < m0 => decided[p1] # 1)
MinorityReport == (MinorityReport0 /\ MinorityReport1)

=============================================================================

Submitted by:
Ameen Mohd. Khan    (UBID: ameenmoh)
Sameer Singh Rathor (UBID: srathor)

# Ben-Or Algorithm
In our implementation, we use macros "SendP1"/"CollectP1" for sending and collecting
Phase 1 values and "SendP2"/"CollectP2" for sending and collecting Phase 2 values.
An additional variable, besides the ones suggested in the Project description, is
"v", which is set after collecting second phase values and used in deciding rounds
value and setting the next round's first phase values.

To understand the model checker execution for different Inputs, N and F,
(MAXROUND 3 for all), we observed that by increasing F, the diameter and the unique
states increased dramatically.

-------------------------------------------------------------------------------

1. Agreement property
    Agreement, as defined, is a property that should never be violated.
    It should still hold even when F (failure nodes) is greater than the majority of
    processes (majority for our case is N/2, N is the total number of processes).
    As suggested, we tested our agreement property with N<5 and F < 5,
    with different values.
    Our property to capture Agreement is that if two processes "decide" a value
    other than -1, they should be equal.

    Observation and Correctness check:
        Case 1: F < N/2
            - In these scenarios, the majority of available/online nodes are non-faulty
            so there are definitely "N-F" values in Phase1's message board. Also,
            there are definitely either "F+1" or a single value in Phase2's message board
            for a consensus to be reached. This observation held true for all
            all N values from 2 to 5, where F was always less than half of that N.

        Case 2: F >= N/2
            - For Phase1 to complete, "N-F" messages are needed in Phase1 message board,
            (using PlusCal's "await" construct). For examples, N=3, F=2 so N-F = 1.
            Since one process is always non-faulty, it writes its own value and
            Phase1 is successfully completed.
            Similarly, Phase2 waits for N-F messages and the looks for "F+1" or at
            least 1 value to "decide". In this example, it is F+1=> 3, which is not
            possible, but there is at least 1 value corresponding to a non-faulty
            processor in Phase2's message_board, which it decides on that value
            and anchors it.
            Interesting thing is, when any of those 2 faulty processes come back
            online, it sees the already decided value and decides upon it.
            Hence consensus is reached even if F is greater or equal to N/2 and
            agreement is observed to not be violated.

-------------------------------------------------------------------------------

2. Progress property
    Progress property is a liveness property, which says good things do happen,
    and in PlusCal, they are usually defined using temporal (non-deterministic)
    operators. In BenOr, an example of "progress" means that if we start with
    all same preference values (INPUT=«1,1,1,1» or «0,0,0,0» ), algorithm should
    terminate such that, every process should eventually have "decided" not -1.
    Another way of putting this is, for Progress to hold, "eventually all
    processes should decide a value".
    This is exactly what we have modeled using eventual (<>) operator. <>P means
    that for every possible behavior, at least one state has P as true.

    Observation and Correctness check:
        - Progress property held for all cases where F =< N/2, because majority of
        processes are non-faulty. So consequently Phase1's message board always have
        N-F messages and Phase2's message board always have at least F+1 or a single
        value(s) to decide the consensus.

        - Exception to the above scenarios when F=N/2 is explained below.
        This exception was observed when varying MAXROUNDS.
        Example: F=2, N=4, INPUT=<<0,0,1,1>>, MAXROUND=2. This case resulted in an
        execution trace in which consensus wasn't reached. But for all the increased
        MAXROUNDS, this violation of property wasn't observed. This implies that
        low MAXROUNDS were not sufficient to ensure Fairness and this violates
        the progress property and model checker "stutters" in the end and terminates.
        "Stuttering" is when a process can choose not to run any step at all and
        it simply stops.
        This stuttering would happen whenever the rounds (MAXROUND) for a given
        INPUT are not sufficient enough for the algorithm to decide the desired values.
        The program counter "pc" sets to done before the "decided" variable was
        able to decide it's correct values, and the algorithm stutters. 

        - For cases where F were greater than N/2 like for example F=2 and N=3,
        progress property was violated because until the end of all rounds, not
        all processes would decide a value (0, 1), therefore proving the correctness.

-------------------------------------------------------------------------------

3. BaitProgress
    BaitProgress is essentially an invariant that says 'consensus can never be reached',
    which the model checker tries to contradict by finding some computations where
    all processes have "decided" value other than -1, consequently "baiting" the model
    checker into providing examples of consensus being reached in the traceback.
    By further analyzing the algorithm, we know consensus will not be reached when it's
    impossible for a majority to be reached. So our property is just checking if the
    number of 1's and 0's at the beginning of a "round" are equal, and if so, consensus
    cannot be reached.

    Observations and Correctness check:
        - We observed that bait property is independent of MAXROUNDS, so tested
        with MAXROUND=3
        - In our execution, our model violates the bait progress property and eventually
            finds a way to decide a value other than -1 which shows that the model reaches
            a consensus.
        - Our model violates bait progress property for following configurations which
            proves its correctness:
            i) F=1, N=4, input = <<0,1,1,1>>
            ii) F=0, N=4, input = <<0,0,1,1>>
            In this case, during it's execution, there would come a state where majority
            wasn't reached and a random value would be assigned for a process, which would
            shift the majority to either of the 0/1 and would ensure consensus.
            iii) F=1, N=4, input = <<0,0,1,1>>
            iv) F=2, N=4, input = <<0,0,1,1>>
            In the last two cases, the traces suggested that failing in a node would shift
            the majority to either of 0 or 1, and therefore lead to a consensus.

-------------------------------------------------------------------------------

4. Minority Report
    Minority Report is a safety property which claims that it is not possible
    for all the nodes to finalize with "0" as the consensus value if "0" is a
    minority in the INPUT (like «0,1,1,1)».
    We wrote a property which the model checker will try to prove wrong and produce
    a counterexample. The Minority Report property could is split between either
    minority of 0 in majority of 1 or vice verse. If either of them is true, then
    safety is proved by violation of the property.
    Tested with F=0, F=1, and F=2 for N = 4 and INPUT <<0,1,1,1>>

    Observation and Correctness check:
        - For F=0 and "0" is in minority in INPUT, then "0" can not be decided.
                This is because, since "0" is in minority, more than N/2 processes proposed
            same value ("1") which is decided as the consensus value.
        - For F=1 or F=2 and INPUT=<<0,1,1,1>, or F>=N/2, then "0" can be decided and
            Minority Report is violated.
                - The reason being, in Phase1's Message Board, no value is in majority, i.e.
                more than N/2. When one process crashes with value 1, it leaves Phase1's
                Message Board with two 1's, which is equal to N/2 (not a majority).
                This leads to "-1" being broadcasted in  Phase2's Message Board in the
                next round and random number being decided, which repeated after a few
                rounds produce a counterexample in which "0" is finalized as consensus
                value and Minority Report is violated.
                - This proves the correctness of MinorityReport property.
                - As per our observations of executions multiple of the algorithm for
                different INPUTS and N, we can simply formulate that for Minority Report
                to violate, F should at least be equal to N/2 -1.

-------------------------------------------------------------------------------

NOTE
- In our code and subsequent observations, we have used "nodes"/"processes"
 interchangeably.
- For observing model checker for the above properties, we restrict our
 MAXROUND to 4. For a high F and N value, we reduce MAXROUND to
 lower values because execution time started going beyond 30 minutes



------------------------------- MODULE BenOr -------------------------------
(*\* Ben-Or algorithm *)
EXTENDS Integers, Sequences, FiniteSets
\* N nodes; F possible failure; MAXROUND iteration of rounds
CONSTANT N, F, INPUT, MAXROUND
ASSUME N \in Nat /\ F < N
Procs == 1..N
(*
--algorithm BenOr
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

    macro NextRound(n,r)
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
			NextRound(node_id,r);
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
Agreement == (\A j,k \in Procs: decided[j] # -1 /\ decided[k] # -1 => decided[j]=decided[k])

\*PROGRESS
Progress == <>(\A d \in Procs: decided[d] # -1)

\*BAIT PROGRESS

\* BaitProgress == (\A d \in Procs: decided[d] = -1)

\* Util Variables: Count number of 0s and 1s in INPUT
m0 == (Cardinality({i \in Procs: (INPUT[i]=0)}))
m1 == (Cardinality({i \in Procs: (INPUT[i]=1)}))

\*MINORITY REPORT
MinorityReport0 == (\A p1 \in Procs: m1 > m0 => decided[p1] # 0)
MinorityReport1 == (\A p1 \in Procs: m1 < m0 => decided[p1] # 1)
MinorityReport == (MinorityReport0 /\ MinorityReport1)


\* ============================================================================
\* Submitted by:
\* Ameen M Khan (UBID: ameenmoh)
\* Sameer Singh Rathor (UBID: srathor)
\* Ben-Or Algorithm

\*  1. Agreement property
\* Agreement, as defined, is a property which should never be violated.
\* It should still hold even when F (failure nodes) is greater than majority of
\* processes (majority for our case is N/2, N is total number of processes).
\* As suggested, we tested our agreement  property with N<5 and F < 5,
\* with different values.
\* Our property to capture Agreement is that if two process "decide" a value
\* other than -1, they should be equal.

\* 2. Progress property
\* Progress property is a liveness property, which says good things do happen
\* and in PlusCal, they are usually defined using temporal (non deterministic)
\* operators. In BenOr, "progress" means if we start with all same preference values
\* (INPUT=«1,1,1,1» or «0,0,0,0» ), algorithm should terminate such that, every
\* process should eventually  have "decided" not -1.
\* This is exactly what we have modeled using eventual (<>) operator. <>P means
\* that for every possible behavior, at least one state has P as true.


\* 3. BaitProgress
\* BaitProgress is basically an invariant that says 'consensus can never be reached' 
\* and the model checker would try to find some computations where all processes 
\* will have "decided" value -1, and will consequently  provide examples of 
\* consensus being reached in the traceback. So the safety property here is
\* "baiting" the model checker into showing you that progress can be made and
\* gives scenarios of just that happening

\* 4. Minority Report
\*  MinorityReport is a safety property which claims that it is not possible
\* for all the nodes to finalize with "0" as the consensus value if "0" is a 
\* minority in the INPUT (like «0,1,1,1)».
\* We wrote a property which the model checker will try to prove  wrong 
\* by producing a counterexample. 
\* Tested with F=0, F=1, and F=2 for N = 4.


\* NOTE
\* - In our code and subsequent observations, we have used "nodes"/"processes" 
\*   interchangeably.
\* - For observing model checker for above properties, we restrict our
\*   MAXROUND to 4. For a high F and N value, we reduce MAXROUND to
\*   lower values because execution time started going beyond 30 minutes
=============================================================================

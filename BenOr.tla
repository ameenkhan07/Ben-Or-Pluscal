------------------------------- MODULE BenOr -------------------------------
(*\* Ben-Or algorithm *)
EXTENDS Integers, Sequences, FiniteSets
\* N nodes; F possible failure; MAXROUND iteration of rounds
CONSTANT N, F, MAXROUND, INPUT
ASSUME N \in Nat /\ F < N
Procs == 1..N
Rounds == 1..MAXROUND
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
SentPhase1Msgs(n,r) == {m \in p1Msg: (m.node_id # n) /\ (m.round=r)}
SentPhase1ValMsgs(n,r,b) == {m \in p1Msg: (m.node_id # n) /\ (m.round=r) /\ (m.val=b)}

SentPhase2Msgs(n,r) == {m \in p2Msg: (m.node_id # n) /\ (m.round=r)}
SentPhase2ValMsgs(n,r,b) == {m \in p2Msg: (m.node_id # n) /\ (m.round=r) /\ (m.val=b)}

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
             /\ (Cardinality(SentPhase1Msgs(node_id[self],r[self])) >= (N-F))
             /\ IF Cardinality(SentPhase1ValMsgs(node_id[self],r[self],0))*2 > (N)
                   THEN /\ p2v' = [p2v EXCEPT ![self] = 0]
                   ELSE /\ IF Cardinality(SentPhase1ValMsgs(node_id[self],r[self],1))*2 > (N)
                              THEN /\ p2v' = [p2v EXCEPT ![self] = 1]
                              ELSE /\ p2v' = [p2v EXCEPT ![self] = -1]
             /\ pc' = [pc EXCEPT ![self] = "P2"]
             /\ UNCHANGED << p1Msg, p2Msg, node_id, r, p1v, decided, v >>

P2(self) == /\ pc[self] = "P2"
            /\ p2Msg' = (p2Msg \union {[node_id |-> node_id[self], round |-> r[self], val |-> p2v[self]]})
            /\ pc' = [pc EXCEPT ![self] = "CP2"]
            /\ UNCHANGED << p1Msg, node_id, r, p1v, p2v, decided, v >>

CP2(self) == /\ pc[self] = "CP2"
             /\ (Cardinality(SentPhase2Msgs(node_id[self],r[self])) >= (N-F))
             /\ IF Cardinality(SentPhase2ValMsgs(node_id[self],r[self],0)) >= (F + 1)
                   THEN /\ v' = [v EXCEPT ![self] = 0]
                   ELSE /\ IF Cardinality(SentPhase2ValMsgs(node_id[self],r[self],1)) >= (F + 1)
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
             /\ IF SentPhase2ValMsgs(node_id[self],r[self],1) # {}
                   THEN /\ p1v' = [p1v EXCEPT ![self] = 1]
                   ELSE /\ IF SentPhase2ValMsgs(node_id[self],r[self],0) # {}
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
---------------------------------------------------------
Agreement == (\A j,k \in Procs: decided[j] # -1 /\ decided[k] # -1 => decided[j]=decided[k])

v0 == \A d \in Procs: decided[d] = 0
v1 == \A d \in Procs: decided[d] = 1
v3 == \A d \in Procs: decided[d] # -1
Progress == \A d \in Procs:
            \A ro \in Rounds:
            Cardinality(SentPhase2ValMsgs(d,ro,0)) = N \/
            Cardinality(SentPhase2ValMsgs(d,ro,1)) = N
            \* => v0 \/ v1
            => v3

m0 == Cardinality({i \in Procs: (INPUT[i]=0)})
m1 == Cardinality({i \in Procs: (INPUT[i]=1)})
MinorityReport0 == \A p1 \in Procs: m1 > m0 => decided[p1] # 0
MinorityReport1 == \A p1 \in Procs: m1 < m0 => decided[p1] # 1
MinorityReport == MinorityReport0 /\ MinorityReport1


=============================================================================
\* Ben Or algorithm

\*  1. Agreement Property
\* Agreement should never be violated. Even when F is more than majority of processes, 
\* Agreement should still hold. Agreement should always be satisfied, 
\* even when F is more than N/2. Test with N<5 and F < 5, with different values.

\* 2. Progress Report

\* 3. BaitProgress

\* 4. Minority Report
\* If N=4 and INPUT=«0,1,1,1», is it possible to have 0 decided for a run?
\* Write a safety property called MinorityReport which claims that it
\* is not possible for all the nodes to finalize with "0" as the consensus
\* value. The model checker will try to prove you wrong by producing a
\* counterexample when possible. Check this with F=0, F=1, and F=2.

=============================================================================

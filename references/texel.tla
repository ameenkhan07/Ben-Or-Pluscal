------------- MODULE texel --------------------
EXTENDS Integers, Sequences, FiniteSets
CONSTANT N, F
Procs == 1..N

(*
\* This is atomic version of Texel algorithm
\* Assumes process can poll every other process atomically
--algorithm texel
{ variable f=0, \* actual crash fault count in the system
           decision= <<"a","b","b","a", "a", "b", "a">>; \* hardwiring for N=4
define{
SupDecision == (CHOOSE r \in {"a","b"}: Cardinality({j \in Procs: decision[j]=r}) > F)
\* Because Choose is deterministic, progress is satisfied in this model
}

fair process (p \in Procs)
variable t=FALSE; \* t is the finality flag for the decision
{ 
S: while (t=FALSE /\ decision[self]#"crash"){
   either 
      { \* experiment and change your vote
       decision[self] := SupDecision;}
   or { await( f<F ); \* Fail me maybe
       decision[self] := "crash"; 
       f:=f+1;}
   or { \* Decide if you can
        if ( Cardinality({j \in Procs: decision[j]=decision[self]}) >= N-F )
           t:=TRUE;
       }    
  };
}
}
*)
\* BEGIN TRANSLATION
VARIABLES f, decision, pc

(* define statement *)
SupDecision == (CHOOSE r \in {"a","b"}: Cardinality({j \in Procs: decision[j]=r}) > F)

VARIABLE t

vars == << f, decision, pc, t >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ f = 0
        /\ decision = <<"a","b","b","a", "a", "b", "a">>
        (* Process p *)
        /\ t = [self \in Procs |-> FALSE]
        /\ pc = [self \in ProcSet |-> "S"]

S(self) == /\ pc[self] = "S"
           /\ IF t[self]=FALSE /\ decision[self]#"crash"
                 THEN /\ \/ /\ decision' = [decision EXCEPT ![self] = SupDecision]
                            /\ UNCHANGED <<f, t>>
                         \/ /\ ( f<F )
                            /\ decision' = [decision EXCEPT ![self] = "crash"]
                            /\ f' = f+1
                            /\ t' = t
                         \/ /\ IF Cardinality({j \in Procs: decision[j]=decision[self]}) >= N-F
                                  THEN /\ t' = [t EXCEPT ![self] = TRUE]
                                  ELSE /\ TRUE
                                       /\ t' = t
                            /\ UNCHANGED <<f, decision>>
                      /\ pc' = [pc EXCEPT ![self] = "S"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << f, decision, t >>

p(self) == S(self)

Next == (\E self \in Procs: p(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
---------------------------------------------------------
Agreement == (\A j,k \in Procs: t[j]=TRUE /\ t[k]=TRUE => decision[j]=decision[k])
Progress  == <> (\A j \in Procs: decision[j]#"crash" => t[j]=TRUE)
========================================================= 
Result:

This is a Pluscal model of Texel. It uses atomic actions. 
In one step a process can read other processes and change its decision. 
Both agreement and progress always satisfied for N>=3f+1.

Progress is always satisfied even for ambivalent initial state, because Choose is deterministic.
It will choose a when both a and b meets SupDecision criteria.

It is cute. Look ma, no rounds.

Next step is to reduce atomicity.

Quorum == {J \in SUBSET(Procs) : Cardinality(J) > N-F} 

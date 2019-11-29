------------- MODULE fpax1 --------------------
(*\* Flexible Paxos extension *)
EXTENDS Integers, Sequences, FiniteSets
CONSTANT M, N, STOP, MAXB, Quorum1, Quorum2, AcceptorSet
ASSUME M \in Nat /\ N \in Nat
ASSUME QuorumAssumption == /\ \A Q \in Quorum1 : Q \subseteq AcceptorSet
                           /\ \A Q \in Quorum2 : Q \subseteq AcceptorSet
                           /\ \A Q1 \in Quorum1 : \A Q2 \in Quorum2 : Q1 \cap Q2 # {}

\*\* In the model use  N=4, M=2, STOP=3 (number of slots), MAXB=5
\*\* AcceptorSet={1,2,3,4}, Quorum1={{1,2},{3,4}}, Quorum2={{1,3},{2,4},{1,4},{2,3}}
Acceptor == 1..N
Leader == N+1..N+M

Slots == 1..STOP
Ballots == 0..MAXB

(*
 --algorithm fpaxos
 { variable AccMsg={}, LMsg={};

   define{
   ExtractValSet(S) == {m.valSet : m \in S}
   SuitVal(S,s) == CHOOSE x \in S: x[1]=s /\ (\A z \in S:z[1]=s => x[2] >= z[2])

   SentAccMsgs(t,b) == {m \in AccMsg: (m.type=t) /\ (m.bal=b)}
   SentLMsgs(t,b) == {m \in LMsg: (m.type=t) /\ (m.bal=b)}
   SentLMsgs2(t,b,s) == {m \in LMsg: (m.type=t) /\ (m.bal=b) /\ (m.slot=s)}

   SatQ1(b) == \E Q \in Quorum1: \A a \in Q: \E m \in LMsg: m.type="p1b" /\ m.bal=b /\ m.acc=a
   SatQ2(b) == \E Q \in Quorum2: \A a \in Q: \E m \in LMsg: m.type="p2b" /\ m.bal=b /\ m.acc=a
  }

\* \* leader calls this to send p1a msg to acceptors
   macro SendP1 (b)
   {
     AccMsg:=AccMsg \union {[type |->"p1a", bal |-> b]};
   }

\* \* acceptor calls this to reply with a p1b msg to leader
   macro ReplyP1 (b)
   {
    await (b> maxBal) /\ (SentAccMsgs("p1a",b) #{});
    maxBal:=b;
    LMsg:=LMsg \union {[type |->"p1b", acc |-> self, bal |-> b, valSet |-> hVal]};
   }

\* \* leader calls this to collect p1b msgs from acceptors
   macro CollectP1 (b)
   {
    await \/ SatQ1(b)
          \/ (\E B \in Ballots: B>b /\ SentLMsgs("p1a",B)#{});
    if (~(\E B \in Ballots: B>b /\ SentLMsgs("p1a",B)#{})) {
       elected:=TRUE;
       pVal:=UNION ExtractValSet(SentLMsgs("p1b",b));
    }
   }


\* \* leader calls this to send p2a msg to acceptors
   macro SendP2 (b,s)
   {
    if (Cardinality({pv \in pVal: pv[1]=s})=0)
         AccMsg:=AccMsg \union {[type |-> "p2a", bal |-> b, slot |-> s, val |-> <<s,b,self>> ]};
    else AccMsg:=AccMsg \union {[type |-> "p2a", bal |-> b, slot |-> s, val |->SuitVal(pVal,s)]};
   }

\* \* acceptor calls this to reply with a p2b msg to leader
   macro ReplyP2 (b)
   {
    await (b>= maxBal);
    with (m \in SentAccMsgs("p2a",b)){
      maxBal:=b;
      hVal:= hVal \union {m.val}; \* update val heard with message of maxBal so far
      LMsg:=LMsg \union {[type |->"p2b", acc |-> self, bal |-> b, slot|-> m.slot, vv |->m.val[3] ]};
    }
   }

\* \* leader calls this to collect p1b msgs from acceptors
   macro CollectP2 (b,s)
   {
    await \/ SatQ2(b)
           \/ (\E B \in Ballots: B>b /\ SentLMsgs("p1a",B)#{});
    if (\E B \in Ballots: B>b /\ SentLMsgs("p1a",B)#{})
       elected:=FALSE;
    else with (m \in SentLMsgs("p2b",b)) {lv:=m.vv;}
   }

\* \* leader calls this to finalize decision for slot s
   macro SendP3 (b,s)
   {
    AccMsg := AccMsg \union {[type |-> "p3a", bal |-> b, slot |-> s, dcd |->lv ]};
   }

\* \* acceptor calls this to finalize decision for slot
   macro RcvP3 (b)
   {
    await (b>= maxBal);
    with (m \in SentAccMsgs("p3a",b)){
      maxBal:=b;
      decided[m.slot]:= decided[m.slot] \union {m.dcd};
    }
   }

\* \* Acceptor process actions
   fair process (a \in Acceptor)
   variable maxBal=-1, hVal={<<-1,-1,-1>>}, \* \* <<s,b,v>>
            decided=[i \in Slots |-> {}];
   {
A:  while (TRUE) {
     with (ba \in Ballots) {
      either ReplyP1(ba)
      or ReplyP2(ba)
      or RcvP3(ba)
     }
     }
   }


\* \* Leader process
   fair process (l \in Leader)
   variable b=self-N, s=1, elected=FALSE, lv=-1, pVal={<<-1,-1,-1>>}; \* \* <<s,b,v>>
   {
        L:  while (s \in Slots /\ b \in Ballots) {
        \*\* Try to get elected as leader first
        P1L:  while (elected # TRUE) {
                b:=b+M; \*\* guarantees unique ballot num
                SendP1(b);
        CP1L:     CollectP1(b);
            };
        \*\* Move to phase2
        P2L:  SendP2(b,s);
        CP2L: CollectP2(b,s);
        \*\* Move to phase 3
        P3L:  if (elected=TRUE){ \*\* leader may have been overthrown in P2
                SendP3 (b,s);
                s:=s+1;};
            }
        }
    }
*)
---------------------------------------------------------
\*\*  No acceptor could have finalized/decided 2 different vals for same slot
\*\* check the two below as invariant
Agreement == \A a1,a2 \in Acceptor:
              \A k \in Slots: Cardinality(decided[a1][k])=1
                           /\ Cardinality(decided[a2][k])=1 => decided[a1][k]=decided[a2][k]

Agreement2 == \A i \in Acceptor:
               \A k \in 1..STOP: Cardinality(decided[i][k]) <=1


\* \* Short cut for the above

Agreement3 == \A i \in Acceptor:
               \A k \in 1..STOP: Cardinality(decided[i][k]) <=1


\* Of course this is violated! Don't check this as invariant
No2Leaders == \A i,j \in Leader : elected[i] /\ elected[j] => i=j

\* Agreement ==
\*    \A i,j \in Acceptor :
\*        (   accepted[i] \subseteq accepted[j]
\*         \/ accepted[j] \subseteq accepted[i] )
=========================================================

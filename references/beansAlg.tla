------------ MODULE beansAlg ------------------
EXTENDS Integers
CONSTANTS M, N
ASSUME /\ M \in 1..100
       /\ N \in 1..100
       /\ M+N > 0

(*
--fair algorithm beansAlg {
   variable w=M, b=N;
  {S:while (TRUE)
     { either 
      {await (w>1); \* \* same color and white
      	  w:=w-1;
          };
       or
     {await (b>1); \* \* same color and black
          b:= b-2; w:= w+1;
         };            
       or
    {await (w>0 /\ b>0); \* \* different color
          w:= w-1;
         };            
      }
    }
   }
*)
\* BEGIN TRANSLATION
VARIABLES w, b

vars == << w, b >>

Init == (* Global variables *)
        /\ w = M
        /\ b = N

Next == \/ /\ (w>1)
           /\ w' = w-1
           /\ b' = b
        \/ /\ (b>1)
           /\ b' = b-2
           /\ w' = w+1
        \/ /\ (w>0 /\ b>0)
           /\ w' = w-1
           /\ b' = b

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION
TypeOK ==  \* /\ w \in 0..100
           \* /\ b \in 0..100
           w+b>0
NonTermination == w+b>1
Termination == <> (w+b < 2)

============================================
Consider a can of coffee beans.

Each bean is either white or black.  The can is initially
nonempty (w+b>0).  Now consider the following program: 

Choose two beans from the can;

- if they are the same color, toss them out and put in a white bean

- if they are different colors, toss them out and put in a black bean


This action is repeated.

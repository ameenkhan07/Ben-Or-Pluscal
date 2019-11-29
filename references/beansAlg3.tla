------------ MODULE beansAlg3 ------------------
EXTENDS Integers
CONSTANTS R, G, B
ASSUME /\ R \in 1..100
       /\ G \in 1..100
       /\ B \in 1..100
       /\ R+G+B > 0

(*
--fair algorithm beansAlg3 {
   variable r=R, g=G, b=B;
   { S: while (TRUE)
     { either 
        {await (r>1); \* same color and red
	   Ar:        r:=r-2; g:=g+1; b:=b+1;
          };
       or
         {await (b>1);  \* same color and blue
	    Ab:        b:=b-2; r:=r+1; g:=g+1; 
          };
       or   
         {await (g>1);  \* same color and green
	    Ag:        g:=g-2; r:=r+1; b:=b+1;
          };
       or
         {await (r>0 /\ b>0);  \* different color and r and b
        Arb:         r:= r-1; b:=b-1; g:=g+1;
         };            
       or
        {await (r>0 /\ g>0); \* different color and r and g
         Arg:         r:= r-1; g:=g-1; b:=b+1;
         };            
       or
         {await (b>0 /\ g>0); \* different color and b and g
        Abg:         b:= b-1; g:=g-1; r:=r+1;
         };            

      }\* end while
    }\* end alg
   }\* end alg
*)
\* BEGIN TRANSLATION
VARIABLES r, g, b, pc

vars == << r, g, b, pc >>

Init == (* Global variables *)
        /\ r = R
        /\ g = G
        /\ b = B
        /\ pc = "S"

S == /\ pc = "S"
     /\ \/ /\ (r>1)
           /\ pc' = "Ar"
        \/ /\ (b>1)
           /\ pc' = "Ab"
        \/ /\ (g>1)
           /\ pc' = "Ag"
        \/ /\ (r>0 /\ b>0)
           /\ pc' = "Arb"
        \/ /\ (r>0 /\ g>0)
           /\ pc' = "Arg"
        \/ /\ (b>0 /\ g>0)
           /\ pc' = "Abg"
     /\ UNCHANGED << r, g, b >>

Ar == /\ pc = "Ar"
      /\ r' = r-2
      /\ g' = g+1
      /\ b' = b+1
      /\ pc' = "S"

Ab == /\ pc = "Ab"
      /\ b' = b-2
      /\ r' = r+1
      /\ g' = g+1
      /\ pc' = "S"

Ag == /\ pc = "Ag"
      /\ g' = g-2
      /\ r' = r+1
      /\ b' = b+1
      /\ pc' = "S"

Arb == /\ pc = "Arb"
       /\ r' = r-1
       /\ b' = b-1
       /\ g' = g+1
       /\ pc' = "S"

Arg == /\ pc = "Arg"
       /\ r' = r-1
       /\ g' = g-1
       /\ b' = b+1
       /\ pc' = "S"

Abg == /\ pc = "Abg"
       /\ b' = b-1
       /\ g' = g-1
       /\ r' = r+1
       /\ pc' = "S"

Next == S \/ Ar \/ Ab \/ Ag \/ Arb \/ Arg \/ Abg

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION

TypeOK == /\ r \in 0..200
          /\ g \in 0..200
          /\ b \in 0..200
RunsForEver == r+g+b>=1          
Termination == <> (r+g+b < 2)

============================================ 

Consider a coffee can containing an arbitrary (but finite) number of beans. The
beans come in 3 different colors: red, green, and blue. Now consider the
following program:

Choose two beans from the can;

if they are the same color, toss them out and add two beans for the other two
colors

if they are different colors, toss them out and add a bean of the third color

Repeat.

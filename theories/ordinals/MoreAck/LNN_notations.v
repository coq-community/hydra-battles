Require Import fol Languages PAtheory LNN.
Require Import FOL_notations. 
Import FOL_notations. 
(*** Expermimental ***)


Module LNN_notations.

Set Printing Implicits. 
Check Zero. 
Locate Zero. 
Notation zero := (@apply _ (Languages.Zero: Functions LNN) (fol.Tnil)).
Check zero.


Notation "t1 + t2" := 
  (apply  _ Languages.Plus 
     (Tcons t1 (Tcons t2 (Tnil)))): 
    fol_scope.


Notation "t1 * t2" := (apply  _ Languages.Times 
     (Tcons  t1 
        (Tcons  t2 (Tnil)))): fol_scope.

Notation S_ t  := (Succ t).
   
About atomic. 

Locate Times.
Locate LT. 
Print LT. 
Infix "<" := LNN.LT : fol_scope. 
Infix "+" := LNN.Plus : fol_scope.
Infix "*" := LNN.Times: fol_scope. 

Reserved Notation "x <' y" (at level 70, no associativity).
Notation "t1 <' t2" := (@atomic Languages.LT (Tcons t1 (Tcons t2 Tnil))): fol_scope.

End LNN_notations.






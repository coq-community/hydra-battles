From Coq Require Import Arith Lists.List.
Require Import fol folProp Languages LNN.
Require Import LNN_notations. 

Import LNN_notations.

Require Import LNN.

Example t1_0 := (v_ 1 + zero)%lnn. 
Check t1_0. 
Goal t1_0 = Plus (var 1) Zero. 
reflexivity. 
Qed. 

Print t1_0.
Unset Printing Notations.  

Compute t1_0. 
Set Printing Notations.  
Section Examples.

(* begin snippet v1Plus01 *)
Let t1: Term  := Plus (var 1) Zero. 
(* end snippet v1Plus01 *)

Compute t1. 

(** forall v0, v0 = 0 \/ exists v1,  v0 = S v1 *)
(* begin snippet f1Example *)
Let f1 : Formula  :=
  (allH 0 
    (v_ 0 = zero \/
          exH 1 (v_ 0 = S_ (v_ 1))))%lnn.
(* end snippet f1Example *)

Compute f1. 
Import LNN_notations CLNN_notations. 

Compute f1. 

(* begin snippet f2Example *)
Let f2 : Formula :=
   (exH 2 (zero < v_ 2 /\ natToTerm 4 = v_ 2 + v_ 2))%lnn.

Let f3 := (v_ 0 = zero \/ exH 1 (v_ 0 = S_ (v_ 1)))%lnn.


Let f4 := (v_ 0 = v_ 1 + v_ 1 <-> v_ 0 = v_ 1 * (natToTerm 2))%lnn.
(* end snippet f2Example *)

Compute f4. 
Print f4.

(* begin snippet depthCompute *)
Compute (depth _ f1, depth _ f2).
(* end snippet depthCompute *)
(* begin snippet freeVarExamples *)
Compute  freeVarFormula _ f3.

Compute ListExt.no_dup _ Nat.eq_dec (freeVarFormula _ f3).

Compute close _ f3.

Compute freeVarFormula _ f3.

Compute freeVarFormula _ (close _ f4).

Compute substituteFormula LNN f4 0 (natToTerm 0).
(* end snippet freeVarExamples *)


End Examples. 




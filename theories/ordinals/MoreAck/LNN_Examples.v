From Coq Require Import Arith Lists.List.
Require Import fol folProp Languages LNN.
Require Import fol_Examples.

Import FOL_notations.
Import FOL_notations.

Require Import LNN.

Check t1_0. 
Goal t1_0 = Plus (var 1) Zero. 
reflexivity. 
Qed. 

Print t1_0.
(*
t1_0 = 
apply LNN Languages.Plus
  (Tcons LNN 1 (fol.var LNN 1)
     (Tcons LNN 0 (apply LNN Languages.Zero (Tnil LNN)) (Tnil LNN)))
     : fol.Term LNN
*)
Compute t1_0. 
(*
apply LNN Languages.Plus
         (Tcons LNN 1 (fol.var LNN 1)
            (Tcons LNN 0 (apply LNN Languages.Zero (Tnil LNN)) (Tnil LNN)))
*)

Section Examples.

(* begin snippet v1Plus01 *)
Let t1: Term  := Plus (var 1) Zero. 
(* end snippet v1Plus01 *)


(** forall v0, v0 = 0 \/ exists v1,  v0 = S v1 *)
(* begin snippet f1Example *)
Let f1 : Formula  :=
  (allH 0 
    (v_ 0 = Zero \/
          exH 1 (v_ 0 = Succ (v_ 1))))%fol.
(* end snippet f1Example *)

(* begin snippet f2Example *)
Let f2 : Formula :=
   (existH 2 (andH (LT Zero (var 2))
                 (equal (natToTerm 4) (Plus (var 2) (var 2))))).

Let f3 := (orH (equal (var 0) Zero)
             (existH 1 (equal (var 0) (Succ (var 1))))).

Let f4 := (iffH (equal (var 0) (Plus (var 1) (var 1)))
                (equal (var 0) (Times (var 1) (natToTerm 2)))).
(* end snippet f2Example *)

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




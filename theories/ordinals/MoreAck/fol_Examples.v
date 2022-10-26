From Coq Require Import Arith Lists.List.
Require Import fol folProp Languages.
Require Import primRec.

Locate arity. 

(* begin snippet arityTest *)
Compute arity LNT (inr Languages.Plus). 
Compute arity LNN (inr Languages.Succ). 
Compute arity LNN (inl Languages.LT). 
Fail Compute arity LNT (inl Languages.LT).
(* end snippet arityTest *)

Check var _ 1: Term LNN.


Check  @apply LNT Languages.Zero (Tnil _) : fol.Term LNT. 

(* begin snippet v1Plus0 *)
(** v1 + 0 *)
Example t1_0: Term LNN :=
 apply LNN Plus 
   (Tcons LNN _ (var LNN  1)
     (Tcons LNN _ (apply LNN Zero (Tnil _)) (Tnil _))). 
(* end snippet v1Plus0 *)

(* begin snippet instantiations *)
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
  forallH 0 
    (orH (equal (var 0) Zero)
          (existH 1 (equal (var 0) (Succ (var 1))))).
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

(* begin snippet FormulaRect *)
About Formula_rect.
(* end snippet FormulaRect *)

(** depth-order vs structural order *)
(* begin snippet ltDepth1:: no-out *)
Goal lt_depth _ f1  f2.
Proof. red; cbn; auto with arith. Qed. 
(* end snippet ltDepth1 *)

(* begin snippet freeVarExamples *)
Compute  freeVarFormula _ f3.

Compute ListExt.no_dup _ Nat.eq_dec (freeVarFormula _ f3).

Compute close _ f3.

Compute freeVarFormula _ f3.

Compute freeVarFormula _ (close _ f4).

Compute substituteFormula LNN f4 0 (natToTerm 0).
(* end snippet freeVarExamples *)


End Examples. 


Section depth_rec_demo. 
Variable L: Language.
Variable P: fol.Formula L -> Prop. 
Variable a: fol.Formula L. 
Goal P a. 
  eapply  Formula_depth_rec_rec with (depth L a); [| apply le_n].
  (* begin snippet depthRecDemo:: unfold no-in *)
 clear a; intros a Ha.
  (* end snippet depthRecDemo *)
Abort.
Goal P a. 
 (* begin snippet depthRecDemo2:: unfold no-in *)
 apply Formula_depth_ind2.
 (* end snippet depthRecDemo2 *)
Abort. 




End depth_rec_demo. 




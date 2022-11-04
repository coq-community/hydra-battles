From Coq Require Import Arith Lists.List.
Require Import fol folProp Languages.
Require Import primRec.

Require Import FOL_notations.
Import FOL_notations. 


Locate arity. 

(* begin snippet arityTest *)
Compute arity LNT (inr Languages.Plus). 
Compute arity LNN (inr Languages.Succ). 
Compute arity LNN (inl Languages.LT). 
Fail Compute arity LNT (inl Languages.LT).
(* end snippet arityTest *)

Check var _ 1: Term LNN.


Check  @apply LNT Languages.Zero (Tnil _) : fol.Term LNT. 

Section Examples. 

(* begin snippet v1Plus0 *)
(** v1 + 0 *)
Example t1_0: Term LNN :=
 apply LNN Plus 
   (Tcons LNN _ (var LNN  1)
     (Tcons LNN _ (apply LNN Zero (Tnil _)) (Tnil _))). 
(* end snippet v1Plus0 *)
Print t1_0. 

(** forall v0, v0 = 0 \/ exists v1,  v0 = S v1 *)
(* begin snippet f1Example *)
Let f1 : Formula LNN :=
      forallH LNN 0 
        (orH _ (equal _ (var _ 0) (apply LNN Zero (Tnil _)))
           (existH _ 1 (equal _ (var _ 0)
                          (apply LNN Succ 
                             (Tcons _ _ (var _ 1) (Tnil _)))))).

Let f2 : Formula LNN :=
(existH _ 1 (equal _ (var _ 0)
                          (apply LNN Succ 
                             (Tcons _ _ (var _ 1) (Tnil _))))).

Let f3 := (orH LNN (equal _ (var _ 0) (apply LNN Zero (Tnil _)))
             (existH _ 1 (equal _ (var _ 0) (apply LNN Succ 
                             (Tcons _ _ (var _ 1) (Tnil _)))))).
(* end snippet f1Example *)

Print f3.

(* begin snippet FormulaRect *)
About Formula_rect.
(* end snippet FormulaRect *)

(** depth-order vs structural order *)
(* begin snippet DepthCompute *)
Compute depth _ f1.
(* end snippet DepthCompute *)

(* begin snippet ltDepth1:: no-out *)
Goal lt_depth _ f2 f1. 
cbn. red; auto with arith. 
Qed.
(* end snippet ltDepth1 *)

(* begin snippet freeVarExamples *)
Compute  freeVarFormula _ f2.

Compute ListExt.no_dup _ Nat.eq_dec (freeVarFormula _ f3).

Compute close _ f3.

Compute freeVarFormula _ f3.

Compute freeVarFormula _ (close _ f3).

Compute substituteFormula LNN f3 0 (apply LNN Zero (Tnil _)) . 
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




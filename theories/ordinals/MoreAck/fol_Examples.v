From Coq Require Import Arith Lists.List.
Require Import fol folProp .


Require Import FOL_notations.
Import FOL_notations. 


Declare Scope Cfol. 
Delimit Scope Cfol with cfol. 
Module CFOL_notations.
Notation " A -> B" := (@fol.impH _ A B)%fol : Cfol.
Notation " A \/ B" := ((@fol.notH _  A) -> B)%cfol : Cfol.
Notation " A /\ B" := (@fol.notH _ (@fol.notH _  A \/ @fol.notH _ B))%cfol: Cfol.
Notation "~ A" := (@fol.notH _ A): Cfol.
Notation exH v A := (@fol.notH _ (@fol.forallH _ v (~ A)%cfol)).

Goal forall L (A B: Formula L), (A \/ B)%cfol = (A \/ B)%fol.
reflexivity. 
Qed.

Goal forall L (A B: Formula L), (A /\ B)%cfol = (A /\ B)%fol.
reflexivity. 
Qed.


End CFOL_notations.
Import CFOL_notations.

Module Toy.


Inductive Fun : Set := _f | _g | _h | _a | _b.
Inductive Rel : Set := _P | _R | _S.

Definition arity (x: Rel + Fun): nat :=
  match x with
    inl _P => 1 
  | inl _ => 2
  | inr _f | inr _g => 1
  | inr _h => 2
  | inr _a | inr _b => 0
  end.

Definition L := language Rel Fun arity.

Notation f x := (app1 (_f: Functions L) x).
Notation g x := (app1 (_g: Functions L) x).
Notation h  x y := (app2 (_h: Functions L) x y).
Notation a := (k_ (_a : Functions L)).
Notation b := (k_ (_b : Functions L)).

Notation P t := (fol.atomic L (_P: Relations L) (Tcons _ _ t (Tnil _))).
Notation R t1 t2 :=
  (fol.atomic L (_R: Relations L) (Tcons _ _ t1 (Tcons _ _ t2  (Tnil _)))).

Notation S t1 t2 :=
  (fol.atomic L (_S: Relations L) (Tcons _ _ t1 (Tcons _ _ t2  (Tnil _)))).




Check f (v_ 1).
Check a. 
Check f a. 
Check (allH 1 (v_ 1 = a))%fol. 
Check (R (v_ 1) (v_ 2))%fol. 

Compute arity (inr _f).
Compute arity (inl _S).
Print app2.
Check apply L _h (Tcons _ _ (var _ 1) (Tcons _ _ (var _ 0) (Tnil _))).



Check (app2  (_h: Functions L)  (var _ 1) (var _ 2))%fol: Term L.
Check (h (v_ 1) (v_ 2))%fol.


Goal Sentence L (allH  1 (v_ 1 = v_ 1))%fol. 
intro v; cbn ; tauto. 
Qed. 

Goal ~ Sentence L (allH  0 (v_ 1 = v_ 1))%fol. 
intro H. specialize (H 1). cbn in H; tauto. 
Qed. 

Let f1 : Formula L :=
      (allH 0 (v_ 0 = a \/ exH 1 (v_ 0 = f (v_ 1))))%fol.

Let f2 : Formula L :=
      (exH  1 (v_ 0 = f (v_ 1)))%fol. 

Let f3 := (v_ 0 = a \/ exH 1 (v_ 0 = f (v_ 1)))%fol.


Module MyModule. 
#[local] Notation f x := (app1 (_f: Functions L) x)%fol.
#[local] Notation g x := (app1 (_g: Functions L) x)%fol.

Compute substituteFormula L f3 0 (g (v_ 1))%fol. 

Goal substituteFormula L f3 0 (g (v_ 1))%fol =
       (g (v_ 1) = a \/ exH 2 (g (v_ 1) = f (v_ 2)))%fol.
reflexivity. 
Qed. 



End MyModule. 
End Toy. 






Require Import Languages.
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

Check Sentence. 


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




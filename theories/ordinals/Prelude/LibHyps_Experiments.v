From LibHyps Require Export LibHyps.

Tactic Notation (at level 4) tactic4(Tac) "/" "dr" := Tac ; {< fun h
=> try revert dependent h }.
Tactic Notation (at level 4) tactic4(Tac) "/" "r?" :=
  Tac ; {< fun h  => try revert h }.


(*  move to experimental file (not to export *)

Require Import List.
Import ListNotations. 
Local Open Scope autonaming_scope.

Ltac old_tac := rename_hyp_default.

Ltac rename_hyp_default n th :=
  match th with
  | (?f ?x ?y ?z ?t ?u) => name ((f # 1) ++ (x # n) )
  | (?f ?x ?y ?z ?t)=> name ( (f # 1) ++ (x # 1))
  | (?f ?x  ?y ?z)=> name ( (f # 1) ++ (x # 1))
  | (?f ?x ?y) => name ((f # 1) ++ (x # 1))                          
  | (?f ?x) => name ((f # 1))
  | _ => old_tac n th
   end.

Ltac rename_hyp n th ::= rename_hyp_default n th.

Goal forall n p , n <= p -> forall q, p <= q -> n <= q.
induction 1  /n.
- intros; assumption.
- intros  /n.  apply h_all_le_n_; transitivity (S m); auto.
Qed.

Require Import Arith. 
Parameters f g h : nat -> nat.
Parameter P : nat->nat->nat-> Prop.
Goal forall x y ,  f (g (h x)) = h (g (f y)) -> x = y -> x < y ->  P  x y x  -> f y <> f x.
  intros x y H H0 H1 H2 /n. subst y.
  absurd (x < x) ; trivial. 
  apply Nat.lt_irrefl. 
Qed. 

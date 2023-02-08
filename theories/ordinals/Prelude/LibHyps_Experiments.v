From LibHyps Require Export LibHyps.
Require Export MoreLibHyps. 

(*  move to experimental file (not to export *)

Require Import List.
Import ListNotations. 
#[local] Open Scope autonaming_scope.

Ltac rename_hyp n th ::= rename_short n th.

Goal forall n p , n <= p -> forall q, p <= q -> n <= q.
induction 1  /n.
- intros; assumption.
- intros /n.  apply h_all_le_n_; transitivity (S m); auto.
Qed.

Goal forall n p , n <= p -> forall q, p <= q -> n <= q.
  intros * H; destruct H /dr.
  - intros /n.  assumption.
  - intros /n.  transitivity (S m); auto.
Qed.

Require Import Arith. 
Parameters f g h : nat -> nat.
Parameter P : nat->nat->nat-> Prop.
Goal forall x y ,  f (g (h x)) = h (g (f y)) -> x = y -> x < y ->
                   P  x y x  -> f y <> f x.
  intros x y H H0 H1 H2 /n. subst y.
  absurd (x < x) ; trivial. 
  apply Nat.lt_irrefl. 
Qed. 

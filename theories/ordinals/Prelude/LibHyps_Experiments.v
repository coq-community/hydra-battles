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
  | (?f ?x ?y) => name ((f # 1))
  | (?f ?x   ?y ?z)=> name ((f # 1) ++ (x # 1))
  | (?f ?x ?y ?z ?t)=> name ((f # 1) ++ (x # 1))
  | (?f ?x ?y ?z ?t ?u) => name ((f # 1) ++ (x # 1) )
  | _ => old_tac n th
   end.

Ltac rename_hyp n th ::= rename_hyp_default n th.

Goal forall n p , n <= p -> forall q, p <= q -> n <= q.
induction 1  /n.
- intros; assumption.
- intros  /n; apply h_all_le_; transitivity (S m); auto.
Qed.


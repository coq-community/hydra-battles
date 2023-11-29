From LibHyps Require Import LibHyps.

Tactic Notation (at level 4) tactic4(Tac) "/" "dr" := 
  Tac ; {< fun h => try generalize dependent h }.

Tactic Notation (at level 4) tactic4(Tac) "/" "r?" :=
  Tac ; {< fun h  => try revert h }.


From Coq Require Import List.
Import ListNotations. 
#[local] Open Scope autonaming_scope.


(*  move to experimental file (not to export *)


Ltac old_rename := rename_hyp_default.

Ltac rename_short n th :=
  match th with
  | (?f ?x ?y) => name ((f # 1) ++ (x # 1))                          
  | (?f ?x) => name ((f # 1))
  | _ => old_rename n th
  end.

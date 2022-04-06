(** Learning ssreflect:  *)

From mathcomp Require Import all_ssreflect zify.
From hydras Require Import Canon Paths.
Require Import T1Bridge GCanon.

Lemma diffP {T:eqType}(i j:T): i <> j <-> i != j.
Proof.
  split => H.
  - case E: (eq_op i j) => //.
    have H1: i = j by apply /eqP => //.
    by move: (H H1). 
    move => E; subst; move: H; by rewrite eq_refl.  
Qed.

(* To clean ! *)

Lemma eq_op_sym {T:eqType}{x y: T}: (x == y) = (y == x). 
Proof. 
  case E: (x == y) => //.
  case E': (y == x) => //.
  have H: x = y by apply /eqP; subst.
  move: E. subst. by rewrite E'.
  have H: x <> y. apply diffP. by rewrite E. 
  have H': y<>x by congruence. 
  symmetry; have H0: y != x by apply diffP. 
  move : H0; case (y == x) => //.
Qed.

Lemma diffsym {T:eqType}{x y: T}: (x != y) = (y != x). 
Proof. 
 by rewrite eq_op_sym.  Qed. 
  

(*
Search orderType.
Locate mixin. 
Print Order.Total.mixin.


Search "mixin".
 *)

Definition T1POrder_mixin :  Order.POrder.mixin_of  T1_eqMixin.
Proof. 
  eexists T1le T1lt.
  - move => x y. Search T1le T1lt andb.
    rewrite T1lt_neAle => //.
    by rewrite diffsym.
    move => x. rewrite /T1le => //=.  by rewrite eq_refl.
    move => x y. Search eq ((?x <= ?y) && (?y <= ?x)). 
    rewrite -T1eq_le.  apply /eqP. 
    move => x y z. 
    apply T1le_trans. 
Defined.


Set Printing All. 
Check (3 <= 3)%N. 
Search ssrnat.leq.
Locate ssrnat.leq. 


Print Order.POrder.class_of. 
(*

Record class_of (T : Type) : Type := Class
  { base : Choice.class_of T;  mixin : Order.POrder.mixin_of base }.
*)


Print Order.POrder.mixin_of.
(*
Record class_of (T : Type) : Type := Class
  { base : Choice.class_of T;  mixin : Order.POrder.mixin_of base }.
*)

Check  @Order.POrder.Pack tt T1.

Print Choice.class_of. 
Print choiceMixin. 
Print Choice.mixin_of.




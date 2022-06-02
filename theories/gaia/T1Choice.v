(** Experimental *)

From mathcomp Require Import all_ssreflect zify.
From Coq Require Import Logic.Eqdep_dec.
From hydras Require Import DecPreOrder ON_Generic  T1 E0.
From gaia Require Export ssete9.
Require Import T1Bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint T12Tree (a: T1): GenTree.tree nat :=
  if a is cons b n c
  then GenTree.Node n [:: T12Tree b; T12Tree c]
  else GenTree.Leaf 0.                                        

Fixpoint Tree2T1 (t: GenTree.tree nat): option T1 :=
  match t with
  | GenTree.Leaf 0 => Some zero
  | GenTree.Node n [:: t1; t2] =>
      match Tree2T1 t1, Tree2T1 t2 with
      | Some b, Some c => Some (cons b n c)
      | _, _ => None
      end
  | _ => None
  end.

Lemma TreeT1K : pcancel T12Tree Tree2T1. 
Proof. 
  elim => //.
  move => t Ht n t0 Ht0 /=; by rewrite Ht0 Ht. 
Qed.                                              

 
Lemma  T12Tree_inj: injective T12Tree.   
Proof.
  move => t1 t2 Heq.
  have H: Some t1 = Some t2 by rewrite -!TreeT1K Heq. 
  by injection H. 
Qed.

Definition T1mixin :
  Countable.mixin_of T1 := PcanCountMixin TreeT1K.

Canonical T1Choice :=
  Eval hnf in ChoiceType T1 (CountChoiceMixin T1mixin).

Example ex_pos: exists alpha: T1, zero != alpha. 
Proof. exists (cons zero 0 zero) => //. Qed. 

Example some_pos: T1 := xchoose ex_pos. 

Example some_pos' : T1 := choose (fun p : T1 => zero != p)
                                 T1omega.
Goal zero != some_pos'. 
  pose p a := (zero != a); move: (@chooseP _ p T1omega).
  rewrite /p /some_pos' => H; by apply: H. 
Qed.

(*Check tree_countType nat_countType. 

Check @PcanCountMixin (tree_countType nat_countType) T1
                      T12Tree _ TreeT1K. 

Check PcanCountMixin TreeT1K.
Compute  (Choice.class_of T1). 
*)

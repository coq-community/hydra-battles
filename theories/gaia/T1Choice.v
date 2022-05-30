(** Experimental *)

From mathcomp Require Import all_ssreflect zify.
From Coq Require Import Logic.Eqdep_dec.
From hydras Require Import DecPreOrder ON_Generic  T1 E0.
From gaia Require Export ssete9.
Require Import T1Bridge.
(* end snippet Requirements *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint T12Tree (a: T1): GenTree.tree nat :=
  if a is cons b n c
  then GenTree.Node n [:: T12Tree b; T12Tree c]
  else GenTree.Leaf 0.                                        

Lemma  T12Tree_inj: injective T12Tree.
Proof.
  rewrite /injective; elim; first by case.
  move => t Ht n t0 Ht0 ; case => //=. 
  move => t1 n0 t2 /= H; injection H; clear H. 
  move /Ht0 => ->; by move /Ht => -> ->.
Qed.


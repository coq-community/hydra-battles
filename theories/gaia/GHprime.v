
(** Gaia-compatible [H'_ alpha] fast growing functions  

(imported from [hydras.Epsilon0.Hprime] )
*)


(* begin snippet Requirements:: no-out  *)
From mathcomp Require Import all_ssreflect zify.
From gaia Require Export ssete9.
From Coq Require Import Logic.Eqdep_dec.
From hydras Require Import DecPreOrder.
From hydras Require Import T1 E0.
From hydras Require Paths.
From hydras Require Import primRec PrimRecExamples. 
From hydras Require Import  Hprime.
From gaia_hydras Require Import T1Bridge GCanon GPaths.
(* end snippet Requirements *)

Set Implicit Arguments.
Unset Strict Implicit.

Notation hH'_ := Hprime.H'_. 

Definition H'_ alpha i := hH'_ (E0_g2h alpha) i.



(** ** Equations for [H'_] *)

Lemma H'_eq1 (i: nat) : H'_ E0zero i = i. 
Proof. by rewrite /H'_  g2h_E0zero Epsilon0.Hprime.H'_eq1.  Qed.

Lemma H'_eq2  alpha i :
  H'_ (E0succ alpha) i = H'_ alpha (S i).
Proof.
  destruct alpha; by rewrite /H'_  g2h_E0succ  H'_eq2.   
Qed.

Lemma H'_eq3 alpha i :
  E0limit alpha ->  H'_ alpha i =  H'_ (E0Canon alpha (S i)) i.
Proof. 
  rewrite /E0limit /H'_ => H; rewrite H'_eq3 => //; f_equal.
  apply E0_eq_intro => /=;  by rewrite g2h_canon.
Qed.



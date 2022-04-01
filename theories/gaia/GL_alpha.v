
(** Gaia-compatible [L_ alpha] fast growing functions  

(imported from [hydras.Epsilon0.Hprime] )
*)


(* begin snippet Requirements:: no-out  *)
From mathcomp Require Import all_ssreflect zify.
From gaia Require Export ssete9.
From Coq Require Import Logic.Eqdep_dec.
From hydras Require Import DecPreOrder.
From hydras Require Import T1 E0.
From hydras Require Paths L_alpha.
From hydras Require Import primRec PrimRecExamples. 
From hydras Require Import  L_alpha.
From gaia_hydras Require Import T1Bridge GCanon GPaths.
(* end snippet Requirements *)

Set Implicit Arguments.
Unset Strict Implicit.

Definition L_ (alpha:E0) (i:nat): nat :=
  hydras.Epsilon0.L_alpha.L_  (E0_g2h alpha) i. 

Lemma L_zero_eqn i :  L_ E0zero i = i.
Proof. by rewrite /L_. Qed.

Lemma L_eq2 alpha i :
  E0is_succ alpha -> L_ alpha i = L_ (E0pred alpha) (S i).
Proof.
  move => H;  case (E0is_succE H) => x Hx; subst.
  rewrite E0pred_succK /L_ hydras.Epsilon0.L_alpha.L_eq2 => //. 
  f_equal; rewrite g2h_E0succ; by rewrite E0pred_of_Succ. 
Qed. 


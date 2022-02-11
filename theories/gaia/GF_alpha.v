(* begin snippet Requirements:: no-out  *)
From Coq Require Import Logic.Eqdep_dec.
From hydras Require Import DecPreOrder.
From hydras Require Import T1 E0.
From mathcomp Require Import all_ssreflect zify.
From gaia Require Export ssete9.
Set Bullet Behavior "Strict Subproofs".
(* end snippet Requirements *)

Require Import T1Bridge.

Set Implicit Arguments.
Unset Strict Implicit.

(** *  Rapidly growing functions *)

(* TODO: move to a specific file *)



(* begin snippet FAlphaDef *)
From hydras Require Import F_alpha.

Notation hF_ := F_.

Definition F_ (alpha : E0)  := hF_ (E0_g2h alpha).
(* end snippet FAlphaDef *)

Definition T1F_ (alpha :T1)(Hnf : T1nf alpha == true) (n:nat) : nat.
Proof. refine (F_ (@mkE0 alpha _) n); by rewrite Hnf.  Defined.

Lemma T1F_eq alpha (Hnf : T1nf alpha == true) (n:nat) :
  F_ (@mkE0 alpha Hnf) n = T1F_  Hnf n.
Proof.
  rewrite /T1F_; f_equal; apply gE0_eq_intro => //. 
Qed.

(* begin snippet FAlphaProps:: no-out *)
Lemma F_alpha_ge_S (alpha : E0) (n : nat): (n < F_ alpha n)%N.
Proof.
   apply /ltP; apply F_alpha_ge_S.
Qed.

Lemma gF_alpha_mono (alpha: E0): strict_mono (F_ alpha).
Proof.
  rewrite /strict_mono /F_ => n p Hnp; apply /ltP.
  apply F_alpha_mono; move: Hnp => /ltP //.
Qed.


Lemma gF_alpha_dom alpha:
  dominates_from 1 (F_ (E0succ alpha)) (F_ alpha).
Proof.
  rewrite /dominates_from /F_ g2h_E0succ => p Hp.
  apply /ltP; apply F_alpha_dom; by apply /leP.
Qed. 
(* end snippet FAlphaProps *)

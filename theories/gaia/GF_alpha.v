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
Lemma gF_alpha_ge_S (alpha : E0) (n : nat): (n < F_ alpha n)%N.
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

Lemma gF_alpha_Succ_le alpha:
 fun_le (F_ alpha) (F_ (E0succ alpha)).
Proof.
  rewrite /fun_le /F_ g2h_E0succ => n.
  apply /leP; apply F_alpha_Succ_le. 
Qed. 

Lemma gF_alpha_positive (alpha : hE0) (n : nat): (0 < hF_ alpha n)%N.
Proof.
  rewrite /F_. apply /ltP ; apply Lt.le_lt_trans with n;
    [ auto with arith| apply F_alpha_ge_S].
Qed.

Lemma gF_zero_eqn i: F_ E0zero i = i .+1.
Proof.
  rewrite /F_ . replace (E0_g2h E0zero) with Zero.
  by rewrite F_zero_eqn. 
  apply E0_eq_intro => //.
Qed. 

Lemma gF_mono_l alpha beta:
  E0_lt beta alpha -> dominates (F_ alpha) (F_ beta).
Proof.
  rewrite /dominates;
    specialize (F_mono_l (E0_g2h alpha) (E0_g2h beta)).
  move => H hbeta_alpha.
  have H' : E0_g2h beta o< E0_g2h alpha by rewrite gE0_lt_iff in hbeta_alpha.  
  case (H H') => x Hx; exists x;  rewrite /dominates_from /F_ => p Hp.
  apply /ltP; apply : Hx; by apply /leP. 
Qed.


Lemma gF_alpha_0_eq (alpha : E0): F_ alpha 0 = 1.
Proof. by  rewrite /F_ F_alpha_0_eq. Qed.


(*

F_restricted_mono_l:
  forall (alpha beta : hE0) (n : nat),
  Paths.Canon_plus n alpha beta -> (hF_ beta n <= hF_ alpha n)%coq_nat

H'_F:
  forall (alpha : hE0) (n : nat),
  (hF_ alpha n.+1 <= Hprime.H'_ (E0.phi0 alpha) n.+1)%coq_nat

F_succ_eqn:
  forall (alpha : hE0) (i : nat),
  hF_ (Succ alpha) i = Iterates.iterate (hF_ alpha) i.+1 i

LF2: forall i : nat, ((Exp2.exp2 i * i)%coq_nat < hF_ 2 i)%coq_nat
LF1: forall i : nat, hF_ 1 i = (2 * i)%coq_nat.+1
LF2_0:
  Iterates.dominates_from 0 (hF_ 2) (fun i : nat => (Exp2.exp2 i * i)%coq_nat)
F_lim_eqn:
  forall (alpha : hE0) (i : nat),
  Limitb alpha -> hF_ alpha i = hF_ (Canon.Canon alpha i) i

HF0:
  (fun alpha : hE0 =>
   forall n : nat, (hF_ alpha n.+1 <= Hprime.H'_ (E0.phi0 alpha) n.+1)%coq_nat)
    Zero

F_star_iterate:
  forall (alpha : hE0) (n i : nat),
  F_star (alpha, n) i = Iterates.iterate (hF_ alpha) n i
LF2': forall i : nat, (1 <= i)%coq_nat -> (Exp2.exp2 i < hF_ 2 i)%coq_nat


LF3_2:
  Iterates.dominates_from 2 (hF_ 3)
    (fun n : nat => Iterates.iterate Exp2.exp2 n.+1 n)

F_mono_l_0:
  forall alpha beta : hE0,
  beta o< alpha ->
  forall n : nat,
  Paths.Canon_plus n.+1 alpha beta ->
  forall i : nat, (n.+1 < i)%coq_nat -> (hF_ beta i < hF_ alpha i)%coq_nat

*)

(** Gaia-compatible [F_ alpha] fast growing functions  

(imported from [hydras.Epsilon0.F_alpha] )
*)


(* begin snippet Requirements:: no-out  *)
From mathcomp Require Import all_ssreflect zify.
From gaia Require Export ssete9.
From Coq Require Import Logic.Eqdep_dec.
From hydras Require Import DecPreOrder.
From hydras Require Import T1 E0.
From hydras Require Paths.
(* end snippet Requirements *)

From hydras Require Import primRec PrimRecExamples. 
From hydras Require Import  F_alpha F_omega. 

From gaia_hydras Require Import T1Bridge GCanon GHprime.

Set Implicit Arguments.
Unset Strict Implicit.

(** *  Rapidly growing functions *)

(* begin snippet FAlphaDef *)


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

(** Please note that a lemma [foo] may mask [F_alpha.Foo] *)

(* begin snippet FAlphaProps:: no-out *)
Lemma F_alpha_gt (alpha : E0) (n : nat): (n < F_ alpha n)%N.
Proof. apply /ltP; apply Epsilon0.F_alpha.F_alpha_gt. Qed.

Lemma F_alpha_mono (alpha: E0): strict_mono (F_ alpha).
Proof.
  rewrite /strict_mono /F_ => n p Hnp; apply /ltP.
  apply F_alpha_mono; move: Hnp => /ltP //.
Qed.

Lemma F_alpha_dom alpha:
  dominates_from 1 (F_ (E0succ alpha)) (F_ alpha).
Proof.
  rewrite /dominates_from /F_ g2h_E0succ => p Hp.
  apply /ltP; apply F_alpha_dom; by apply /leP.
Qed.

(* end snippet FAlphaProps *)

Lemma F_alpha_Succ_le alpha:
 fun_le (F_ alpha) (F_ (E0succ alpha)).
Proof.
  rewrite /fun_le /F_ g2h_E0succ => n;  apply /leP; apply F_alpha_Succ_le. 
Qed. 

Lemma F_alpha_positive (alpha : hE0) (n : nat): (0 < hF_ alpha n)%N.
Proof.
  rewrite /F_. apply /ltP ; apply Lt.le_lt_trans with n;
    [auto with arith| apply F_alpha.F_alpha_gt].
Qed.

Lemma F_zero_eqn i: F_ E0zero i = i .+1.
Proof.
  rewrite /F_; replace (E0_g2h E0zero) with E0.E0zero.
  -  by rewrite F_zero_eqn. 
  -  apply E0_eq_intro => //.
Qed. 

Lemma F_mono_l alpha beta:
  E0lt beta alpha -> dominates (F_ alpha) (F_ beta).
Proof.
  rewrite /dominates;  specialize (F_mono_l (E0_g2h alpha) (E0_g2h beta)); 
  move => H hbeta_alpha.
  have H' : E0_g2h beta o< E0_g2h alpha
    by move: hbeta_alpha; rewrite gE0lt_iff.  
  case (H H') => x Hx; exists x; rewrite /dominates_from /F_ => p Hp.
  apply /ltP; apply : Hx; by apply /leP. 
Qed.

Lemma F_alpha_0_eq (alpha : E0): F_ alpha 0 = 1.
Proof. by  rewrite /F_ F_alpha_0_eq. Qed.

Lemma F_succ_eqn alpha i :
  F_ (E0succ alpha) i = Iterates.iterate (F_ alpha) i.+1 i.
Proof.
  rewrite (Iterates.iterate_ext _  (hF_ (E0_g2h alpha))); last first.
  by rewrite /F_. 
  rewrite -F_succ_eqn /F_; f_equal;
    apply E0_eq_intro => /= ;  by rewrite g2h_succ. 
Qed.

Lemma F_lim_eqn alpha i:
  T1limit (cnf alpha) -> F_ alpha i = F_ (E0Canon alpha i) i.
Proof. 
 move => Hlimit; rewrite /F_ F_lim_eqn.
 -  f_equal; apply E0_eq_intro; cbn; by rewrite g2h_canon. 
 -  rewrite /hE0limit limitb_ref.
   move: alpha Hlimit ;case => /= x Hx H'x;  by rewrite h2g_g2hK. 
Qed.

(**  numerical examples *)

Lemma LF1 i: F_ (E0fin 1) i = ((2 * i) .+1)%N.
Proof. 
  replace (F_ (E0fin 1) i) with (hF_ (hE0fin 1) i). 
  - rewrite LF1 => //.
  - rewrite /F_; f_equal; by apply E0_eq_intro .
Qed.

Lemma LF2 i:  (Exp2.exp2 i * i < F_ (E0fin 2) i)%N.
Proof. 
  apply /ltP; replace (F_ (E0fin 2) i) with (hF_ (hE0fin 2) i). 
  - apply LF2. 
  - rewrite /F_; f_equal;  by apply E0_eq_intro .
Qed.

Lemma LF2' i:  (1 <= i)%N -> (Exp2.exp2 i < F_ (E0fin 2) i)%N.
Proof. 
  move => Hi; apply /ltP; replace (F_ (E0fin 2) i) with (hF_ (hE0fin 2) i). 
  - apply LF2'; by apply /leP. 
  - rewrite /F_; f_equal; by apply E0_eq_intro .
Qed. 

Lemma LF3_2:
  Iterates.dominates_from 2 (F_ (E0fin 3))
    (fun n : nat => Iterates.iterate Exp2.exp2 n.+1 n).
Proof.
  rewrite /dominates_from /F_. 
  replace (E0_g2h (E0fin 3)) with (hE0fin 3); last first. 
  - by apply E0_eq_intro.
  - apply LF3_2.   
Qed.

Definition Canon_plus n alpha beta :=
  Paths.Canon_plus n (E0_g2h alpha) (E0_g2h beta). 

Lemma F_restricted_mono_l alpha beta n:
    Canon_plus n alpha beta -> (F_ beta n <= F_ alpha n)%N.
Proof.
  rewrite /Canon_plus /F_. move => HCanon; apply /leP. 
  by apply F_restricted_mono_l.    
Qed. 

Lemma H'_F alpha n : (F_ alpha n.+1 <= H'_ (E0phi0 alpha) n.+1)%N.
Proof. 
 apply /leP; rewrite /F_ /H'_. 
 replace (E0_g2h (E0phi0 alpha)) with (hE0phi0 (E0_g2h alpha)). 
 - apply H'_F; apply E0_eq_intro; destruct alpha => /=.
 - apply E0_eq_intro; rewrite /E0phi0 => //.
Qed.

(* begin snippet FAlphaNotPR:: no-out *)
Lemma F_alpha_not_PR_E0  alpha:
  E0le E0omega alpha -> isPR 1 (F_ alpha) -> False. 
Proof. 
  move => Halpha HPR;  have H0: isPR 1 (hF_ (E0_g2h alpha)).
  eapply isPR_extEqual_trans with  (F_ alpha) => //.
  eapply F_alpha_not_PR with (E0_g2h alpha) => //.
  replace E0.E0omega with (E0_g2h E0omega); last first.
  - by apply E0_eq_intro. 
  - by rewrite -gE0le_iff. 
Qed.
(* end snippet FAlphaNotPR *)

Lemma F_alpha_not_PR alpha (Hnf: T1nf alpha == true):
  gLE T1omega alpha -> isPR 1 (@T1F_ alpha Hnf) -> False.
Proof. 
  rewrite /T1F_ => Halpha; 
  apply F_alpha_not_PR_E0; rewrite /E0le  => /=; by destruct Halpha. 
Qed. 


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
Set Program Cases.

(** *  Rapidly growing functions *)

Notation hF_ := F_alpha.F_.

(* begin snippet FAlphaDef *)
Definition F_ (alpha : E0)  := F_alpha.F_ (E0_g2h alpha).
(* end snippet FAlphaDef *)

#[program]
 Definition T1F_ (a : T1)(Hnf : T1nf a == true) (n:nat) : nat:=
  (F_ (@mkE0 a _) n).


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

Lemma F_alpha_positive (alpha : hE0) (n : nat): (0 < F_alpha.F_ alpha n)%N.
Proof.
  rewrite /F_. apply /ltP ; apply Lt.le_lt_trans with n;
    [auto with arith| apply F_alpha.F_alpha_gt].
Qed.

(* begin snippet FZeroEqn:: no-out *)
Lemma F_zeroE i: F_ E0zero i = i.+1.
(* end snippet FZeroEqn *)
Proof.
  rewrite /F_; replace (E0_g2h E0zero) with E0.E0zero.
  -  by rewrite F_zero_eqn. 
  -  apply E0_eq_intro => //.
Qed. 

Lemma F_mono_l alpha beta:
  E0lt beta alpha -> dominates (F_ alpha) (F_ beta).
Proof.
  rewrite /dominates;
    move: (F_mono_l (E0_g2h alpha) (E0_g2h beta))  => H hbeta_alpha.
  have H' : E0_g2h beta o< E0_g2h alpha
    by move: hbeta_alpha; rewrite gE0lt_iff.  
  case (H H') => x Hx; exists x; rewrite /dominates_from /F_ => p Hp.
  apply /ltP; apply : Hx; by apply /leP. 
Qed.

(* begin snippet FAlphaZeroEqn:: no-out *)
Lemma F_alpha_0_eq (alpha : E0): F_ alpha 0 = 1.
(* end snippet FAlphaZeroEqn *)
Proof. by  rewrite /F_ F_alpha_0_eq. Qed.

(* begin snippet FSuccEqn:: no-out *)
Lemma F_succE alpha i :
  F_ (E0succ alpha) i = Iterates.iterate (F_ alpha) i.+1 i.
(* end snippet FSuccEqn *)
Proof.
  rewrite (Iterates.iterate_ext _  (F_alpha.F_ (E0_g2h alpha))); last first.
  by rewrite /F_. 
  rewrite -F_succ_eqn /F_. congr hF_;
    apply E0_eq_intro => /= ;  by rewrite g2h_succ. 
Qed.

(* begin snippet FLimEqn:: no-out *)
Lemma F_limE alpha i:
  T1limit (cnf alpha) -> F_ alpha i = F_ (E0Canon alpha i) i.
(* end snippet FLimEqn *)
Proof. 
 move => Hlimit; rewrite /F_ F_lim_eqn.
 -  congr hF_; apply E0_eq_intro; cbn; by rewrite g2h_canon. 
 -  rewrite /hE0limit T1limit_ref.
   move: alpha Hlimit ;case => /= x Hx H'x;  by rewrite h2g_g2hK. 
Qed.

(**  numerical examples *)

Lemma LF1 i: F_ (E0fin 1) i = ((2 * i) .+1)%N.
Proof. 
  replace (F_ (E0fin 1) i) with (F_alpha.F_ (hE0fin 1) i). 
  - rewrite LF1 => //.
  - rewrite /F_; congr hF_; by apply E0_eq_intro .
Qed.

Lemma LF2 i:  (Exp2.exp2 i * i < F_ (E0fin 2) i)%N.
Proof. 
  apply /ltP; replace (F_ (E0fin 2) i) with (F_alpha.F_ (hE0fin 2) i). 
  - apply LF2. 
  - rewrite /F_; congr hF_ ; by apply E0_eq_intro .
Qed.

Lemma LF2' i:  (1 <= i)%N -> (Exp2.exp2 i < F_ (E0fin 2) i)%N.
Proof. 
  move => Hi; apply /ltP;
          replace (F_ (E0fin 2) i) with (F_alpha.F_ (hE0fin 2) i). 
  - apply LF2'; by apply /leP. 
  - rewrite /F_; congr hF_; by apply E0_eq_intro .
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


(* begin snippet HprimeF:: no-out *)
Lemma H'_F alpha n : (F_ alpha n.+1 <= H'_ (E0phi0 alpha) n.+1)%N.
(* end snippet HprimeF *)
Proof. 
 apply /leP; rewrite /F_ /H'_. 
 replace (E0_g2h (E0phi0 alpha)) with (hE0phi0 (E0_g2h alpha)). 
 - apply H'_F; apply E0_eq_intro; destruct alpha => /=.
 - apply E0_eq_intro; rewrite /E0phi0 => //.
Qed.

(* begin snippet FAlphaNotPR:: no-out *)
Lemma F_alpha_not_PR_E0  alpha:
  E0le E0omega alpha -> isPR 1 (F_ alpha) -> False. 
(* end snippet FAlphaNotPR *)
Proof. 
  move => Halpha HPR;  have H0: isPR 1 (F_alpha.F_ (E0_g2h alpha)).
  eapply isPR_extEqual_trans with  (F_ alpha) => //.
  eapply F_alpha_not_PR with (E0_g2h alpha) => //.
  replace E0.E0omega with (E0_g2h E0omega); last first.
  - by apply E0_eq_intro. 
  - by rewrite -gE0le_iff. 
Qed.


Lemma F_alpha_not_PR alpha (Hnf: T1nf alpha == true):
  LE T1omega alpha -> isPR 1 (@T1F_ alpha Hnf) -> False.
Proof. 
  rewrite /T1F_ => Halpha; 
  apply F_alpha_not_PR_E0; rewrite /E0le  => /=; by destruct Halpha. 
Qed. 


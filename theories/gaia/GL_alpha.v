
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
From gaia_hydras Require Import T1Bridge GCanon GPaths GHprime.
(* end snippet Requirements *)

Set Implicit Arguments.
Unset Strict Implicit.

Definition L_ (alpha:E0) (i:nat): nat :=
 L_alpha.L_  (E0_g2h alpha) i. 

Lemma L_zero_eqn i :  L_ E0zero i = i.
Proof. by rewrite /L_. Qed.

Lemma L_eq2 alpha i :
  E0is_succ alpha -> L_ alpha i = L_ (E0pred alpha) (S i).
Proof.
  move => H;  case (E0is_succE H) => x Hx; subst.
  rewrite E0pred_succK /L_ L_alpha.L_eq2 => //. 
  f_equal; rewrite g2h_E0succ; by rewrite E0pred_of_Succ. 
Qed. 

Lemma L_succ_eqn alpha i :
  L_ (E0succ alpha) i = L_ alpha i.+1.
Proof. 
  rewrite L_eq2 ?E0pred_succK => //; apply E0is_succ_succ.
Qed.


Lemma L_lim_eqn alpha i :
  E0limit alpha ->
  L_ alpha i = L_ (E0Canon alpha i) (S i).
Proof.
  move => Halpha; rewrite /E0limit /L_  L_alpha.L_lim_eqn /E0Canon; f_equal.
  - apply E0_eq_intro; cbn; by rewrite g2h_canon.
  - move: Halpha ; by rewrite /E0limit.
Qed.

Lemma L_finite : forall i k :nat,  L_ (E0fin  i) k = (i+k)%nat.
Proof.  move => i k. by rewrite /L_ E0g2h_Fin L_alpha.L_finite. Qed.

Lemma L_omega : forall k, L_ E0omega k = S (2 * k)%nat.
Proof.  move => k; by rewrite /L_ E0g2h_omegaE L_alpha.L_omega. Qed.


Lemma L_ge_id alpha : forall i,  (i <= L_ alpha i)%N.
Proof. move => i; rewrite /L_. apply /leP ; apply L_alpha.L_ge_id. Qed.

Lemma L_ge_S alpha i:
  alpha <> E0zero -> (i <  L_ alpha i)%N.
Proof.
  move =>  Halpha. rewrite /L_; apply /ltP. apply L_alpha.L_ge_S.
  move => H; apply Halpha, E0_eqE => //.
  rewrite H;  by apply E0_eq_intro.
Qed. 

Definition L_spec (alpha:T1) (f: nat -> nat):=
  Large_Sets.L_spec (g2h alpha) f.

Lemma L_spec0 (f:nat -> nat) : L_spec zero f <-> forall k, f k.+1 = k.+1.
Proof.
 rewrite /L_spec; split => H.
 move => k; inversion H => //.
 by left. 
Qed.


Lemma L_spec1 (alpha:T1) (f:nat -> nat) :
  alpha != zero ->
  L_spec alpha f <->
    (forall k,
        Large_Sets.mlarge (g2h alpha)
                          ( MoreLists.interval (S k)
                                               (Nat.pred (f (S k))))) .
Proof. 
  move => Halpha. 
  have Hdiff : alpha <> zero.  move => H0; subst. by cbn in Halpha. 
  rewrite /L_spec; split => H.
  inversion H as [f0 H0 H1 H2| alpha0 f0 H0 H1 H2 H3].
  {  suff Hzero: alpha = zero by contradiction. 
  apply g2h_eqE.  by rewrite -H1.    }
  move => k;  move: (H1 k).
  rewrite interval_def => //.
  right;  move => Hzero //.
  apply Hdiff; apply g2h_eqE; by rewrite Hzero. 
Qed. 

Lemma L_pos_inv alpha f :
 alpha != zero -> L_spec alpha f ->
                        forall k, (S k < f (S k))%N.
Proof.
  move => Halpha H k.
   have Hdiff : alpha <> zero.  move => H0; subst. by cbn in Halpha. 
   apply /ltP; apply Large_Sets.L_pos_inv with (g2h alpha) => //. 
   move => H0; apply Hdiff,g2h_eqE, H0. 
Qed.


Theorem L_correct alpha : L_spec (cnf alpha) (L_ alpha).
Proof.  apply (L_alpha.L_correct (E0_g2h alpha)). Qed. 

(* begin snippet HprimeLAlpha:: no-out *)
Theorem H'_L_ alpha i: (H'_ alpha i <= L_ alpha i.+1)%N.
Proof.  rewrite /L_ /H'_; apply /leP; by apply L_alpha.H'_L_.  Qed.
(* end snippet HprimeLAlpha *)


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
From hydras Require Import  L_alpha.
From gaia_hydras Require Import T1Bridge GCanon GPaths GHprime.
(* end snippet Requirements *)

Set Implicit Arguments.
Unset Strict Implicit.

(* begin snippet Ldef:: no-out *)
Definition L_ (alpha:E0) (i:nat): nat :=
 L_alpha.L_ (E0_g2h alpha) i. 

Lemma L_zeroE i :  L_ E0zero i = i.
Proof. by rewrite /L_. Qed.
(* end snippet Ldef *)

(* begin snippet Leq2:: no-out *)
Lemma L_eq2 alpha i :
  E0is_succ alpha -> L_ alpha i = L_ (E0_pred alpha) (S i).
(* end snippet Leq2 *)
Proof.
  move => H;  case (E0is_succE H) => x Hx; subst.
  rewrite E0_pred_succK /L_ L_alpha.L_eq2 => //. 
  congr L_alpha.L_; rewrite g2h_E0_succ; by rewrite E0_pred_of_Succ. 
Qed. 

(* begin snippet Leq3:: no-out *)
Lemma L_succE alpha i : L_ (E0_succ alpha) i = L_ alpha i.+1.
(* end snippet Leq3 *)
Proof. 
  rewrite L_eq2 ?E0_pred_succK => //; apply E0is_succ_succ.
Qed.

(* begin snippet Leq4:: no-out *)
Lemma L_limE alpha i :
  E0limit alpha ->  L_ alpha i = L_ (E0Canon alpha i) (S i).
(* end snippet Leq4 *)
Proof.
  move => Halpha; rewrite /E0limit /L_  L_alpha.L_lim_eqn /E0Canon.
  - congr L_alpha.L_;  apply E0_eq_intro; cbn; by rewrite g2h_canon.
  - move: Halpha ; by rewrite /E0limit.
Qed.

Lemma L_finite : forall i k :nat, L_ (E0fin  i) k = (i+k)%nat.
Proof.  move => i k. by rewrite /L_ E0g2h_Fin L_alpha.L_finite. Qed.

Lemma L_omega : forall k, L_ E0_omega k = S (2 * k)%nat.
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


Lemma L_spec1 (a:T1) (f:nat -> nat) :
  a != zero ->
  L_spec a f <->
    (forall k,
        Large_Sets.mlarge (g2h a)
                          ( MoreLists.interval (S k)
                                               (Nat.pred (f (S k))))) .
Proof. 
  move => Ha. 
  have Hdiff : a <> zero.  move => H0; subst. by cbn in Ha. 
  rewrite /L_spec; split => H.
  inversion H as [f0 H0 H1 H2| a0 f0 H0 H1 H2 H3].
  {  suff Hzero: a = zero by contradiction. 
  apply g2h_eqE.  by rewrite -H1.    }
  move => k;  move: (H1 k).
  rewrite interval_def => //.
  right;  move => Hzero //.
  apply Hdiff; apply g2h_eqE; by rewrite Hzero. 
Qed. 

Lemma L_pos_inv a f :
 a != zero -> L_spec a f ->
                        forall k, (S k < f (S k))%N.
Proof.
  move => Ha H k.
   have Hdiff : a <> zero.  move => H0; subst. by cbn in Ha. 
   apply /ltP; apply Large_Sets.L_pos_inv with (g2h a) => //. 
   move => H0; apply Hdiff,g2h_eqE, H0. 
Qed.

Theorem L_correct a : L_spec (cnf a) (L_ a).
Proof.  apply (L_alpha.L_correct (E0_g2h a)). Qed. 

(* begin snippet HprimeLAlpha:: no-out *)
Theorem H'_L_ a i: (H'_ a i <= L_ a i.+1)%N.
Proof.  rewrite /L_ /H'_; apply /leP; by apply L_alpha.H'_L_.  Qed.
(* end snippet HprimeLAlpha *)

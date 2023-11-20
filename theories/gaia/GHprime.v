
(** Gaia-compatible [H'_ alpha] fast growing functions  

(imported from [hydras.Epsilon0.Hprime] )
*)


(* begin snippet Requirements:: no-out  *)
From mathcomp Require Import all_ssreflect zify.
From gaia Require Export ssete9.
From Coq Require Import Logic.Eqdep_dec.
From hydras Require Import DecPreOrder T1 E0.
From hydras Require Paths.
From hydras Require Import  Iterates Hprime L_alpha.
From gaia_hydras Require Import T1Bridge GCanon GPaths.
(* end snippet Requirements *)

Set Implicit Arguments.
Unset Strict Implicit.

(* begin snippet HprimeDef *)
Definition H'_ alpha i := Hprime.H'_ (E0_g2h alpha) i.
(* end snippet HprimeDef *)



(** ** Equations for [H'_] *)

(* begin snippet HprimeEquations:: no-out *)
Lemma H'_eq1 (i: nat) : H'_ E0zero i = i. 
Proof. by rewrite /H'_  g2h_E0zero Epsilon0.Hprime.H'_eq1.  Qed.

Lemma H'_eq2  alpha i :
  H'_ (E0_succ alpha) i = H'_ alpha (S i).
Proof.
  case alpha => ? ?; by rewrite /H'_  g2h_E0_succ H'_eq2.   
Qed.

Lemma H'_eq3 alpha i :
  E0limit alpha ->  H'_ alpha i =  H'_ (E0Canon alpha (S i)) i.
(* ... *)
(* end snippet HprimeEquations *)
Proof. 
  rewrite /E0limit /H'_ => H; rewrite H'_eq3 => //; congr Hprime.H'_.    apply E0_eq_intro => /=;  by rewrite g2h_canon.
Qed.

(** **  Examples *)

(* begin snippet Examples:: no-out *)
Lemma H'_omega k : H'_ E0_omega k = (2 * k).+1 %nat.
Proof. 
  rewrite H'_eq3  ?/E0limit => //.
  (* ... *)
(* end snippet Examples *)
  replace (E0Canon E0_omega k.+1) with (E0fin k.+1); last first.
  apply gE0_eq_intro => /=;  by rewrite E0fin_cnf T1succ_nat. 
  rewrite /H'_ E0g2h_Fin H'_Fin; lia.
Qed. 

(* begin snippet Examplesb:: no-out *)
Lemma H'_omega_double (k: nat) :
  H'_ (E0mul E0_omega (E0fin 2)) k =  (4 * k + 3)%coq_nat.
Proof.
  by rewrite /H'_  -H'_omega_double E0g2h_mulE E0g2h_omegaE E0g2h_Fin. 
Qed.
(* end snippet Examplesb *)

(** TODO
    import more abstract properties of H'_ *)

(* begin snippet abstract:: no-out  *)
Lemma H'_dom alpha beta :
  E0lt alpha beta -> dominates_strong (H'_ beta) (H'_ alpha).
(* end snippet abstract  *)
Proof.
  move => H; have H' : (hE0lt (E0_g2h alpha) (E0_g2h beta)) 
  by rewrite -gE0lt_iff.
  case (Epsilon0.Hprime.H'_dom _ _ H') => x Hx; exists x; rewrite  /H'_.
  move => p Hp; apply /ltP; apply Hx;  by apply /leP.
Qed.

(* begin snippet abstractb:: no-out  *)
Lemma H'_alpha_mono (alpha : E0) : strict_mono (H'_ alpha).
Proof.
  generalize (Hprime.H'_alpha_mono (E0_g2h alpha)) => H x y /ltP.
  move /H;  by rewrite /H'_ => /ltP. 
Qed.
(* end snippet abstractb  *)

(* begin snippet abstractc:: no-out  *)
Theorem H'_alpha_gt alpha (Halpha: alpha <> E0zero) n :
  (n < H'_ alpha n)%N.
Proof.
  move: (H'_alpha_gt (E0_g2h alpha)) => H.
  rewrite /H'_ ; apply /ltP; apply H => H0; apply Halpha.  
  apply gE0_eq_intro; case: alpha H H0 Halpha => // ? ? ? H0 ?. 
  injection H0 => Heq; by rewrite -g2h_eqE ?Heq. 
Qed.

Lemma H'_omega_cube_min :
forall k : nat,
  0 <> k -> (hyper_exp2 k.+1  <= H'_ (E0_phi0 (E0fin 3)) k)%N.
Proof.
  move => k Hk; apply /leP; transitivity (Hprime.H'_ (hE0phi0 3) k). 
  - by apply H'_omega_cube_min.
  - by rewrite /H'_  E0g2h_phi0 E0g2h_Fin. 
Qed. 
(* end snippet abstractc  *)

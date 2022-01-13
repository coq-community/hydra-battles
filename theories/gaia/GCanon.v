From hydras Require Import T1.
From mathcomp Require Import all_ssreflect zify.
Require Import T1Bridge.
Import ssete9.CantorOrdinal. 

From gaia Require Import ssete9.
Import ssete9.CantorOrdinal. 
Set Bullet Behavior "Strict Subproofs".

From hydras Require Import Canon.

#[global] Notation hcanon := canon. 

Definition gcanon (a: gT1) (i:nat) : gT1 :=
  iota (hcanon (pi a) i).

Compute gcanon (g_phi0 T1omega) 6 == (g_phi0 (\F 6))%brg.

Lemma gcanon_zero i:  gcanon g_zero i = g_zero. 
Proof.  unfold gcanon => //. Qed. 

Lemma nf_gcanon alpha i : g_nfb alpha -> g_nfb (gcanon alpha i).
Proof.  
 unfold gcanon; rewrite -nf_ref => Halpha; rewrite -(iota_pi alpha)in Halpha.
 rewrite -nf_ref in Halpha; by  apply nf_canon. 
Qed.

Search hcanon.

Lemma gcanon_succ i alpha: g_nfb alpha -> gcanon (g_succ alpha) i = alpha.
Proof.
  rewrite -(iota_pi alpha). rewrite succ_ref. rewrite -nf_ref.
  unfold gcanon. rewrite pi_iota. Search hcanon h_succ.
  move => Halpha; rewrite canon_succ => //.
Qed.


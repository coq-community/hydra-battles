From mathcomp Require Import all_ssreflect zify.

From Coq Require Import Logic.Eqdep_dec.
From hydras Require Import DecPreOrder ON_Generic.
From hydras Require Import T1 E0 Hessenberg Hydra_Theorems Hydra_Termination.
From gaia Require Export ssete9.
Set Bullet Behavior "Strict Subproofs".

Require Import T1Bridge. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma mVariant: Hvariant  nf_Wf free (fun h =>  h2g (m h)).
Proof. 
  split; move => i h h' Hnot_head step; rewrite /restrict; split. 
  1,3 : rewrite -nf_ref; apply m_nf.
  rewrite -hlt_iff; by apply round_decr.
Qed.



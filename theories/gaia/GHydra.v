From mathcomp Require Import all_ssreflect zify.

From Coq Require Import Logic.Eqdep_dec.
From hydras Require Import DecPreOrder ON_Generic.
From hydras Require Import T1 E0 Hessenberg Hydra_Theorems Hydra_Termination.
From gaia Require Export ssete9.
Set Bullet Behavior "Strict Subproofs".

Require Import T1Bridge GHessenberg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint m (h:Hydra) : T1 :=
  match h with
  | head => zero
  | node (Hydra_Definitions.hcons _ _ as hs) => ms hs
  end
    with ms (s : Hydrae) : T1 :=
  match s with
  | hnil => zero
  | Hydra_Definitions.hcons h s' => phi0 (m h) o+ ms s'
  end.

Lemma m_ref h : g2h (m h) = (Hydra_Termination.m h).
Proof.
  induction h using   Hydra_rect2 with
    (P0 :=
       (fun hs =>  g2h (ms hs) =  Hydra_Termination.ms hs)) => //.
  -  case: h IHh => [/= // |] => h hs H => //.
  - rewrite /ms -!/m -!/ms /oplus g2h_phi0 IHh IHh0 g2h_h2gK => //.
Qed.

Lemma m_nf h : T1nf (m h). 
Proof. 
  rewrite -hnf_g2h m_ref; apply  Hydra_Termination.m_nf.
Qed. 
  
Lemma mVariant: Hvariant  nf_Wf free m .
Proof. 
  split; move => i h h' Hnot_head step; rewrite /restrict; split. 
  1,3 : apply m_nf.
  rewrite -(h2g_g2hK (m h)) -(h2g_g2hK (m h')).
   apply lt_ref; rewrite !m_ref; by apply round_decr. 
Qed.



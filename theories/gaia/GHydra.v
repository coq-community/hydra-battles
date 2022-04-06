From mathcomp Require Import all_ssreflect zify.

From Coq Require Import Logic.Eqdep_dec.
From hydras Require Import DecPreOrder ON_Generic.
From hydras Require Import T1 E0 Hessenberg Hydra_Theorems Hydra_Definitions
     Hydra_Termination.
From gaia Require Export ssete9.

Require Import T1Bridge GHessenberg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Hydra_Definitions. 

(* begin snippet mDef *)
Fixpoint m (h:Hydra) : T1 :=
  if h is  node (hcons _ _ as hs) then ms hs else zero
with ms (s : Hydrae) : T1 :=
  if s is hcons h s' then phi0 (m h) o+ ms s' else zero.
(* end snippet mDef *)

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

(* begin snippet mVariant:: no-out *)
Lemma mVariant: Hvariant  nf_Wf free m .
(* end snippet mVariant *)
Proof. 
  split; move => i h h' Hnot_head step; rewrite /restrict; split. 
  1,3 : apply m_nf.
  rewrite -(h2g_g2hK (m h)) -(h2g_g2hK (m h')).
   apply lt_ref; rewrite !m_ref; by apply round_decr. 
Qed.

(* begin snippet Termination:: no-out *)
Theorem every_battle_terminates : Termination.
(* end snippet Termination *)
Proof. 
  red; apply Inclusion.wf_incl with (R2 := fun h h' =>  LT (m h) (m h')).
  - case mVariant => Hvar; rewrite /inclusion => x y Hstep.
    case: Hstep => x0 Hstep;  apply (Hvar x0 y x).
    move => Hhead; subst; apply (head_no_round_n _ _ Hstep).
    by  [exists x0]. 
  - apply Inverse_Image.wf_inverse_image, nf_Wf. 
Qed.
(*||*)

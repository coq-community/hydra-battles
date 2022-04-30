From mathcomp Require Import all_ssreflect zify.

From Coq Require Import Logic.Eqdep_dec.
From hydras Require Import DecPreOrder ON_Generic.
From hydras Require Import T1 E0 Hessenberg Hydra_Theorems Hydra_Definitions
     Hydra_Termination Battle_length Hydra_Examples
     Epsilon0_Needed_Free  Epsilon0_Needed_Std.
From gaia Require Export ssete9.
Require Import T1Bridge GHessenberg GL_alpha GPrelude.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Hydra_Definitions. 

(* begin snippet mDef *)
Fixpoint m (h:Hydra) : T1 :=
  if h is  node (hcons _ _ as hs) then ms hs else zero
with ms (s : Hydrae) : T1 :=
  if s is hcons h s' then phi0 (m h) o+ ms s' else zero.

Compute T1pp (m Examples.Hy).
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
  red; apply Inclusion.wf_incl with
    (R2 := fun h h' =>  LT (m h) (m h')).
  - case mVariant => Hvar; rewrite /inclusion => x y Hstep.
    case: Hstep => x0 Hstep;  apply (Hvar x0 y x).
    move => Hhead; subst; apply (head_no_round_n _ _ Hstep).
    by  [exists x0]. 
  - apply Inverse_Image.wf_inverse_image, nf_Wf. 
Qed.
(*||*)

(* begin snippet lDef *)
Definition l_std alpha k := (L_ alpha (S k) - k)%nat.
(* end snippet lDef *)

Lemma l_stdE alpha k : l_std alpha k = Battle_length.l_std (E0_g2h alpha) k. 
Proof. reflexivity.  Qed.


(* begin snippet lStdOk:: no-out *)
Definition T1toH (a: T1) : Hydra := O2H.iota (g2h a).

Lemma l_std_ok : forall alpha : E0,
    alpha != E0zero ->
    forall k : nat,
      (1 <= k)%N -> battle_length standard k (T1toH (cnf alpha))
                                  (l_std alpha k).
(* end snippet lStdOk *)
Proof.
  move => alpha Halpha k /leP Hk; rewrite  /l_std.
  have H0: E0_g2h alpha <> hE0zero
    by rewrite -g2h_E0zero; apply /E0_diffE; apply /diffP.
  move:  (Battle_length.l_std_ok (E0_g2h alpha) H0 k Hk);
  rewrite /L_ => He; by apply He.
Qed.

Section ImpossibilityProof.
  Context (b: Battle). 
  Variable mu:T1.
  Hypothesis nfMu: T1nf mu.
  Variable m : Hydra -> T1.
  Let mh (h:Hydra) := g2h (m h).

  Context  (Var : Hvariant nf_Wf b m)
           (BVar:  BoundedVariant Var mu).

  #[local] Instance hVar : Hvariant T1_wf b mh.
  Proof.
    split => i h h' Hh Hrel; rewrite /mh.
    case :Var => Hvar; move:  (Hvar i h h' Hh Hrel) .
    case => ? ? ?; by rewrite -T1lt_iff. 
  Qed.

  #[local] Instance bVar : BoundedVariant hVar (g2h mu).
  Proof. 
  split. 
  case: BVar => Hb h; case: (Hb h) => Hnf Hm Hnf'; repeat split.
  1,3:  rewrite /mh; by rewrite hnf_g2h.
  rewrite /mh; by rewrite hlt_iff !h2g_g2hK.
  Qed.

  End ImpossibilityProof.

(* begin snippet impossibilityThms:: no-out *)

Lemma Impossibility_free mu m (Var: Hvariant nf_Wf free m):
  ~ BoundedVariant Var mu.
Proof. 
  move => bvar; refine (Impossibility_free _ _ _ (bVar  bvar)). 
Qed.

Lemma Impossibility_std mu  m (Var: Hvariant nf_Wf standard m):
  ~ BoundedVariant Var mu.
Proof. 
  move => bvar; refine (Impossibility_std _ _ _ (bVar  bvar)).
Qed.
(* end snippet impossibilityThms *)



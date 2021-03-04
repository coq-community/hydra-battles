From hydras Require Import OrdinalNotations.ON_Generic.
From Coq Require Import Relations.

Section Proofs_of_unicity.
  
Context (A:Type)
        (lt : relation A)
        (compare : A -> A -> comparison)
        (On : ON lt compare).

Section Proofs.
  Variables alpha beta : A.
  
  (** beta is a successor of alpha *)
  
  Hypothesis Halphabeta : Successor beta alpha.

  Section S1.
  Variable gamma: A.  
  Hypothesis Halphagamma :   Successor gamma alpha.

  Lemma L1 :  gamma = beta.
  Proof.
    destruct (lt_eq_lt_dec gamma beta) as [[Hlt | Heq] | Hgt];
      [ exfalso|trivial|exfalso]; destruct Halphabeta as [H0 H1];
        destruct  Halphagamma as [H2 H3]; eauto.
  Qed.

  End S1.

  Section S2.
    Variable gamma: A.
    Hypothesis Hgammaalpha : Successor beta gamma.

    Lemma L2 : gamma = alpha.
    Proof.
      destruct (lt_eq_lt_dec gamma alpha) as [[Hlt | Heq] | Hgt];
        [ exfalso|trivial|exfalso]; destruct Halphabeta as [H0 H1];
        destruct  Hgammaalpha as [H2 H3]; eauto.
    Qed.

  End S2.


End Proofs.

(** Please remind that [Successor beta alpha] must be read as
    "[beta] is a successor of [alpha]" *)


Lemma Successor_unicity (alpha beta gamma : A):
  Successor beta alpha ->
  Successor gamma alpha ->
  gamma = beta.
Proof.
  intros H H0.  apply (L1 _ _ H _ H0).
Qed.

Lemma Predecessor_unicity (alpha beta gamma : A):
  Successor beta alpha ->
  Successor beta gamma ->
  gamma = alpha.
Proof.
  intros H H0.  apply (L2 _ _ H _ H0).
Qed.

End Proofs_of_unicity.



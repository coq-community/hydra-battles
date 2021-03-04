From hydras Require Import OrdinalNotations.ON_Generic.
From Coq Require Import Relations.

Section Proofs_of_lt_succ_le.
  
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
  Hypothesis HGammaBeta :   lt gamma beta.

  Lemma L1 :   ON_le gamma alpha.
  Proof.
    destruct (lt_eq_lt_dec gamma alpha) as [[Hlt | Heq] | Hgt].
    - now left.
    - subst. right.
    - destruct Halphabeta.
      exfalso. eauto. 
  Qed.

  End S1.

End Proofs.

End Proofs_of_lt_succ_le.




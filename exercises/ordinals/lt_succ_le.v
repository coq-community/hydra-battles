From hydras Require Import OrdinalNotations.ON_Generic.
From Coq Require Import Relations.

Open Scope ON_scope.

Section Proofs_of_lt_succ_le.
  
  Context (A:Type)
          (lt : relation A)
          (compare : A -> A -> comparison)
          (On : ON lt compare).

  Section Proofs.
    Variables alpha beta : A.
    
    (** beta is a successor of alpha *)
    
    Hypothesis Halphabeta : Successor beta alpha.

    
    Lemma lt_succ_le : forall gamma, gamma o< beta -> gamma o<= alpha.
    Admitted.

  End Proofs.

End Proofs_of_lt_succ_le.




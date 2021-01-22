From hydras Require Import OrdinalNotations.ON_Generic.
From Coq Require Import Relations.


(** Prove that, in any ordinal notation, every ordinal has 
     at most one predecessor and one successor *)

Section Proofs_of_unicity.
  
Context (A:Type)
        (lt : relation A)
        (compare : A -> A -> comparison)
        (On : ON lt compare).

(** Please remind that [Successor alpha beta] must be read as
    "[beta] is a successor of [alpha]" *)


Lemma Successor_unicity (alpha beta gamma : A):
  Successor alpha beta ->
  Successor alpha gamma ->
  gamma = beta.
Admitted.

Lemma Predecessor_unicity (alpha beta gamma : A):
  Successor alpha beta ->
  Successor gamma beta ->
  gamma = alpha.
Admitted.

End Proofs_of_unicity.



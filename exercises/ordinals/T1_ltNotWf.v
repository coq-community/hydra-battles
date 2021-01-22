(** The order [lt] on [T] is not well-founded *)

From hydras Require Import T1.
From Coq Require Import Relations.



(** Prove the following theorem : *)

Theorem not_decreasing (A:Type)(R: relation A) (Hwf : well_founded R) :
  ~ (exists seq : nat -> A, (forall i:nat, R (seq (S i)) (seq i))).
Admitted.


Section Proof_of_lt_not_wf.

  Hypothesis lt_wf : well_founded lt.

  (** Please consider the following sequence of terms 
     (most of them are not in Cantor normal form) *)
  
  Fixpoint  s (i:nat) : T1 :=
    match i with
      0 => phi0 2
    | S j => ocons 1 0 (s j)
    end.

  Lemma contrad : False.
  Admitted. 

End Proof_of_lt_not_wf.

Lemma lt_not_wf : ~ well_founded lt.
Admitted.

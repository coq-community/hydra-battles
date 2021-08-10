(** Comparison between Hydra-battle's and Gaia's [T1]  *)




From hydras Require  T1.
From gaia Require Import ssete9.


Fixpoint to_gaia (alpha : T1.T1) : CantorOrdinal.T1 :=
  match alpha with
    T1.zero => zero
  | T1.ocons alpha n beta => cons (to_gaia alpha) n (to_gaia beta)
  end.

Fixpoint from_gaia (alpha : CantorOrdinal.T1) : T1.T1 :=
  match alpha with
    zero => T1.zero
  | cons alpha n beta => T1.ocons (from_gaia alpha) n (from_gaia beta)
  end.


Lemma to_from alpha:  to_gaia (from_gaia alpha) = alpha.
Proof.
  induction alpha.
  - trivial.
  - cbn; now rewrite IHalpha1, IHalpha2. 
Qed.

Lemma from_to alpha:  from_gaia (to_gaia alpha) = alpha.
Proof.
  induction alpha.
  - trivial.
  - cbn; now rewrite IHalpha1, IHalpha2. 
Qed.




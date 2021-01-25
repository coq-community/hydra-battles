From hydras Require Import T1 E0.
From Coq Require Import Lia.

Open Scope E0_scope.

(** Prove the following lemma *)

Lemma ge_omega_iff (alpha : E0):
  omega o<= alpha <-> (forall i:nat, i + alpha = alpha).
Admitted.


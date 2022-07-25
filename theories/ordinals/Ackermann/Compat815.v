(** provisionally fixes some compatibilty issues 8.15 -> 8.16 *)

Require Import Arith.
Import Nat.

Module Compat815.

   (* --> Nat.lt_0_r *)
  Lemma le_n_0_eq : forall n : nat, n <= 0 -> 0 = n.
  Proof. intros n Hn;  symmetry; now rewrite <- Nat.le_0_r. Qed.

  (* --> Nat.lt_eq_cases *)
  Lemma le_lt_or_eq :
    forall n m : nat, n <= m -> n < m \/ n = m.
  Proof. intros n m; now rewrite Nat.lt_eq_cases. Qed.

End Compat815.


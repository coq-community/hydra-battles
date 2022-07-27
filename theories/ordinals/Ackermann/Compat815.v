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

  (* --> Nat.lt_succ_r *)
  Lemma lt_n_Sm_le:
      forall n m : nat, n < S m -> n <= m.
  Proof. intros n m; now rewrite Nat.lt_succ_r. Qed.

  Definition ind_0_1_SS (P : nat -> Prop) (H0 : P 0) (H1 : P 1)
  (H2 : forall n : nat, P n -> P (S (S n))) : forall n, P n :=

fix ind_0_1_SS (n : nat) : P n :=
  match n as n0 return (P n0) with
  | 0 => H0
  | S n0 =>
      (fun n1 : nat =>
       match n1 as n2 return (P (S n2)) with
       | 0 => H1
       | S n2 => (fun n3 : nat => H2 n3 (ind_0_1_SS n3)) n2
       end) n0
  end. 

End Compat815.


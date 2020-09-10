Require Import ON_plus ON_Finite ON_Omega.
Import Generic.
Require Import Compare_dec.


Definition O3O :=  ON_plus (FinOrd 3) Omega.


Arguments on_t : clear implicits.
Arguments on_t {A lt compare} _.

Definition inj1 (x: on_t (FinOrd 3)): nat.
  destruct x.
  exact x.
Defined.

Goal forall (z : on_t (FinOrd 3)),  PeanoNat.Nat.ltb (inj1 z) 3.
  unfold inj1; intros.
  destruct z.
  auto.
Qed.

Definition inj2 (z: on_t O3O) : on_t Omega.
destruct z.
- destruct t.
  exact x.
- exact (3 + n).
Defined.

Program Definition inj2' (z: on_t O3O) : on_t Omega :=
  match z with inl i => i | inr j => 3+j end.

Compute inj2' (inr 2).
Program Definition o2 : on_t (FinOrd 3) := 2.

Compute (inj2' (inl o2)).



Program Definition inj3 (a : on_t Omega) : on_t O3O :=
  match (le_lt_dec 3 a) with
    left _ => inr (a - 3)
  | right _ => inl a
  end.
Next Obligation.
now apply Ltb_ij.
Defined.

Compute inj3 42.
Compute inj3 2.
Compute match inj3 2 with inl x => proj1_sig x | inr z => z end.



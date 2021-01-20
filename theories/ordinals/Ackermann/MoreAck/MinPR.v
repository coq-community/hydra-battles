Require Import Min primRec extEqualNat.

Definition minPR (a b: nat) : nat :=
  (charFunction 2 leBool a b) * a +
  (charFunction 2 ltBool b a) * b.

Compute minPR 5 9.
Compute minPR 9 5.


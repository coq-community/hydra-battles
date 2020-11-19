Module Alt.

  Definition double (n:nat) := 2 * n.

End Alt.

Require Import Arith Lia.

Require Import Even.

Lemma alt_double_ok n : Nat.double n = Alt.double n.
Proof.
  unfold Alt.double, Nat.double.
  lia.
Qed.




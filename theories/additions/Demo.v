Module Alt.

  Definition double (n:nat) := 2 * n.

End Alt.

From Coq Require Import Arith Lia Even.

Lemma alt_double_ok n : Nat.double n = Alt.double n.
Proof.
  unfold Alt.double, Nat.double.
  lia.
Qed.




From Coq Require Import Arith.

Fixpoint exp2 (n:nat) : nat :=
  match n with
    0 => 1
  | S i => 2 * exp2 i
  end.

Lemma exp2_positive : forall i, 0 < exp2 i.
Proof.
   induction i; simpl; auto with arith. 
Qed.


Lemma exp2_not_zero i : exp2 i <> 0.
Proof.
  specialize (exp2_positive i); intros H H0.
   rewrite H0 in H; apply (Nat.nlt_0_r _ H).
Qed.

  

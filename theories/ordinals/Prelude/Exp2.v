From Coq Require Import Arith Lia.

(* begin snippet exp2Def *)
Fixpoint exp2 (n:nat) : nat :=
  match n with
    0 => 1
  | S i => 2 * exp2 i
  end.
(* end snippet exp2Def *)


Lemma exp2_positive : forall i, 0 < exp2 i.
Proof.
   induction i; simpl; auto with arith. 
Qed.


Lemma exp2_not_zero i : exp2 i <> 0.
Proof.
  specialize (exp2_positive i); intros H H0.
   rewrite H0 in H; apply (Nat.nlt_0_r _ H).
Qed.


Lemma exp2_gt_id : forall n, n < exp2 n.
Proof.
  induction n.
  - cbn; auto with arith.
  - cbn; generalize IHn; generalize (exp2 n); intros; lia.
Qed.


Lemma exp2S : forall n, exp2 (S n) = 2 * exp2 n.
Proof.
  unfold exp2;  intros; simpl; ring. 
Qed. 


 

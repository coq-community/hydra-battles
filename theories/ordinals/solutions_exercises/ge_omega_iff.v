From hydras Require Import T1 E0.
From Coq Require Import Lia.

Open Scope E0_scope.

Lemma ge_omega_iff (alpha : E0):
  omega o<= alpha <-> (forall i:nat, i + alpha = alpha).
Proof.
  destruct alpha as [a Ha]; unfold Le; cbn.
  destruct a; cbn; split; intros H.
  - unfold le; cbn. destruct H as (H, (Hle, Hnf)).
    now apply le_zero_inv in Hle.
  - specialize (H 1); compute in H; now injection H.
  - intros i.
    apply E0_eq_intro.
    destruct i; auto.
    destruct a1; auto.
    now destruct H as [_ ([Heq | Hlt], _)].
  - destruct a1.
    + specialize (H 1); cbn in H.
      assert (a2 = zero) by (eapply nf_of_finite; eauto).
      subst; compute in H; inversion H; lia.
    + repeat split; auto with T1.
      apply le_trans with (phi0 (ocons a1_1 n0 a1_2)).
      2: apply le_phi0. 
      apply phi0_mono, le_trans with (ocons a1_1 0 zero).
      * apply phi0_mono; auto with T1.
      * apply le_phi0.
Qed.


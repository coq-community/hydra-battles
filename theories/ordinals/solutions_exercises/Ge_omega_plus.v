Require Import T1 E0 Lia.

Open Scope E0_scope.

Lemma ge_omega_iff (alpha : E0):
  omega o<= alpha <-> (forall i:nat, i + alpha = alpha).
Proof.
  destruct alpha as [a Ha];  unfold Le;  cbn.
  destruct a; cbn; split; intro H.
  - destruct H, H0.
    now apply le_zero_inv in H0.
  - specialize (H 1); compute in H;
    injection H; discriminate.
  - intro i. apply E0_eq_intro. cbn.
    destruct i; cbn; auto.
    destruct a1; auto.
    now destruct H as [_ [[Heq | Hlt] _]].
  - intros; destruct a1.
    + specialize (H 1); cbn in H.
      assert (a2 = zero) by (eapply nf_of_finite; eauto).
      subst; compute in H; inversion H; lia.
    + repeat split;  auto with T1.
      apply le_trans with (phi0 (ocons a1_1 n0 a1_2)).
      * apply phi0_mono.
        apply le_trans with (ocons a1_1 0 zero).
        -- apply phi0_mono; auto with T1.
        -- apply le_phi0.
      * apply le_phi0.
Qed.


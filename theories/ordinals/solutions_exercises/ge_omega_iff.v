From hydras Require Import T1 E0.
From Coq Require Import Lia.

Open Scope E0_scope.

Lemma ge_omega_iff (alpha : E0):
  omega o<= alpha <-> (forall i:nat, i + alpha = alpha).
Proof.
  destruct alpha as [a Ha];  unfold Le;  cbn.
  -   destruct a; cbn.
      + split.
        *   unfold le; cbn;  intro H; destruct H; destruct H0.
            specialize (le_zero_inv _ H0); discriminate.            
        *  intros; specialize (H 1); compute in H;
           injection H; discriminate.
      +  split; intros.
        * cbn; apply E0_eq_intro; cbn.
          destruct i; cbn; auto.
          --  destruct a1.
              ++  destruct H as [H [H0 H1]]; destruct H0.
              ++   auto.
        *   intros;  destruct a1.
        --   specialize (H 1); cbn in H.
             assert (a2 = zero) by (eapply nf_of_finite; eauto).
             subst; compute in H; inversion H; lia.
        --  repeat split;  auto with T1.    
            apply le_trans with (phi0 (ocons a1_1 n0 a1_2)).
             ++ apply phi0_mono.
                apply le_trans with (ocons a1_1 0 zero); auto with T1.
                **  apply phi0_mono; auto with T1.
                ** apply le_phi0.   
             ++ apply le_phi0.
Qed.


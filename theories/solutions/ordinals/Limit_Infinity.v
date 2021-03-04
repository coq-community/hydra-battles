(** Prove that, for any ordinal [0 < alpha < epsilon0], [alpha] is a limit 
  if and only if forall ordinal [beta < alpha], there exists an infinite 
  number of ordinals betawee [beta] and [alpha]
 *)

From hydras Require Import Epsilon0 T1.
Open Scope t1_scope.
From Coq Require Import Ensembles Image Compare_dec.


Definition Infinite {A: Type} (E: Ensemble A) :=
  exists s: nat -> A, injective nat A s /\ forall i, In  E (s i).

Section On_alpha.

  Variable alpha : T1.
  Hypothesis Halpha : nf alpha.
  Hypothesis HnonZero : alpha <> zero.

  Section S1.
    Hypothesis H : limitb  alpha.

    Variable beta : T1.
    Hypothesis Hbeta : beta t1< alpha.

    Definition s (i:nat) := beta + S i.
    
    Lemma L1 (i: nat) : beta t1< s i t1< alpha.
    Proof.
      induction i; unfold s; cbn.
      - split.
        + apply LT_add; eauto with T1; discriminate.
        + rewrite <- succ_is_plus_one; apply succ_lt_limit;auto.
      -  replace (beta + FS (S i)) with (succ (beta + S i)).
         + destruct IHi; split.            
           *  apply LT_trans with (s i); auto.
              apply LT_succ; eauto with T1.
           * apply succ_lt_limit; auto.
         + rewrite succ_of_plus_finite.
           * reflexivity.
           * eauto with T1.
    Qed.

    (** Shows that [s] is infinite *)
    
    Lemma L2 : forall i,  s i t1< s (S i).
    Proof.
      unfold s; intro i;
        apply plus_smono_LT_r; eauto with T1.
      change (fin (S i)) with (FS i);
        change (fin (S (S i))) with (FS (S i)).
      rewrite  <- succ_compatS; eauto with T1.
      apply LT_succ; eauto with T1.
    Qed.

    
    Lemma L3: injective _ _ s.
      assert (mono: forall i j, i < j -> s i t1< s j).      
      {
        induction 1.
        - apply L2.
        - transitivity (s m); auto.
          apply L2.
      }
      intros i j;
        destruct (lt_eq_lt_dec i j) as [[H0 | Heq] | H0]; [|auto|];
          intro e; apply mono in H0; rewrite e in H0; destruct (LT_irrefl H0).  
    Qed.
    
  End S1.

  Section S2.
    Hypothesis H :  forall beta, beta t1< alpha ->
                                 exists gamma, beta t1< gamma t1< alpha.

    Lemma L4 : limitb alpha.
    Proof.
      destruct (zero_limit_succ_dec Halpha) as [[Hzero | Hlim] | Hsucc].
      - now destruct HnonZero.
      - assumption.
      - destruct Hsucc as [beta [Hbeta e]]; subst; destruct (H beta).
        + now apply LT_succ.
        + destruct (@LT_succ_LT_eq_dec x beta); auto.
          * destruct H0; eauto with T1.
          * destruct H0; auto.
          * destruct H0; assert (x t1< x) by (transitivity beta; auto).
            destruct (LT_irrefl H2).
          * subst; destruct H0.
            destruct (LT_irrefl H0).
    Qed.

  End S2.

  Theorem Limit_Infinity : limitb alpha <-> (forall beta,
                                                beta t1< alpha -> Infinite (fun gamma =>  beta t1< gamma t1< alpha)).
  Proof.
    split; intro H.
    - intros beta Hbeta.
      exists (s beta). split.
      apply L3.
      auto.
      intros i; red.
      apply L1; auto.
    -
      specialize (L4 ); intro.
      apply H0.
      intros.
      destruct (H beta H1) as [x [H2 H3]].
      exists (x 0).
      apply H3.     
  Qed.
  
End On_alpha.


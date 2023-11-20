Require Import Arith.
Require Import Iterates F_alpha E0.
Require Import ArithRing Lia   Max.
Import Exp2.
Require Import Compat815.
Open Scope nat_scope.

Lemma LF3 : dominates_from 2 (F_ 3) (fun  n => iterate exp2 n n).
Proof.
  generalize (LF3_2); intros H n Hn; eapply Nat.le_lt_trans.
  -  apply  iterate_le_n_Sn;  intro x; generalize (exp2_gt_id x); lia.
  -  now apply H.
Qed.


 (** * Proof that F_alpha  (S n) > exp2 (F_ alpha n) for alpha >= 3 and 
    n >= 2  (by induction over alpha) *)

Section S1.
  
 
  Let P alpha := forall n, 2 <= n -> exp2 (F_ alpha n) <= F_ alpha (S n).

  Remark F_3_eqn : forall n, F_ 3  n = iterate (F_ 2) (S n) n.
  Proof.
    intro n; ochange (E0fin 3)  (E0_succ (E0fin 2)); now rewrite F_succ_eqn.
  Qed.


  (** ** Base case *)
  
  Lemma P_3 : P 3. 
  Proof.
    intros n H; rewrite (F_3_eqn (S n)); rewrite iterate_S_eqn.
    rewrite F_3_eqn.
    transitivity (exp2 (iterate (F_ 2) (S n) (S n))).
    -   apply PeanoNat.Nat.lt_le_incl; apply exp2_mono.
        apply iterate_mono; auto.
        + apply F_alpha_mono.
        + intro n0; apply (F_alpha_gt (E0fin 2) n0).
    -  specialize (LF2_0 (iterate (F_ 2) (S n) (S n))); intro H0.
       remember (iterate (F_ 2) (S n) (S n)) as N.
       transitivity ((fun i : nat => (exp2 i * i)%nat) N).
       +   assert (0 < N).
           {  rewrite HeqN; cbn; apply F_alpha_positive. }
    
           rewrite PeanoNat.Nat.mul_comm.  
           (** deprecated, not replaced yet *)
           destruct (Compat815.mult_O_le (exp2 N) N).
             auto.
           * lia.
       * apply H2. 
       + apply PeanoNat.Nat.lt_le_incl,  LF2.
  Qed.

  (** Successor case *)
  
  Section Successor.
    
    Variable alpha: E0.
    Hypothesis H_alpha : P alpha.

    Remark R1: forall n, 2 <= n ->
                         forall p, n < p ->
                                   exp2 (F_ alpha n) <= F_ alpha p.
    Proof.
      induction 2.  
      - apply H_alpha; auto.
      - transitivity (F_ alpha m);auto.
        + apply mono_weak.
          * apply F_alpha_mono.
          * auto with arith.
    Qed.


    Section S2.
      Variable n : nat.
      Hypothesis Hn : 2 <= n.

      Remark R3 :
        F_ (E0_succ alpha) (S n)= F_ alpha (iterate (F_ alpha) (S n) (S n)).
      Proof.
        rewrite F_succ_eqn; now rewrite iterate_S_eqn.
      Qed.

      Remark R3' : F_ (E0_succ alpha) n = iterate (F_ alpha) (S n) n.
      Proof.
        now rewrite F_succ_eqn.
      Qed.  

      Remark R4 : F_ (E0_succ alpha) n < iterate (F_ alpha) (S n) (S n).
      Proof.
        rewrite F_succ_eqn; apply iterate_mono; auto with arith.
        - apply F_alpha_mono.
        - intro; apply F_alpha_gt.
      Qed.

      Lemma L2 : exp2 (F_ (E0_succ alpha)  n) <= (F_ (E0_succ alpha) (S n)).
      Proof.
        assert (H: 2 <= (F_ (E0_succ alpha) n)).
        {
          apply Nat.le_lt_trans with n.
          - lia.        
          - apply F_alpha_gt.
        }
        assert (H0: F_ (E0_succ alpha) n < iterate (F_ alpha) (S n) (S n)).
        {
          rewrite F_succ_eqn;  apply iterate_mono; auto.
          - apply F_alpha_mono.
          - intro; apply F_alpha_gt.
        }
        generalize(R1 (F_ (E0_succ alpha) n) H
                      (iterate (F_ alpha) (S n) (S n)) H0); intro H1;
          rewrite <- R3 in H1.
        transitivity ( exp2 (F_ alpha (F_ (E0_succ alpha) n))); [| auto].
        -  apply PeanoNat.Nat.lt_le_incl; apply exp2_mono.
           apply F_alpha_gt.
      Qed.
      
    End S2.

    Lemma L3 : P (E0_succ alpha).
    Proof.
      unfold P; intros;  now apply L2.
    Qed.

  End Successor.

  (** ** Limit case *)
  
  Section Limit.
    Variable lambda : E0.
    Hypothesis Hlambda : E0limit lambda.
    Hypothesis IHlambda :
      forall alpha, E0fin 3 o<= alpha -> alpha o< lambda -> P alpha.


    Remark R5: forall beta, 3 o<= beta -> beta o< lambda ->
                            forall n, 2 <= n ->
                                      forall p, n < p ->
                                                exp2 (F_ beta n) <= F_ beta p.
    Proof.
      induction 4.  
      - apply IHlambda; auto.
      - transitivity (F_ beta m);auto.
        + apply mono_weak.
          * apply F_alpha_mono.
          * auto with arith.
    Qed.

    Section S3.
      Variable n: nat.
      Hypothesis Hn : 2 <= n.

      (* TODO: simplify this proof ! *)
      Lemma L04 : forall beta:T1,
          T1limit beta ->
          forall n, leq lt  (\F (S n)) (Canon.canon beta (S n)).
      Proof.
        destruct beta.
        -  discriminate.
        -  cbn.
           destruct beta1.
           + discriminate.
           + destruct beta2.
             * destruct n0.
               -- cbn.
                  destruct beta1_1; cbn.
                  ++ destruct n1.
                     ** reflexivity.
                     ** intros; apply lt_incl_le.
                        apply head_lt; auto with T1.
                  ++  destruct (pred beta1_2).
                      ** intros; apply lt_incl_le; apply head_lt;
                         auto with T1.
                      **  intros; apply lt_incl_le; apply head_lt.
                          { destruct  n1;cbn.
                            destruct beta1_2; cbn.
                            - destruct beta1_1_1; cbn.
                              + destruct n0; cbn; auto with T1.
                              + destruct (pred beta1_1_2); cbn; auto with T1.
                          -  destruct n0; cbn; auto with T1.
                          - destruct beta1_2; auto with T1.
                            + destruct beta1_1_1.
                              * destruct n0; cbn; auto with T1.
                              * destruct (pred beta1_1_2); cbn; auto with T1.
                          }                            
               -- intros;apply lt_incl_le.
                  destruct (pred (cons beta1_1 n1 beta1_2)).
                  ++  apply head_lt; auto with T1.
                  ++ apply head_lt; auto with T1.
             * intros; apply lt_incl_le.
               destruct n0.
               --  apply head_lt; auto with T1.
               --  apply head_lt; auto with T1.
      Qed. 


      Lemma L04' : forall beta, E0limit beta ->
                                forall n, (S n) o<= 
                                          (Canon.Canon beta (S n)).
      Proof.
        destruct beta; unfold E0limit.
        cbn;  intros; rewrite Le_iff; split. 
        - apply  (@E0.cnf_ok (E0finS n0)).
        - cbn; split.
          + apply L04; auto.
          + cbn; apply Canon.nf_canon; auto.
      Qed.

      Lemma L4 : exp2 (F_ lambda n) <= F_ lambda (S n).
      Proof.
        repeat rewrite (F_lim_eqn lambda); auto.
        transitivity (exp2 (F_ (Canon.Canon lambda (S n))  n)).
        -  apply PeanoNat.Nat.lt_le_incl; apply exp2_mono.
           apply F_mono_l_0 with 0.
           + apply Paths.Canon_mono1; auto.
           + apply Paths.Cor12_E0 with (i := 0); auto. 
             * apply   Paths.Canon_mono1; auto.
             * destruct n.
               -- lia.
               -- apply (@Paths.KS_thm_2_4_E0 _ Hlambda n0 (S n0)).
                  auto with arith.
           + auto with arith. 
        - apply R5; auto.
          + generalize (L04' lambda Hlambda); intro H; specialize (H n).
            eapply E0.Le_trans with (S n).
            * rewrite Le_iff. split. 
              -- now compute.
              -- split.
                 ++ cbn; destruct (Compat815.le_lt_or_eq _ _ Hn).
                    **  apply lt_incl_le;  now apply finite_lt.
                    **  subst n;  apply Comparable.le_refl.
                 ++   cbn; apply nf_FS.
            *  assumption.
          + apply Canon.Canon_lt.
            apply Limit_not_Zero; auto. 
      Qed. 

    End S3.
  End Limit.
  

  Lemma L alpha :  3 o<= alpha -> P alpha.
  Proof.
      pattern alpha; eapply well_founded_induction with E0lt.
    - apply E0lt_wf.
    - clear alpha; intro alpha.  intros IHalpha Halpha.
      destruct (Zero_Limit_Succ_dec  alpha) as [[H1 | H1] | H1].
      +  subst; rewrite Le_iff in Halpha.
         decompose [and] Halpha. cbn in Halpha. destruct Halpha
           as [H1 [H2 H3]].
         rewrite le_lt_eq in H2; destruct H2; try discriminate.
      + red; intros;  eapply L4; auto.
      + destruct H1; subst alpha.
        assert (H: 3 o<= x \/ x = E0fin 2).
        { destruct (le_lt_eq_dec Halpha).
          - left; destruct (E0_Lt_Succ_inv e).
            + apply Lt_Le_incl; auto.
            + subst; apply Le_refl.
          - right;  revert e; ochange (E0fin 3) (E0_succ 2).
            intro; symmetry ; now apply Succ_inj. 
        }
        destruct H.
        *   apply L3; apply IHalpha; auto.
            -- apply Lt_Succ; auto. 
        * subst x; ochange (E0_succ 2) (E0fin 3); apply P_3.
  Qed.

End S1.

Theorem F_alpha_Sn alpha : 3 o<= alpha ->
                   forall n, 2 <= n -> exp2 (F_ alpha n) <= F_ alpha (S n).
Proof. apply L. Qed.


(** What happens if alpha is less than 3, or n less than 2 ? *)


Goal  F_ 2 3 = 63.
  ochange (E0fin 2) (E0_succ (E0fin 1)).
  rewrite F_succ_eqn.
  cbn.
  repeat rewrite LF1.
  reflexivity.
  Qed.
  
Goal  F_ 2 2 = 23.

  ochange (E0fin 2) (E0_succ (E0fin 1)).
  rewrite F_succ_eqn.
  cbn.
  repeat rewrite LF1.
  reflexivity. 
Qed.

Goal  F_ 3 1 = 2047.
  ochange (E0fin 3) (E0_succ (E0_succ (E0fin 1))).
  repeat rewrite F_succ_eqn.
  cbn.
  repeat rewrite F_succ_eqn. cbn.
  repeat rewrite LF1.
  rewrite iterate_S_eqn. cbn.
  repeat rewrite LF1.
  compute.
  reflexivity.
Qed.


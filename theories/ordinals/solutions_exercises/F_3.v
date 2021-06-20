
Require Import Iterates F_alpha E0.
Require Import ArithRing Lia   Max.
Import Exp2.
Require Import Mult.
Open Scope nat_scope.


Lemma LF3 : dominates_from 2 (F_ 3) (fun  n => iterate exp2 n n).
Proof.
  generalize (LF3_2); intros H n Hn; eapply Lt.le_lt_trans.
  -  apply  iterate_le_n_Sn;  intro x; generalize (exp2_gt_id x); lia.
  -  now apply H.
Qed.


 (** * Proof that F_alpha  (S n) > exp2 (F_ alpha n) for alpha >= 3 and 
    n >= 2  (by induction over alpha) *)

Section S1.
  
 
  Let P alpha := forall n, 2 <= n -> exp2 (F_ alpha n) <= F_ alpha (S n).

  Remark F_3_eqn : forall n, F_ 3  n = iterate (F_ 2) (S n) n.
  Proof.
    intro n; ochange (Fin 3)  (Succ (Fin 2)); now rewrite F_succ_eqn.
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
        + intro n0; apply (F_alpha_ge_S (Fin 2) n0).
    -  specialize (LF2_0 (iterate (F_ 2) (S n) (S n))); intro H0.
       remember (iterate (F_ 2) (S n) (S n)) as N.
       transitivity ((fun i : nat => (exp2 i * i)%nat) N).
       +   assert (0 < N).
           {  rewrite HeqN; cbn; apply F_alpha_positive. }
           rewrite PeanoNat.Nat.mul_comm; destruct (mult_O_le (exp2 N) N);
             auto.
           * lia.
       +  apply PeanoNat.Nat.lt_le_incl,  LF2.
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
        F_ (Succ alpha) (S n)= F_ alpha (iterate (F_ alpha) (S n) (S n)).
      Proof.
        rewrite F_succ_eqn; now rewrite iterate_S_eqn.
      Qed.

      Remark R3' : F_ (Succ alpha) n = iterate (F_ alpha) (S n) n.
      Proof.
        now rewrite F_succ_eqn.
      Qed.  

      Remark R4 : F_ (Succ alpha) n < iterate (F_ alpha) (S n) (S n).
      Proof.
        rewrite F_succ_eqn; apply iterate_mono; auto with arith.
        - apply F_alpha_mono.
        - intro; apply F_alpha_ge_S.
      Qed.

      Lemma L2 : exp2 (F_ (Succ alpha)  n) <= (F_ (Succ alpha) (S n)).
      Proof.
        assert (H: 2 <= (F_ (Succ alpha) n)).
        {
          apply Lt.le_lt_trans with n.
          - lia.        
          - apply F_alpha_ge_S.
        }
        assert (H0: F_ (Succ alpha) n < iterate (F_ alpha) (S n) (S n)).
        {
          rewrite F_succ_eqn;  apply iterate_mono; auto.
          - apply F_alpha_mono.
          - intro; apply F_alpha_ge_S.
        }
        generalize(R1 (F_ (Succ alpha) n) H
                      (iterate (F_ alpha) (S n) (S n)) H0); intro H1;
          rewrite <- R3 in H1.
        transitivity ( exp2 (F_ alpha (F_ (Succ alpha) n))); [| auto].
        -  apply PeanoNat.Nat.lt_le_incl; apply exp2_mono.
           apply F_alpha_ge_S.
      Qed.
      
    End S2.

    Lemma L3 : P (Succ alpha).
    Proof.
      unfold P; intros;  now apply L2.
    Qed.

  End Successor.

  (** ** Limit case *)
  
  Section Limit.
    Variable lambda : E0.
    Hypothesis Hlambda : Limitb lambda.
    Hypothesis IHlambda :
      forall alpha, Fin 3 o<= alpha -> alpha o< lambda -> P alpha.


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
          limitb beta ->
          forall n, T1.le (fin (S n)) (Canon.canon beta (S n)).
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
                     ** intros; apply lt_le_incl.
                        apply head_lt; auto with T1.
                  ++  destruct (pred beta1_2).
                      ** intros; apply lt_le_incl; apply head_lt;
                         auto with T1.
                      **  intros; apply lt_le_incl; apply head_lt.
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
               -- intros;apply lt_le_incl.
                  destruct (pred (ocons beta1_1 n1 beta1_2)).
                  ++  apply head_lt; auto with T1.
                  ++ apply head_lt; auto with T1.
             * intros; apply lt_le_incl.
               destruct n0.
               --  apply head_lt; auto with T1.
               --  apply head_lt; auto with T1.
      Qed. 


      Lemma L04' : forall beta, Limitb beta ->
                                forall n, (S n) o<= 
                                          (Canon.Canon beta (S n)).
      Proof.
        destruct beta; unfold Limitb.
        cbn; split. 
        -  apply  (@E0.cnf_ok (FinS n0)).
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
            * split.
              -- now compute.
              -- split.
                 ++ cbn; destruct (le_lt_or_eq _ _ Hn).
                    **  apply lt_le_incl;  now apply finite_lt.
                    **  subst n;  apply T1.le_refl.
                 ++   cbn; apply nf_FS.
            *  assumption.
          + apply Canon.Canon_lt.
            apply Limit_not_Zero; auto. 
      Qed. 

    End S3.
  End Limit.
  

  Lemma L alpha :  3 o<= alpha -> P alpha.
  Proof.
      pattern alpha; eapply well_founded_induction with Lt.
    - apply Lt_wf.
    - clear alpha; intro alpha.  intros IHalpha Halpha.
      destruct (Zero_Limit_Succ_dec  alpha) as [[H1 | H1] | H1].
      + subst;  compute in Halpha; decompose [and] Halpha ; tauto.
      + red; intros;  eapply L4; auto.
      + destruct H1; subst alpha.
        assert (H: 3 o<= x \/ x = Fin 2).
        { destruct (le_lt_eq_dec Halpha).
          - left; destruct (E0_Lt_Succ_inv l).
            + apply Lt_Le_incl; auto.
            + subst; apply Le_refl.
          - right;  revert e; ochange (Fin 3) (Succ 2).
            intro; symmetry ; now apply Succ_inj. 
        }
        destruct H.
        *   apply L3; apply IHalpha; auto.
            -- apply Lt_Succ; auto. 
        * subst x; ochange (Succ 2) (Fin 3); apply P_3.
  Qed.

End S1.

Theorem F_alpha_Sn alpha : 3 o<= alpha ->
                   forall n, 2 <= n -> exp2 (F_ alpha n) <= F_ alpha (S n).
Proof. apply L. Qed.


(** What happens if alpha is less than 3, or n less than 2 ? *)


Goal  F_ 2 3 = 63.
  ochange (Fin 2) (Succ (Fin 1)).
  rewrite F_succ_eqn.
  cbn.
  repeat rewrite LF1.
  reflexivity.
  Qed.
  
Goal  F_ 2 2 = 23.

  ochange (Fin 2) (Succ (Fin 1)).
  rewrite F_succ_eqn.
  cbn.
  repeat rewrite LF1.
  reflexivity. 
Qed.

Goal  F_ 3 1 = 2047.

ochange (Fin 3)   (Succ (Succ (Fin 1))).
 repeat rewrite F_succ_eqn.
 cbn.
 repeat rewrite F_succ_eqn. cbn.
 repeat rewrite LF1.
 rewrite iterate_S_eqn. cbn.
 repeat rewrite LF1.
 compute.
 reflexivity.
Qed.


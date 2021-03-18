(**
 Pierre Castéran, LaBRI and University of Bordeaux 


 We prove that the impossibility result of #<a href="./hydras.Hydra.Epsilon0_Needed_Free.html"> Epsilon0_Needed_Free</a># still holds for "standard" battles *)



From hydras Require Import Epsilon0_Needed_Generic.
Import Hydra_Lemmas Epsilon0 Canon Paths Relation_Operators O2H.


Open Scope t1_scope.
Section Impossibility_Proof.
  
  Context (mu: T1)
          (Hmu: nf mu)
          (m : Hydra -> T1)
          (Var : Hvariant  T1_wf standard m)
          (Hy : BoundedVariant Var mu).

  Let big_h := big_h mu.
  Let small_h := small_h mu m.   

  Lemma m_ge : m big_h t1<= m small_h.
  Proof.
    unfold big_h, small_h.  eapply m_ge_generic; trivial.   
    intros; eapply variant_decr; eauto.
     intro; subst h; apply (head_no_round_n _ _ H).
  Qed.

  (** ** Proof of the inequality m small_h t1< m big_h *)

  (**  The measure is strictly decreasing along any round *)

  Lemma Lvar : forall h h0 i ,  h <> head -> 
                                battle_rel standard i h h0 -> m h0 t1< m h.
  Proof.   
    intros h h0 i H  H1;  apply Var with  i; auto.
  Qed.
  
  (** Application to standard battles *)
  
  Lemma m_decrease : forall j h0 i h,
      h <> head -> battle standard i  h j h0  -> m h0 t1< m h.
  Proof.
    induction 2.  
    -  apply Lvar with i; auto. 
    -  destruct (h_eq_dec h'' head).
       +  rewrite e in H1;  elimtype False.
          eapply standard_battle_head; eauto.  
       + apply LT_trans with (m h'');auto.
         apply Lvar with i; auto.
  Qed.
  
  (** Conversion of ordinal inequalities into  standard battles  *)

  
  (* begin hide *)
  Lemma o2iota_0 : forall j beta i alpha,
      standard_pathR j beta i alpha -> (0 < i)%nat ->  nf alpha ->
      nf beta ->  beta <> T1.zero -> 
      battle standard (Nat.pred i) (iota alpha) j (iota beta) .
  Proof.
    induction 1.
    - intros; subst j; destruct i.
      +  now destruct  H2.
      +  simpl; left; trivial.
         * subst beta;   apply canonS_iota_i; trivial.
    -  intros  H0 H1 H2 H3;   destruct i.
       + inversion H0.
       +  eapply battle_trans with  (S i) (iota (canon alpha (S i)));
            trivial.
          2:(left; simpl); trivial.
          replace (S i) with (Nat.pred (S (S i))).
          *   eapply IHstandard_pathR; trivial.
              auto with arith. 
              eapply nf_canonS;eauto.
          * simpl; auto.
          * apply canonS_iota_i; trivial.
            intro; subst alpha.
            apply H3;  eapply standard_path_zero; eauto.
  Qed.

  Lemma o2iota_1 : forall j beta i alpha,
      standard_pathR j beta ( S i) alpha ->  nf alpha ->
      nf beta ->  beta <> T1.zero -> 
      battle standard  i (iota alpha) j (iota beta) .
  Proof.
    intros.    
    change i with (Nat.pred (S i)).
    apply o2iota_0; auto.
 auto with arith.
  Qed.
  
  Lemma o2iota : forall alpha  ,
      nf alpha -> forall i, 
        (0 < i)%nat -> alpha = T1.zero \/ 
                       exists k : nat, 
                         battle standard (Nat.pred i) (iota alpha) k head .
  Proof.
    intros alpha; transfinite_induction_lt alpha.
    intros x H H0 i H1;  destruct (T1_eq_dec x T1.zero).
    -   now  left.
    -  right; destruct i.    
       +   inversion H1.
       +   specialize (H (canonS x i) H0); 
             assert (nf (canonS x i)) by (eapply nf_canonS; eauto).
           assert (T1.lt (canonS x i) x).
           { eapply canonS_lt; eauto. }
           specialize (H H2 H3 H2 (S (S i)) ).
           destruct H.
           *  auto with arith.
           *  destruct (canonS_zero_inv _ _ H).
              subst; now destruct n.
              subst; exists (S i);  simpl;  left.
              { left;  split; now left.
              }
           *  simpl;  destruct H; exists x0.
              eapply battle_trans with (S i) (iota (canon x (S i))).
              { simpl; simpl in H; trivial. }
              { left.
                eapply canonS_iota_i; auto.
              }
  Qed.
  
  (* end hide *)
  
  Lemma LT_to_standard_battle :
    forall alpha beta,
      beta t1< alpha ->
      exists n i,  battle standard   n (iota alpha)  i (iota beta).
  Proof.
    intros;  assert (nf beta) by eauto with T1.
    assert (nf alpha) by eauto with T1.
    assert (Halpha : alpha <> zero) .
    { intro; subst. apply (not_LT_zero H). }
    destruct (T1_eq_dec beta zero) as [Hbeta | Hbeta].
    {    subst beta.
         destruct (o2iota alpha H1 1).
         auto.
         subst; now destruct Halpha.         
         destruct H2.
         exists 0,x.
         assumption.
    }
    {   destruct (Lemma2_6_1 H1 H) as [n Hn].
        destruct n.
        {
          destruct (constant_to_standard_path H1 Hn).
          now     apply not_zero_lt.

          exists 0, x.
          apply o2iota_1.
          assumption. 
          auto.
          auto.
          auto.           
        }
        {
          destruct (constant_to_standard_path H1 Hn).
          now     apply not_zero_lt.
          apply o2iota_1 in s; auto.
          exists ((S n)), x; auto.
        }
    }
  Qed.


  Remark Rem3 : beta_h mu m  t1< mu.
  Proof. unfold beta_h; auto. destruct Hy; auto. Qed. 
  
  Remark Rem4 : exists n i,
      battle  standard n (iota mu) i (iota (beta_h mu m)).
  Proof. apply (LT_to_standard_battle  _ _ Rem3).  Qed. 
  
  Lemma m_lt : m small_h  t1< m big_h.
  Proof.
    destruct Rem4 as [x [i H]].
    eapply m_decrease with i x; eauto.
    intro H0;  unfold big_h in *.
    clear H;  destruct (T1_eq_dec mu T1.zero).
    -  now apply (mu_positive  _  mu Hmu m Var Hy). 
    -  apply n;   destruct mu.
       + auto. 
       + discriminate H0.
  Qed. 

  (** End of the proof *)
  
  Fact self_lt_standard : m big_h t1< m big_h.
  Proof. 
    apply LE_LT_trans with (m small_h).
    - apply m_ge. 
    - apply m_lt.
  Qed. 


  Theorem Impossibility_std: False.
  Proof.  apply (LT_irrefl self_lt_standard).  Qed.

  

End Impossibility_Proof.



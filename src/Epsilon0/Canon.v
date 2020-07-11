
(**  Canonical Sequences of ordinals below epsilon0

Pierre Casteran, 
       LaBRI and University of Bordeaux.

       After J. Ketonen and R. Solovay's paper
  " Rapidly Growing Ramsey Functions" _in_
    Annals of mathematics, Mar. 1981 

 *)

Require Export Arith Omega  T1 .
Import Relations Relation_Operators.

Set Implicit Arguments.
Open Scope t1_scope.

(** * Definitions *)

(* Computes {alpha}(i+1) *)

Fixpoint canonS alpha (i:nat) : T1 :=
  match alpha with
    zero => zero
  | ocons zero 0 zero => zero
  | ocons zero (S k) zero => FS k
  | ocons gamma 0 zero =>
    match T1.pred gamma with
      Some gamma' => ocons gamma' i zero
    | None => ocons (canonS gamma i) 0 zero
    end
  |  ocons gamma (S n) zero =>
     match T1.pred gamma with
       Some gamma' => ocons gamma n (ocons gamma' i zero)
     | None => ocons gamma n (ocons (canonS gamma i) 0 zero)
     end
  | ocons alpha n beta => ocons alpha n (canonS beta i)
  end.


(** Computes {alpha}(i) for i >= 1 *)

Definition canon alpha i :=
  match i with 0 => zero | S j => canonS alpha j end.



(** * Properties *)


(** ** Rewriting lemmas *)

Lemma canonS_zero i  : canonS zero i = zero.
Proof. reflexivity. Qed.

Lemma canon_zero i :  canon zero i = zero.
Proof. now destruct i. Qed.

Lemma canonS_tail :
  forall alpha n beta i,  nf (ocons alpha n beta) -> 
                          beta <> 0 ->
                          canonS (ocons alpha n beta) i =
                          ocons alpha n (canonS beta i).
Proof.
  destruct alpha as [| alpha1 n alpha2].
  - destruct 2; auto.
    eapply nf_of_finite; eauto.
  - intros; simpl;  destruct n0, beta; auto.
    + destruct H0; auto. 
    + destruct H0; auto.
Qed.

Lemma canonS_lim1 : forall i lambda, nf lambda -> limitb lambda 
                                 -> canonS (ocons lambda 0 zero) i =
                                    phi0 (canonS lambda i).
Proof.
  intros; unfold canonS at 1; destruct lambda.
  - simpl; discriminate.
  - replace ( T1.pred (ocons lambda1 n lambda2)) with (@None T1).
    + f_equal.
    + rewrite pred_of_limit;auto.
Qed.

Lemma canonS_lim2  i n lambda: 
    nf lambda -> limitb lambda 
    -> canonS (ocons lambda (S n) zero) i =
       ocons  lambda n (phi0 (canonS lambda i)).
Proof.
  intros; unfold canonS at 1;  destruct lambda.
  - simpl; discriminate.
  - replace ( T1.pred (ocons lambda1 n lambda2)) with (@None T1);   f_equal.
    all :  rewrite T1.pred_of_limit;auto.
Qed.


Lemma canonS_succ i alpha : nf alpha -> canonS (succ alpha) i = alpha.
Proof.
  induction alpha.
  -   reflexivity.
  -   destruct alpha1.
      + intros; replace alpha2 with zero.   
        * reflexivity. 
        *  T1_inversion H; auto. 
      +  intros; simpl;  destruct n.
         * destruct alpha2.
          { reflexivity. }
          { simpl;destruct alpha2_1.
            - f_equal;  apply nf_inv2 in H.
              T1_inversion H; now subst. 
            - f_equal; rewrite <- IHalpha2; f_equal;  eauto with T1.
          }
         *  case_eq (T1.succ alpha2).
            { intros;  now destruct (@T1.succ_not_zero alpha2). }
            { intros; f_equal ; rewrite <- IHalpha2.
              - now rewrite <- H0.
              - eauto with T1. }
Qed.


Lemma canonS_phi0_succ_eqn i gamma:
  nf gamma -> 
  canonS (phi0 (succ gamma)) i = ocons gamma i zero.
Proof.
  intros; unfold canonS at 1;  rewrite T1.pred_of_succ;
    case_eq (T1.succ gamma); trivial.
  -  intro; destruct (succ_not_zero _ H0); auto 2.
Qed.


Lemma canonS_ocons_succ_eqn2 i n gamma :
    nf gamma -> 
    canonS (ocons (T1.succ gamma) (S n) zero) i =
    ocons (T1.succ gamma) n (ocons gamma i zero).
Proof.
  intros; unfold canonS at 1;   rewrite T1.pred_of_succ;
    case_eq (T1.succ gamma); trivial.
  -  intro; destruct (T1.succ_not_zero _ H0).
Qed.


Lemma canonSSn (i:nat) :
  forall alpha n  ,
    nf alpha -> 
    canonS (ocons alpha (S n) zero) i =
    ocons alpha n (canonS (ocons alpha 0 zero) i).
Proof. 
  intros; destruct (@zero_limit_succ_dec alpha).
  - eauto with T1.
  - destruct s.
    + destruct n.
      subst alpha;  reflexivity.       
      subst alpha; reflexivity.
    + rewrite canonS_lim2 ; auto.
      rewrite canonS_lim1; auto.
  - destruct s as [beta [Hdeta e]]; subst alpha.
    rewrite canonS_ocons_succ_eqn2, canonS_phi0_succ_eqn; auto.
Qed.



Lemma canonS_zero_inv (alpha:T1) (i:nat) : 
  canonS alpha i = zero -> alpha = zero \/ alpha = one.
Proof.
  destruct alpha; cbn; auto.
  destruct alpha1, n, alpha2;auto; try discriminate.
  all:  destruct (T1.pred (ocons alpha1_1 n0 alpha1_2)); try discriminate.
Qed.

(** Canonical sequences and the order LT *)

Lemma canonS_LT i alpha :
  nf alpha -> alpha <> zero ->
  canonS alpha i <  alpha.
Proof with eauto with T1.
  transfinite_induction_lt alpha.
  clear alpha; intros alpha Hrec Halpha;
    destruct (zero_limit_succ_dec Halpha).
    - destruct s.
      + (* alpha = zero *)
       subst alpha; now destruct 1.
      + (* alpha is a limit *)
        destruct alpha.
        * now destruct 1.
        * intros H; destruct (T1_eq_dec alpha1 zero).
          { subst.
            destruct n.
            - replace alpha2 with zero.
              + split;auto. 
                simpl;  constructor.
                split;simpl;constructor.
              + T1_inversion Halpha; auto.
            -  replace alpha2 with zero.
               +  simpl; split;  constructor.
                  apply finite_lt; auto with arith. 
                  apply nf_FS.
               +  T1_inversion Halpha; auto. 
          }
          destruct alpha2.
          { destruct n.
             {   destruct  (@zero_limit_succ_dec alpha1) ...
                 - destruct s.
                  + subst;  now destruct n0. 
                  + rewrite canonS_lim1.
                    * split.
                      --   apply single_nf; auto.
                 destruct (Hrec alpha1) ...
                 apply head_lt_ocons ;  auto.
                 -- split; auto with T1.
                  ++   apply head_lt; apply Hrec ...
                       apply head_lt_ocons; auto.
                    * auto with T1.
                    * trivial.
                 -  destruct s.
                 { destruct a.
                     { subst; rewrite canonS_phi0_succ_eqn.
                       - split.
                       + apply single_nf; auto. 
                       + split; trivial.
                         * apply head_lt; auto.
                           apply lt_succ; auto. 
                       - eauto with T1.
                     }
                 }
             }
             destruct  (@zero_limit_succ_dec alpha1) ...
             { destruct s.
               - subst; now destruct n0.   
               - rewrite canonS_lim2.
                 + split.
                  { apply ocons_nf ...
                    - destruct (Hrec alpha1) ...
                      + apply head_lt_ocons.
                      + tauto.
                    - eauto with T1.
                      apply single_nf. 
                      destruct (Hrec alpha1); eauto with T1.
                      apply head_lt_ocons.
                  }
                  split.
                   * apply coeff_lt; auto with arith.
                   * eauto with T1.
                     + auto.
                     + eauto with T1.
             }
             destruct s; subst.
             {  destruct a; subst; rewrite canonS_ocons_succ_eqn2.
                  -  split.
                   { apply ocons_nf. 
                     - apply lt_succ.
                     - apply succ_nf; auto.
                     - apply single_nf; auto.
                   }
                     + split.
                       {  apply coeff_lt; auto with arith. }
                       auto with T1.
                  - auto.
             }
          }
          rewrite canonS_tail.
          {
            split.
            {
              apply nf_intro ...
              - destruct (Hrec  (ocons alpha2_1 n1 alpha2_2)) ...
                discriminate.
              - apply lt_phi0_phi0R.
                apply T1.lt_trans with (ocons alpha2_1 n1 alpha2_2).
                + destruct (Hrec (ocons alpha2_1 n1 alpha2_2)) ...
                  *  discriminate.
                  * tauto.
             +  
                apply lt_phi0_phi0.
                apply lt_phi0_intro with n;auto.
            }
            split.
            - apply tail_lt. 
              destruct (Hrec (ocons alpha2_1 n1 alpha2_2)); auto.
              +  eauto with T1.
            + apply tail_lt_ocons;  auto.
            + eauto with T1.
            + discriminate.
            + destruct (Hrec (ocons alpha2_1 n1 alpha2_2)) ...
              discriminate.
              tauto. 
            - trivial. 
          }
           eauto with T1.
          discriminate.
    - destruct s.
      {   destruct a; subst.
          intros; rewrite canonS_succ; auto.
          split; auto.
          split; auto; apply lt_succ; auto.
      }
Qed. 

Lemma nf_canonS  i alpha:  nf alpha -> nf (canonS alpha i).
Proof.
  intros Hnf; destruct (T1_eq_dec alpha zero).
  - subst; constructor.
  - destruct  (canonS_LT i  Hnf); auto.
Qed.

Lemma nf_canon : forall i alpha, nf alpha -> nf (canon alpha i).
Proof.
  destruct i.
  - simpl; auto with T1.
  - intros; now apply nf_canonS. 
Qed.


Lemma canonS_lt : forall i alpha, nf alpha -> alpha <> zero ->
                              T1.lt (canonS alpha i) alpha.
Proof.
  intros i alpha Hnf.
  destruct (T1_eq_dec alpha zero).
  - subst. now destruct 1.
  - destruct  (canonS_LT i Hnf); tauto.
Qed.

Lemma canonS_cons_not_zero : forall i alpha n beta,
    alpha <> zero -> canonS (ocons alpha n beta) i <> zero.
Proof. 
  destruct alpha.
  -  now destruct 1.
  -  intros; cbn.
     destruct n0, beta, alpha1, n; try discriminate. 
     all: destruct (T1.pred alpha2); try discriminate. 
Qed.


(** ** Canonical sequences of limit ordinals *)


Lemma limitb_canonS_not_zero i lambda:
  nf lambda -> limitb lambda  -> canonS lambda i <> zero.
Proof.
  destruct lambda as [ | alpha1 n alpha2].
  - discriminate.
  - intros; simpl; destruct alpha1.
    +   destruct n.
        *  destruct alpha2 ; discriminate.
        *  destruct alpha2; discriminate.
    +  destruct n.
       *  destruct alpha2.
          {  destruct (T1.pred (ocons alpha1_1 n0 alpha1_2));
               discriminate. }
          discriminate.
       *   destruct alpha2.
           destruct (T1.pred (ocons alpha1_1 n0 alpha1_2));
             discriminate.
           discriminate.
Qed.

(** 
Let lambda  be a limit ordinal. For any beta < lambda, we can 
compute some item of the canonical sequence  of lambda which is 
greater than beta.
   
   It is a constructive way of expressing that lambda is the 
limit of its  own canonical sequence 
*)

Lemma canonS_limit_strong lambda : 
  nf lambda ->
  limitb lambda  ->
  forall beta, beta < lambda ->
               {i:nat | beta < canonS lambda i}.
Proof.
  transfinite_induction lambda; clear lambda ; intros lambda Hrec Hlambda.
  intros   H beta H1.
  assert (Hbeta: nf beta) by eauto with T1.
  destruct (zero_limit_succ_dec Hlambda).
  -   destruct s.   
      { (* lambda = zero *)
        subst lambda; inversion H1;  destruct (not_LT_zero H1).
      }
      destruct lambda.
      + discriminate.
      + destruct (T1.limitb_cases Hlambda i).
       { (* first case : beta = zero *)
        destruct a; subst lambda2; destruct beta.
        { exists 0; apply not_zero_lt. 
          apply nf_canonS; auto.
          apply limitb_canonS_not_zero;auto.
        }
        destruct (LT_inv_strong H1).
        * destruct n.
          destruct (@zero_limit_succ_dec   lambda1); eauto with T1.
        -- destruct s.
           ++ subst; assert (False) by (eapply not_LT_zero; eauto).
              contradiction. 
           ++ assert {i :nat | (beta1 < canonS lambda1 i)%t1}.         
              { apply Hrec.
                apply head_LT_cons; auto with T1.
                all: auto.
              }
              destruct H3 as [x l].
              exists x; rewrite canonS_lim1; eauto with T1.
        --  destruct s as [x [H4 H5]].
            subst lambda1; assert ({beta1 < x} + {beta1 = x})%t1.
            { apply  LT_succ_LT_eq_dec in H2 ;eauto with T1.  }
            destruct H3.
            ++ exists 0; rewrite canonS_phi0_succ_eqn;auto with T1.
            ++ subst; exists (S n0);  rewrite canonS_phi0_succ_eqn; auto. 
               apply LT3; auto with arith.
        -- clear i; exists 0; rewrite canonSSn.
           ++ apply LT2; eauto with T1.
              apply nf_intro; eauto with T1.
              apply nf_canonS; eauto with T1.
              apply lt_phi0_phi0R.
              apply canonS_lt.
              eapply nf_coeff_irrelevance;eauto. 
              discriminate. 
           ++ eauto with T1.
        *  subst.
          -- destruct n.
             not_neg H3.
             apply lt_n_Sm_le in H3.
             destruct (Compare_dec.le_lt_eq_dec _ _ H3).
             exists 0; rewrite canonSSn. 
             apply LT3; auto.
             {
               apply nf_intro; eauto with T1.
               apply nf_canonS; eauto with T1.
               apply lt_phi0_phi0R.
               apply canonS_lt.
               eapply nf_coeff_irrelevance;eauto.     
               discriminate.  
             }
             { eauto with T1. }
             
             assert {i: nat |  beta2 < (canonS (ocons lambda1 0 zero) i)}%t1.
             { apply Hrec.
               -- apply LT3;auto with arith.
               -- cbn;  destruct lambda1.
                  destruct H1; auto.
                  auto.
               -- cbn; destruct lambda1.
                  cbn in H; discriminate.
                  auto. 
               --  split.
                   ++ eauto with T1.
                   ++ split. 
                      ** apply lt_phi0_phi0.     
                      apply lt_phi0_intro with n0;auto with T1.
                      ** eapply nf_coeff_irrelevance;eauto.     
             }
             subst;
               assert
                 ({i: nat |  beta2 < (canonS (ocons lambda1 0 zero) i)})%t1.
             { apply Hrec.
               - apply LT3;auto with arith.
               - cbn;  destruct lambda1.
               + destruct H2;auto. 
               + auto.
               - cbn;  destruct lambda1.
                 + destruct H2; auto. 
                 + auto.                
               - split.
                 + eauto with T1.
                 + split. 
                 * apply lt_phi0_phi0.    
                  apply lt_phi0_intro with n;auto with T1.
                 * eapply nf_coeff_irrelevance;eauto.   
             }
             destruct H4;  exists x; rewrite canonSSn. 
             apply LT4;auto.
             { 
               apply nf_intro;  eauto with T1.
               apply lt_phi0_phi0R.   
               apply canonS_lt.
               apply nf_phi0; eauto with T1.
               intro; subst; discriminate.
             }
             auto.
        *  elimtype False.
          destruct (not_LT_zero H4).
      }
      destruct a ;  assert (lambda2 <> zero). {
        intro; subst; discriminate.  } 
      destruct beta.
       * exists 0;  apply not_zero_lt.
         apply nf_canonS; auto with T1.
         apply limitb_canonS_not_zero; eauto with T1.
       *  destruct (LT_inv_strong H1).
          -- exists 0;  rewrite canonS_tail.
             apply LT2;auto.
          { apply nf_intro;  eauto with T1.
            apply nf_canonS; eauto with T1.
            apply lt_phi0_phi0R.   
            apply T1.lt_trans with lambda2.
            apply canonS_lt; eauto with T1.
            apply lt_phi0_phi0.
            apply lt_phi0_intro with n; eauto with T1.
          }
          auto.
          auto.
         --  destruct H4; exists 0; rewrite canonS_tail.
             apply LT3;  auto.
             { apply nf_intro. 
               - eauto with T1.
               - apply nf_canonS; eauto with T1.
               - apply lt_phi0_phi0R.   
                 apply T1.lt_trans with lambda2.
                 apply canonS_lt; eauto with T1.
                 apply lt_phi0_phi0.
                 apply lt_phi0_intro with n; eauto with T1.
             }
             all: auto. 
      --  subst; assert ({i: nat |  beta2 < (canonS lambda2 i)})%t1.
      { apply Hrec.
        { apply tail_LT_cons; auto. }
        1,2: eauto with T1.
        assumption.
      }
      destruct H4 as [x Hx]; exists x; rewrite canonS_tail.
      apply LT4; auto. 
      {
        apply nf_intro. 
        eauto with T1.
        apply nf_canonS; eauto with T1.
        apply lt_phi0_phi0R.   
        apply T1.lt_trans with lambda2.
        apply canonS_lt; eauto with T1.
        apply lt_phi0_phi0.
        apply lt_phi0_intro with n; eauto with T1.
      }
      all: auto. 
  -   destruct s as [t [Ht Ht']]; subst lambda.
      destruct (@limitb_succ t); auto. 
Defined.


Lemma canon_limit_strong lambda : 
  nf lambda ->
  limitb lambda  ->
  forall beta, (beta < lambda ->
                {i:nat | beta < canon lambda i})%t1.
Proof.
  intros H H0 beta H1; destruct (canonS_limit_strong H H0 H1) as [x Hx];
    exists (S x);auto.
Defined.


Lemma canonS_limit_lub (lambda : T1) :
  nf lambda -> limitb lambda  ->
  strict_lub (fun i => canonS lambda i) lambda.
Proof.
  split.
  - intros; split.
    + now  apply nf_canonS.
    +    split; trivial.
         * apply canonS_lt;    auto.
           intro H1;subst; discriminate.
  - intros l' Hl';  assert (nf l').
    {  specialize (Hl' 0); eauto with T1. }
    destruct (T1.lt_eq_lt_dec lambda l').
    + repeat split;auto.
      destruct s.
      *  auto with T1. 
      *  subst; auto with T1. 
    + assert (l' < lambda)%t1 by (split; auto).
      destruct (canonS_limit_strong   H H0 H2).
      specialize (Hl' x).
      assert (l' < l')%t1.
      { apply LT_LE_trans with  (canonS lambda x); auto. }
      now destruct (@LT_irrefl l' ).
Qed. 


Lemma canonS_limit_mono alpha i j : nf alpha -> limitb alpha  ->
                                    (i < j)%nat ->
                                    canonS alpha i < canonS alpha j.
Proof with eauto with T1.
  pattern alpha ; apply transfinite_recursor_lt.
  clear alpha;  intros alpha Hrec alpha_nf.
  intros.  
  destruct alpha.
  - discriminate.
  -  destruct (limitb_cases alpha_nf H).
     +  destruct a;subst.
        destruct (@zero_limit_succ_dec alpha1) ...
        *   destruct s.   
            { subst;   discriminate H. }
            {   destruct n.
                - repeat rewrite canonS_lim1 ...
                  {  apply LT2 ...
                     apply single_nf. 
                     apply nf_canonS ...
                     apply single_nf. 
                     apply nf_canonS ...
                     apply Hrec ...
                     apply head_lt_ocons.
                  }
                - repeat rewrite canonS_lim2 ...
                  {
                    apply LT4 ...
                    apply nf_ocons_LT ...
                    apply canonS_LT ...
                    apply single_nf. 
                    apply nf_canonS ...
                    apply nf_ocons_LT ...
                    apply canonS_LT ...
                    apply single_nf; apply nf_canonS ...
                    apply LT2 ...
                    apply single_nf;
                      apply nf_canonS ...
                    apply single_nf;
                      apply nf_canonS ...
                    apply Hrec ...
                    apply head_lt_ocons.
                  }
            }
        * destruct s;subst.
          destruct a.
          subst alpha1.
          destruct n.
          { repeat rewrite canonS_phi0_succ_eqn ... }
          {
            repeat rewrite canonS_ocons_succ_eqn2 ...
            apply LT4 ...
            apply nf_ocons_LT ...
            apply LT_succ ...
            apply nf_ocons_LT ...
            apply LT_succ ...
          }
     + destruct a.
       repeat rewrite canonS_tail ...
       * apply  LT4 ...
         apply nf_intro ...
         apply nf_canonS ...
         apply lt_phi0_phi0R ...
         apply T1.lt_trans with alpha2 ...
         apply canonS_lt ...
         apply lt_phi0_phi0 ...
         apply lt_phi0_intro with n ...
         apply nf_intro ...
         apply nf_canonS ...
         apply lt_phi0_phi0R ...
         apply T1.lt_trans with alpha2 ...
         apply canonS_lt ...
         apply lt_phi0_phi0 ...
         apply lt_phi0_intro with n ...
         apply Hrec ...
         apply tail_lt_ocons ...
Qed.


Lemma canonS_LE alpha n :
    nf alpha ->  canonS alpha n <= canonS alpha (S n).
  Proof.
    intro H; destruct (zero_limit_succ_dec H).
    -   destruct s. 
        +  subst; cbn. 
           apply LE_refl; auto with T1.
        + apply LE_r; eapply canonS_limit_mono; auto.
    - destruct s as [gamma [Hgamma Hgamma']]; subst .
      repeat rewrite canonS_succ;auto with T1.
      apply LE_refl;auto. 
  Qed. 


  (** Adaptation to E0 *)
  
Require Export   E0.
Open Scope E0_scope.

Definition CanonS (alpha:E0)(i:nat): E0.
  refine (@mkord (@canonS (cnf alpha) i) _);  apply nf_canonS.
  destruct alpha;auto.
Defined.

Definition Canon (alpha:E0)(i:nat): E0 :=
  match i with 0 => Zero 
          | S j => CanonS alpha j
  end.

Lemma CanonS_Canon alpha i : Canon alpha (S i) = CanonS alpha i.
Proof. reflexivity. Qed.
  
Lemma Canon_Succ beta n: Canon (Succ beta) (S n) = beta.
Proof.
  destruct beta. simpl. unfold CanonS, Succ. simpl.
  apply E0_eq_intro. simpl.
  now rewrite (canonS_succ).  
Qed.

Lemma Canon_Omega k : Canon omega k = Fin k.
Proof.
  destruct k.
  - now cbn.
  - apply E0_eq_intro; reflexivity.
Qed.

Hint Rewrite Canon_Omega : E0_rw.

Lemma CanonSSn (i:nat) :
  forall alpha n  , alpha <> Zero ->
                    CanonS (Ocons alpha (S n) Zero) i =
                    Ocons alpha n (CanonS (Phi0 alpha) i).
Proof.
  intros; apply E0_eq_intro.
  unfold CanonS;repeat (rewrite cnf_rw || rewrite cnf_Ocons); auto.
  rewrite canonSSn; auto. 
  apply cnf_ok.
  unfold lt.
  unfold Phi0; repeat rewrite cnf_rw. 
  apply canonS_LT.
  apply nf_phi0;auto.
  apply cnf_ok.
  discriminate.
  unfold lt.

  apply LT1.
  apply nf_phi0;auto.
  apply cnf_ok.
Qed. 

Lemma CanonS_Phi0_lim alpha k : Limitb alpha ->
                                CanonS (Phi0 alpha) k =
                                Phi0 (CanonS alpha k). (* to move *)
Proof.
  intro; orefl.
  rewrite phi0_rw.
  unfold CanonS.
  repeat   rewrite cnf_rw.
  rewrite <- canonS_lim1.
  now rewrite phi0_rw.
  apply cnf_ok.
  red in H.
  destruct alpha.   simpl. auto.
Qed.






Lemma CanonS_lt : forall i alpha, alpha <> Zero -> CanonS alpha i < alpha.
Proof.
  destruct alpha. unfold Lt, CanonS. cbn.
  intro;apply canonS_LT; auto.
  intro H0; subst. apply H. unfold Zero;f_equal.
  apply nf_proof_unicity.
Qed.


Lemma Canon_lt : forall i alpha, alpha <> Zero -> Canon alpha i < alpha.
Proof.
  destruct i.
  - unfold Canon;  intros;  destruct alpha.
    unfold Lt, Zero in *; simpl in *. 
    apply T1.not_zero_lt; auto.
    intro; subst cnf; apply H; f_equal;  eapply nf_proof_unicity.
  -   apply CanonS_lt.
Qed.



Lemma Canon_of_limit : forall i alpha, Limitb alpha ->
                                       Canon alpha (S i) <> Zero.
Proof.
  destruct alpha;simpl;unfold CanonS; simpl;  rewrite E0_eq_iff.
  simpl;   apply limitb_canonS_not_zero; auto.
Qed.

Hint Resolve CanonS_lt Canon_lt Canon_of_limit : E0.

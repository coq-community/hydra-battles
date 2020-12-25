
(**  Canonical Sequences of ordinals below epsilon0

Pierre Casteran, 
       LaBRI and University of Bordeaux.

       After J. Ketonen and R. Solovay's paper
  " Rapidly Growing Ramsey Functions" _in_
    Annals of mathematics, Mar. 1981 

 *)

From Coq Require Export Arith Lia.
Import Relations Relation_Operators.

From hydras.Epsilon0 Require Export T1 E0.

Set Implicit Arguments.
Open Scope t1_scope.

(** * Definitions *)

(**  Computes {alpha}(i+1) *)

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

(** * Properties of canonical sequences *)


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
            - f_equal; rewrite <- IHalpha2; f_equal. eapply nf_inv2, H. }
         *  case_eq (T1.succ alpha2).
            { intros;  now destruct (@T1.succ_not_zero alpha2). }
            { intros; f_equal ; rewrite <- IHalpha2.
              - now rewrite <- H0.
              - eapply nf_inv2, H. }
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
  intros; destruct (@zero_limit_succ_dec alpha); trivial.
  - destruct s.
    + destruct n; subst alpha;  reflexivity.       
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

(** ** Canonical sequences and the order LT *)

Lemma canonS_LT i alpha :
  nf alpha -> alpha <> zero ->
  canonS alpha i t1<  alpha.
Proof.
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
             {   destruct  (@zero_limit_succ_dec alpha1) ; trivial. 
                 - destruct s.
                  + subst;  now destruct n0. 
                  + rewrite canonS_lim1.
                    * split.
                      --   apply single_nf; auto.
                 destruct (Hrec alpha1) ; trivial. 
                 apply head_lt_ocons ;  auto.
                 -- split; auto with T1.
                  ++   apply head_lt; apply Hrec ; trivial.
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
                       - assumption.
                     }
                 }
             }
             destruct  (@zero_limit_succ_dec alpha1) ; trivial.
             { destruct s.
               - subst; now destruct n0.   
               - rewrite canonS_lim2.
                 + split.
                  { apply ocons_nf ; trivial.
                    - destruct (Hrec alpha1) ; eauto with T1.
                      + apply head_lt_ocons.
                      + tauto.
                    -  apply single_nf. 
                      destruct (Hrec alpha1); trivial. 
                      apply head_lt_ocons.
                  }
                  split.
                   * apply coeff_lt; auto with arith.
                   * auto with T1.
                     + eapply nf_inv1, Halpha.  
                     + auto.
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
              nf_decomp Halpha.
              apply nf_intro ; trivial.
              - destruct (Hrec  (ocons alpha2_1 n1 alpha2_2)) ; trivial.
               now apply head_lt.
                discriminate.
              - apply nf_helper_phi0R.
                apply T1.lt_trans with (ocons alpha2_1 n1 alpha2_2).
                + destruct (Hrec (ocons alpha2_1 n1 alpha2_2)) ; trivial.
                  apply head_lt; auto. 
                  *  discriminate.
                  * tauto.
             +  
                apply nf_helper_phi0.
                apply nf_helper_intro with n;auto.
            }
            split.
          
            - nf_decomp Halpha.
              apply tail_lt. 
              destruct (Hrec (ocons alpha2_1 n1 alpha2_2)); auto.
              +  auto with T1.
            + discriminate. 
            + destruct (Hrec (ocons alpha2_1 n1 alpha2_2)) ; trivial.
              eauto with T1.
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
  forall beta, beta t1< lambda ->
               {i:nat | beta t1< canonS lambda i}.
Proof.
  transfinite_induction lambda; clear lambda ; intros lambda Hrec Hlambda.
  intros   H beta H1.
  assert (Hbeta: nf beta)  by eauto with T1.
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
          destruct (@zero_limit_succ_dec   lambda1); trivial. 
        -- destruct s.
           ++ subst; assert (False) by (eapply not_LT_zero; eauto).
              contradiction. 
           ++ assert {i :nat | (beta1 t1< canonS lambda1 i)%t1}.         
              { apply Hrec.
                apply head_LT_cons; auto with T1.
                all: auto.
              }
              destruct H3 as [x l].
              exists x; rewrite canonS_lim1; trivial; eauto with T1.
        --  destruct s as [x [H4 H5]].
            subst lambda1; assert ({beta1 t1< x} + {beta1 = x})%t1.
            { apply  LT_succ_LT_eq_dec in H2; trivial. eapply nf_inv1, Hbeta. }
            destruct H3.
            ++ exists 0; rewrite canonS_phi0_succ_eqn;auto with T1.
            ++ subst; exists (S n0);  rewrite canonS_phi0_succ_eqn; auto. 
               apply LT3; auto with arith.
        -- clear i; exists 0; rewrite canonSSn.
           ++ apply LT2; trivial.
              apply nf_intro; trivial.
              now apply nf_canonS.
              apply nf_helper_phi0R.
              apply canonS_lt.
              eapply nf_coeff_irrelevance;eauto. 
              discriminate. 
           ++ eapply nf_inv1, Hlambda. 
        *  subst.
           -- destruct n.
              abstract lia.
              apply lt_n_Sm_le in H3.
              destruct (Compare_dec.le_lt_eq_dec _ _ H3).
              exists 0; rewrite canonSSn. 
             apply LT3; auto.
             {
               apply nf_intro; trivial.
               apply nf_canonS; trivial.
               apply nf_helper_phi0R.
               apply canonS_lt.
               eapply nf_coeff_irrelevance;eauto.     
               discriminate.  
             }
             { eapply nf_inv1, Hlambda. }
             
             assert {i: nat |  beta2 t1< (canonS (ocons lambda1 0 zero) i)}%t1.
             { apply Hrec.
               -- apply LT3;auto with arith.
               -- cbn;  destruct lambda1.
                  destruct H1; auto.
                  auto.
               -- cbn; destruct lambda1.
                  cbn in H; discriminate.
                  auto. 
               --  split.
                   ++ eapply nf_inv2, Hbeta.
                   ++ split. 
                      ** apply nf_helper_phi0.     
                      apply nf_helper_intro with n0;auto with T1.
                      ** eapply nf_coeff_irrelevance;eauto.     
             }
             subst;
               assert
                 ({i: nat |  beta2 t1< (canonS (ocons lambda1 0 zero) i)})%t1.
             { apply Hrec.
               - apply LT3;auto with arith.
               - cbn;  destruct lambda1.
               + destruct H2;auto. 
               + auto.
               - cbn;  destruct lambda1.
                 + destruct H2; auto. 
                 + auto.                
               - split.
                 + eapply nf_inv2, Hbeta. 
                 + split. 
                 * apply nf_helper_phi0.    
                  apply nf_helper_intro with n;auto with T1.
                 * eapply nf_coeff_irrelevance;eauto.   
             }
             destruct H4;  exists x; rewrite canonSSn. 
             apply LT4;auto.
             { 
               apply nf_intro; auto with T1.
               eauto with T1.
               apply nf_helper_phi0R.   
               apply canonS_lt.
               now apply nf_phi0. 
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
         apply nf_canonS; trivial; auto with T1.
         apply limitb_canonS_not_zero; trivial. 
       *  destruct (LT_inv_strong H1).
          -- exists 0;  rewrite canonS_tail.
             apply LT2;auto.
             { apply nf_intro;  trivial.
               eauto with T1.
            apply nf_canonS; trivial; eauto with T1.
            apply nf_helper_phi0R.   
            apply T1.lt_trans with lambda2.
            apply canonS_lt; eauto with T1.
            apply nf_helper_phi0.
            apply nf_helper_intro with n; eauto with T1.
          }
          auto.
          auto.
         --  destruct H4; exists 0; rewrite canonS_tail.
             apply LT3;  auto.
             { apply nf_intro. 
               - eauto with T1.
               - apply nf_canonS; eauto with T1.
               - apply nf_helper_phi0R.   
                 apply T1.lt_trans with lambda2.
                 apply canonS_lt; eauto with T1.
                 apply nf_helper_phi0.
                 apply nf_helper_intro with n; eauto with T1.
             }
             all: auto. 
      --  subst; assert ({i: nat |  beta2 t1< (canonS lambda2 i)})%t1.
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
        apply nf_helper_phi0R.   
        apply T1.lt_trans with lambda2.
        apply canonS_lt; eauto with T1.
        apply nf_helper_phi0.
        apply nf_helper_intro with n; eauto with T1.
      }
      all: auto. 
  -   destruct s as [t [Ht Ht']]; subst lambda.
      destruct (@limitb_succ t); auto. 
Defined.


Lemma canon_limit_strong lambda : 
  nf lambda ->
  limitb lambda  ->
  forall beta, beta t1< lambda ->
                {i:nat | beta t1< canon lambda i}.
Proof.
  intros H H0 beta H1; destruct (canonS_limit_strong H H0 H1) as [x Hx];
    exists (S x);auto.
Defined.


Lemma canonS_limit_lub (lambda : T1) :
  nf lambda -> limitb lambda  ->
  strict_lub (canonS lambda) lambda.
Proof.
  split.
  - intros; split.
    + now  apply nf_canonS.
    +    split; trivial.
         * apply canonS_lt;    auto.
           intro H1;subst; discriminate.
  - intros l' Hl';  assert (nf l').
    {  specialize (Hl' 0). eauto with T1. }
    destruct (T1.lt_eq_lt_dec lambda l').
    + repeat split;auto.
      destruct s.
      *  auto with T1. 
      *  subst; auto with T1. 
    + assert (l' t1< lambda)%t1 by (split; auto).
      destruct (canonS_limit_strong   H H0 H2).
      specialize (Hl' x).
      assert (l' t1< l')%t1.
      { apply LT_LE_trans with  (canonS lambda x); auto. }
      now destruct (@LT_irrefl l' ).
Qed. 


Lemma canonS_limit_mono alpha i j : nf alpha -> limitb alpha  ->
                                    i < j ->
                                    canonS alpha i t1< canonS alpha j.
Proof. 
  pattern alpha ; apply transfinite_recursor_lt.
  clear alpha;  intros alpha Hrec alpha_nf.
  intros.  
  destruct alpha.
  - discriminate.
  -  nf_decomp alpha_nf.
     destruct (limitb_cases alpha_nf H).
     +  destruct a;subst.
        destruct (@zero_limit_succ_dec alpha1) ; trivial.
        *   destruct s.   
            { subst;   discriminate H. }
            {   destruct n.
                - repeat rewrite canonS_lim1 ; trivial.
                  {  apply LT2 ; trivial.
                     apply single_nf. 
                     apply nf_canonS ; eauto with T1.
                     apply single_nf. 
                     apply nf_canonS ; eauto with T1.
                     apply Hrec ; trivial. 
                     apply head_lt_ocons.
                  }
                - repeat rewrite canonS_lim2 ; trivial. 
                  {
                    apply LT4 ; trivial.
                    apply nf_ocons_LT ; trivial.
                    apply canonS_LT ; trivial.
                    apply single_nf. 
                    apply nf_canonS ; trivial.
                    apply nf_ocons_LT; trivial.
                    apply canonS_LT ; eauto with T1.
                    apply single_nf; apply nf_canonS ; eauto with T1.
                    apply LT2 ; trivial.
                    apply single_nf;
                      apply nf_canonS ; eauto with T1.
                    apply single_nf;
                      apply nf_canonS ; eauto with T1.
                    apply Hrec ; trivial.
                    apply head_lt_ocons.
                  }
            }
        * destruct s;subst.
          destruct a.
          subst alpha1.
          destruct n.
          { repeat rewrite canonS_phi0_succ_eqn ; eauto with T1. }
          {
            repeat rewrite canonS_ocons_succ_eqn2 ; trivial. 
            apply LT4 ; trivial.
            apply nf_ocons_LT ; eauto with T1.
            apply LT_succ ; eauto with T1.
            apply nf_ocons_LT ; eauto with T1.
            apply LT_succ ; eauto with T1.
            auto with T1.
          }
     + destruct a.
       repeat rewrite canonS_tail ; eauto with T1.
       nf_decomp alpha_nf.
       * apply  LT4 ; trivial.
         apply nf_intro ; trivial. 
         apply nf_canonS ; eauto with T1.
         apply nf_helper_phi0R ; trivial. 
         apply T1.lt_trans with alpha2 ; trivial. 
         apply canonS_lt ; eauto with T1.
         apply nf_helper_phi0 ; eauto with T1.
         apply nf_helper_intro with n ; eauto with T1.
         apply nf_intro ; trivial. 
         apply nf_canonS ; eauto with T1.
         apply nf_helper_phi0R ; trivial. 
         apply T1.lt_trans with alpha2; trivial. 
         apply canonS_lt ; eauto with T1.
         apply nf_helper_phi0 ; eauto with T1.
         apply nf_helper_intro with n ; eauto with T1.
         apply Hrec ; eauto with T1.
         apply tail_lt_ocons ; eauto with T1.
Qed.


Lemma canonS_LE alpha n :
    nf alpha ->  canonS alpha n t1<= canonS alpha (S n).
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

  (** exercise  after Guillaume Melquiond   *)
  
  Require Import Fuel. 

Fixpoint  approx alpha beta fuel i :=
  match fuel with
          FO => None
        | Fuel.FS f =>
          let gamma := canonS alpha i in
          if lt_b beta gamma
          then Some (i,gamma)
          else approx alpha beta  (f tt) (S i)
        end.


Lemma approx_ok alpha beta :
  forall fuel i j gamma, approx alpha beta fuel i = Some (j,gamma) ->
                         gamma = canonS alpha j /\ lt_b beta gamma.
Proof.
  induction fuel as [| f IHfuel ].
  - cbn; discriminate. 
  - intros i j gamma H0;  cbn in H0.
    case_eq (lt_b beta (canonS alpha i));intro H1; rewrite H1 in *.
    + injection H0; intros; subst; split;auto.
    + now specialize (IHfuel tt (S i) _ _ H0).
Qed.




  
  (** ** Adaptation to E0 (well formed terms of type [T1] ) *)
  

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
  intros; apply E0_eq_intro;
  unfold CanonS;repeat (rewrite cnf_rw || rewrite cnf_Ocons); auto.
  - rewrite canonSSn; auto with E0.
  -  unfold lt, Phi0; repeat rewrite cnf_rw. 
     apply canonS_LT ; trivial. 
     apply nf_phi0;auto with E0. 
     discriminate.
   -  unfold lt; eauto with E0.
      apply LT1; apply nf_phi0;auto with E0.
Qed. 

Lemma CanonS_Phi0_lim alpha k : Limitb alpha ->
                                CanonS (Phi0 alpha) k =
                                Phi0 (CanonS alpha k). 
Proof.
  intro; orefl; rewrite phi0_rw.
  unfold CanonS; repeat   rewrite cnf_rw;  rewrite <- canonS_lim1.
  -  now rewrite phi0_rw.
  - apply cnf_ok.
  - destruct alpha; cbn; assumption. 
Qed.


Lemma CanonS_lt : forall i alpha, alpha <> Zero -> CanonS alpha i o< alpha.
Proof.
  destruct alpha. unfold Lt, CanonS. cbn.
  intro;apply canonS_LT; auto.
  intro H0; subst. apply H. unfold Zero;f_equal.
  apply nf_proof_unicity.
Qed.


Lemma Canon_lt : forall i alpha, alpha <> Zero -> Canon alpha i o< alpha.
Proof.
  destruct i.
  - unfold Canon;  intros;  destruct alpha.
    unfold Lt, Zero in *; simpl in *. 
    apply T1.not_zero_lt; auto.
    intro; subst cnf; apply H; f_equal;  eapply nf_proof_unicity.
  -   apply CanonS_lt.
Qed.

Lemma Canon_of_limit_not_null : forall i alpha, Limitb alpha ->
                                       Canon alpha (S i) <> Zero.
Proof.
  destruct alpha;simpl;unfold CanonS; simpl;  rewrite E0_eq_iff.
  simpl;   apply limitb_canonS_not_zero; auto.
Qed.

Hint Resolve CanonS_lt Canon_lt Canon_of_limit_not_null : E0.



(**  Injection from the set of  ordinal terms in Cantor normal form
  into the set of Schutte's countable ordinal numbers stricly less than
  epsilon0.

  Pierre Castéran, Univ. Bordeuwx and LaBRI

   This is intented to be a validation of main constructions and functions 
   designed for the type [T1].

*)

(*  Pierre Casteran 
    LaBRI, Université Bordeaux 1
*)



From hydras Require Import Epsilon0.Epsilon0 ON_Generic. 
From hydras Require Import Schutte_basics  Schutte.Addition  AP CNF.

Import List  PartialFun Ensembles.

Fixpoint inject (t:T1) : Ord :=
 match t with T1.zero => zero
         | T1.ocons a n b =>
           AP._phi0 (inject a) * S n + inject b
 end.


Lemma inject_of_finite_pos : forall n, inject (T1.fin (S n)) = F (S n).
Proof.
 induction n;simpl.
 -  rewrite phi0_zero.
    rewrite alpha_plus_zero; auto with schutte.
 - clear IHn.  induction n; simpl ; auto.
    + repeat rewrite phi0_zero.
      rewrite alpha_plus_zero; auto with schutte.
      * rewrite <- succ_is_plus_1.
             f_equal. 
    + rewrite alpha_plus_zero. 
     *  rewrite alpha_plus_zero in IHn.
        rewrite IHn. 
        replace (AP._phi0 zero) with (F 1).
        rewrite <- succ_is_plus_1; auto with schutte.
        symmetry; auto with schutte. 
        apply phi0_zero. 
Qed.




Theorem inject_of_zero : inject T1.zero = zero.
Proof. reflexivity. Qed.


Theorem inject_of_finite (n : nat):
  inject (T1.fin n) =  n.
Proof.
  destruct n.
  - apply inject_of_zero.
  - apply inject_of_finite_pos.
Qed.


Theorem inject_of_omega : inject omega%t1 = Schutte_basics._omega.
Proof.
 simpl.
 repeat rewrite alpha_plus_zero.
 rewrite phi0_zero;  generalize omega_second_AP; destruct 1.
 red in H; unfold Ensembles.In in H0; now rewrite omega_eqn.
Qed.

Theorem inject_of_phi0 (alpha : T1):
  inject (phi0 alpha) = AP._phi0 (inject alpha).
Proof.
  simpl; now rewrite alpha_plus_zero.
Qed.

(* begin hide *)

Lemma phi0_mult_lt_phi0 (alpha beta : Ord) :
    alpha < beta ->
    forall n,  (AP._phi0 alpha) * S n  < AP._phi0 beta.
Proof.
  induction n;simpl;auto.
  -  apply phi0_mono;auto.
  -  apply AP_plus_closed; trivial.
    + apply AP_phi0.
    + apply phi0_mono;auto.
Qed.

Lemma phi0_mult_plus_lt_phi0 alpha beta n gamma :
  alpha < gamma -> beta < AP._phi0 gamma ->
  mult_Sn (AP._phi0 alpha) n  + beta < AP._phi0 gamma.
Proof.
  intros;apply AP_plus_closed ; auto with schutte.
  -  apply AP_phi0.
  -  apply  phi0_mult_lt_phi0;auto.
Qed.

Lemma phi0_mult_plus_lt_phi0R alpha beta n gamma :
  mult_Sn (AP._phi0 alpha) n  + beta < AP._phi0 gamma ->
  alpha < gamma /\ beta < AP._phi0 gamma.
Proof.
  split.
  - assert (H0 : AP._phi0 alpha < AP._phi0 gamma).
    {  eapply le_lt_trans.
       2:eexact H.
       apply le_trans with  (mult_Sn (AP._phi0 alpha) n).
       clear H; induction n.
       simpl;auto with schutte.
       simpl;   apply le_plus_r.
       apply le_plus_l;auto with schutte.
    }
    apply phi0_mono_R;auto.
   -   eapply le_lt_trans.
       2:eexact H.
       apply le_plus_r;auto with schutte.
Qed.

 
Lemma zero_lt alpha n beta : 
  zero < mult_Sn (AP._phi0 alpha) n + beta.
Proof.
 apply lt_le_trans with (AP._phi0 alpha).
 -  apply phi0_positive;auto.
 - apply le_trans with ( mult_Sn (AP._phi0 alpha) n).
  induction n; simpl; auto with schutte.
  +  apply le_plus_r;auto.
  +  apply  le_plus_l;auto with schutte.
Qed.
 

Lemma head_lt :  forall a a' n n' b b',
    a  < a' -> b < AP._phi0 a'  ->
    mult_Sn (AP._phi0 a) n + b < mult_Sn (AP._phi0 a') n' + b'.
Proof.
 intros.
 apply lt_le_trans with (AP._phi0 a').
 - apply phi0_mult_plus_lt_phi0;auto.
 -  apply le_trans with (mult_Sn (AP._phi0 a') n').
  + induction n';simpl;auto.
   *  left; auto.
   *  apply le_plus_r;auto with schutte.
  +  apply le_plus_l;auto with schutte.
Qed.


Lemma coeff_lt : forall a  n n' b b',
    b < AP._phi0 a  ->(n < n')%nat ->
    mult_Sn (AP._phi0 a) n + b < mult_Sn (AP._phi0 a) n' + b'.
Proof.
 intros;  apply lt_le_trans with (mult_Sn (AP._phi0 a) n').
 -  apply lt_le_trans with (mult_Sn (AP._phi0 a) n + AP._phi0 a).
   +  apply plus_mono_r; auto.
   +  apply mult_Sn_mono3; auto.
     *  apply  phi0_positive; auto. 
 - apply le_plus_l. 
Qed. 

Lemma inject_mono_0 : forall alpha,
    T1.nf alpha ->
    forall beta gamma, 
      T1.lt  beta gamma -> 
      T1.lt gamma alpha ->
      T1.nf beta -> T1.nf gamma ->
      (inject beta < inject gamma)%sch.
Proof with eauto with T1.
  intros alpha;  T1.transfinite_induction alpha.
  intros x Indx Nx;  induction beta; destruct gamma.
  {  intros H H0;  T1.T1_inversion H. }
  { intros H H0 H1 H2;  simpl; 
      apply lt_le_trans with (AP._phi0 (inject gamma1))%sch.
    -  apply phi0_positive;auto with schutte.
    - eapply le_trans. 
      2:eapply le_plus_l; auto with schutte.
      apply le_a_mult_Sn_a; auto with schutte.
  }
  intros H H0 H1 H2;  T1.T1_inversion H.
  intros H H0 H1 H2; simpl;  destruct (T1.lt_inv H).
  -   apply head_lt.    
      +  eapply IHbeta1 ...

         * apply T1.lt_trans with  (T1.ocons gamma1 n0 gamma2) ...
           apply T1.head_lt_ocons; auto.
      +  apply lt_trans with (inject (phi0 beta1)). 
         *   eapply IHbeta2 ...
             apply T1.nf_helper_phi0.
             apply T1.nf_helper_intro with n; auto. 
             apply  T1.le_lt_trans with (T1.ocons beta1 n beta2); auto with T1.
             apply T1.le_phi0 ; eauto with T1.
             eapply T1.lt_trans ...
         * simpl; rewrite alpha_plus_zero.
           apply phi0_mono,  IHbeta1; auto. 
           apply T1.lt_trans with (T1.ocons gamma1 n0 gamma2) ...
           apply T1.head_lt_ocons ...
           eauto with T1.
           eauto with T1.
  -     decompose [or and] H3.
        subst;  apply coeff_lt. 
        + replace  (AP._phi0 (inject gamma1)) with (inject (phi0 gamma1)).
          *  apply IHbeta2.
             apply T1.nf_helper_phi0.
             eapply T1.nf_helper_intro; eauto.
             apply T1.le_lt_trans with (T1.ocons gamma1 n0 gamma2); auto. 
             destruct n0.
             apply T1.le_tail ...
             apply T1.lt_le_incl.
             apply T1.coeff_lt; auto with arith.
             eauto with T1.
             eapply T1.nf_phi0; eauto with T1.
          * cbn; rewrite alpha_plus_zero ...
        +  auto.
        +  subst; apply plus_mono_r.
           apply IHbeta2; eauto with schutte T1.
           eapply T1.lt_trans.
           2: eapply H0.
           auto with T1.
           apply T1.tail_lt_ocons; auto.
Qed. 

(* end hide *)

Theorem inject_mono (beta gamma : T1) :
  T1.lt  beta gamma -> 
  T1.nf beta -> T1.nf gamma -> 
  inject beta < inject gamma.
Proof.  
  intros H H0 H1; apply inject_mono_0 with (T1.succ gamma);auto.
  -  apply T1.succ_nf;auto.
  -  apply T1.lt_succ;auto.
Qed.

Theorem inject_injective (beta gamma : T1) : nf beta -> nf gamma ->
                                             inject beta = inject gamma -> beta = gamma.
Proof.
  intros H H0 H1. 
  destruct (LT_eq_LT_dec H H0) as [[H2 | H2] | H2]; auto.
  destruct H2 as [H3 [H4 H5]].   apply inject_mono in H4; auto.    
  rewrite H1 in H4; auto.
  destruct (lt_irr H4); auto.
  destruct H2 as [H3 [H4 H5]].   apply inject_mono in H4; auto.    
  rewrite H1 in H4; auto.
  destruct (lt_irr H4); auto.
Qed.

Theorem inject_monoR (beta gamma : T1) : 
  T1.nf beta -> T1.nf gamma -> 
  inject beta < inject gamma -> 
  (beta  t1< gamma)%t1.
Proof.  
  intros H H0 H1; 
  destruct (T1.lt_eq_lt_dec beta gamma) as [[H2 | H2] | H2].
  -  now split.  
  -  subst ;  case (lt_irr  H1).
  -  destruct (@lt_irr (inject beta)).
     eapply lt_trans with (inject gamma); auto.
     now apply inject_mono.
Qed.


Theorem inject_lt_epsilon0 (alpha : T1):
  inject alpha < epsilon0.
Proof.
  assert (Ap := epsilon0_AP); induction alpha; simpl.
  - rewrite <- epsilon0_fxp; apply phi0_positive.
  - apply AP_plus_closed; auto.
    apply AP_mult_Sn_closed; auto.
    now apply phi0_lt_epsilon0.
Qed.

(* begin hide *)




Section Equations_for_addition.

  Lemma plus_alpha_mult_phi0 (alpha beta : Ord)  (H: alpha < AP._phi0 beta)
        (n : nat) : alpha + mult_Sn (AP._phi0 beta) n = mult_Sn (AP._phi0 beta) n.
  Proof.
    induction n.
    - simpl;    destruct (AP_phi0 beta ) as [ _ H1];   apply  (H1 _ H).  
    - simpl;  rewrite plus_assoc; now rewrite IHn.
  Qed.

  Lemma mult_Sn_dist (alpha : Ord) (n p : nat) :
    mult_Sn alpha (S (n + p)) = mult_Sn alpha p + mult_Sn alpha n.
  Proof.
    induction n; simpl.
    - reflexivity. 
    - rewrite  plus_assoc;  f_equal.
      now   rewrite <- IHn.
  Qed. 



  (*

  Quoted from Epsilon0.T1

  Fixpoint plus (alpha beta : T1) :T1 :=
  match alpha,beta with
  |  zero, y  => y
 |  x, zero  => x
 |  ocons a n b, ocons c p d =>
    (match compare a c with
     | Lt => ocons c p d
     | Gt => (ocons a n (plus b (ocons c p d)))
     | Eq  => (ocons a (S (n+p)) d)
     end)
  end
where "alpha + beta" := (plus alpha beta) : t1_scope.
   *)

  

  Variables (a b c d : Ord) (n p : nat).

  Hypotheses (Hnfa : b < AP._phi0 a)
             (Hnfc : d < AP._phi0 c).
  Let alpha := mult_Sn  (AP._phi0 a) n + b.
  Let beta := mult_Sn  (AP._phi0 c) p + d.
  Section case1.
    Hypothesis Hac: a < c.


    Lemma case_lt : alpha + beta = beta.
    Proof.
      unfold alpha, beta.
      rewrite <-
              (plus_assoc (mult_Sn (AP._phi0 a) n)
                          b
                          (mult_Sn (AP._phi0 c) p + d)).
      assert (b < AP._phi0 c).
      { apply lt_trans with (AP._phi0 a); auto with schutte.
        now apply phi0_mono.
      }   
      rewrite (plus_assoc b (mult_Sn (AP._phi0 c) p) d).
      rewrite (plus_alpha_mult_phi0 _ _ H p).
      rewrite  plus_assoc .
      rewrite plus_alpha_mult_phi0.
      auto.
      apply AP_mult_Sn_closed.
      apply AP_phi0.
      now apply phi0_mono.
    Qed.

    
  End case1.

  Section case2.
    Hypothesis Hac : c < a.

    Lemma case_gt : alpha + beta = mult_Sn (AP._phi0 a) n +
                                   (b + beta). 
    Proof. 
      unfold alpha;  now  rewrite plus_assoc.
    Qed.

  End case2.

  Section case3.

    Hypothesis Hac : a = c.

    Lemma case_Eq : alpha + beta = mult_Sn (AP._phi0 a) (S (n + p)) + d.
    Proof.
      unfold alpha, beta; subst c; rewrite <- plus_assoc.
      rewrite (plus_assoc b (mult_Sn (AP._phi0 a) p) d).
      rewrite (plus_alpha_mult_phi0 _ _ Hnfa).
      rewrite plus_assoc;  f_equal.
      rewrite Nat.add_comm; now  rewrite mult_Sn_dist.
    Qed.

  End case3.

End Equations_for_addition.


(* end hide *)

Lemma inject_rw (a b: T1) n : inject (ocons a n b) =
                              mult_Sn (AP._phi0 (inject a)) n + inject b.
Proof. reflexivity. Qed.

Theorem inject_plus (alpha beta : T1): nf alpha -> nf beta ->
                                       inject (alpha + beta)%t1 = inject alpha + inject beta.
Proof with eauto with T1.
  induction alpha.
  - simpl;  now rewrite zero_plus_alpha.
  -  intros H H0;  destruct beta.
     + simpl (inject (ocons alpha1 n alpha2));
         rewrite <- plus_assoc; simpl (inject T1.zero); 
           now rewrite alpha_plus_zero.
     +  repeat rewrite inject_rw;  case_eq (T1.compare alpha1 beta1).
        * intro H1;  apply T1.compare_Eq_impl in H1; subst beta1.
          repeat rewrite inject_rw;  simpl T1.plus; rewrite T1.compare_refl.
          repeat rewrite inject_rw.
          rewrite <- (case_Eq (inject alpha1) (inject alpha2)
                              (inject alpha1) (inject  beta2) n n0) ...
          assert (H1 : (alpha2 t1< phi0  alpha1)%t1). {
            rewrite nf_LT_iff in H;  tauto. }
          rewrite <- inject_of_phi0.
          apply inject_mono ...
          rewrite <- inject_of_phi0; apply inject_mono ...
          rewrite nf_LT_iff in H0 ...
          decompose [and] H0 ... 
        * intros H1; repeat rewrite inject_rw.
          simpl T1.plus; rewrite H1;  rewrite lt_iff in H1.
          { repeat rewrite inject_rw; rewrite case_lt; auto.
            rewrite <- inject_of_phi0;  apply inject_mono ...
            -  rewrite nf_LT_iff in H; decompose [and] H ...
            -  apply inject_mono; eauto with T1.
          }  
        * intros H1; repeat rewrite inject_rw.
          simpl T1.plus; rewrite H1; rewrite gt_iff in H1.
          repeat rewrite inject_rw; rewrite case_gt.
          f_equal; rewrite IHalpha2 ...
Qed.





Theorem inject_mult_fin_r (alpha : T1)  :
  nf alpha -> forall n:nat , inject (alpha *  n)%t1 =  inject alpha * n.
Proof.
  induction n.
  - simpl.
    destruct alpha; simpl; auto.
    destruct alpha1; simpl; auto.
  -  destruct n.
     +  simpl (inject alpha * 1).
        simpl (alpha * 1)%t1.
        destruct alpha; auto.
        destruct alpha1.
        *   f_equal;  destruct n; simpl; auto.
            assert (alpha2 = T1.zero).  
            {  eapply nf_of_finite; eauto. }
            -- now subst.
            --  assert (alpha2 = T1.zero).  
                { eapply nf_of_finite; eauto. }
                subst;  f_equal;   auto with arith.
        *  replace (n * 1)%nat with n; auto with arith.
     +   change ((S (S n)):T1) with  (FS (S n)); rewrite mult_Sn_add.
         replace (S (S n)) with (S (S (n + 0)))%nat.
         simpl mult_fin_r;  rewrite inject_plus; auto with arith.
         *  replace (alpha * (FS n))%t1 with (alpha * (S n))%t1.
            --  rewrite IHn;  replace (n+0)%nat with n.
                reflexivity.
                auto with arith.
            -- reflexivity.
         * 
           { 
             clear IHn; induction n; simpl.
             destruct alpha;  auto.
             destruct alpha1.
             apply nf_FS.
             replace (n * 1)%nat with n; auto with arith.
             destruct alpha; auto with T1.
             destruct alpha1.
             apply nf_FS.
             eapply nf_coeff_irrelevance. eauto. 
           }
         *   auto with arith.
         * auto.
Qed. 



Lemma inject_lt_epsilon0_ex_cnf  (alpha : Ord) :
  forall (H  : alpha < epsilon0)
         (l: list Ord),  is_cnf_of alpha l ->
                         exists t: T1,  nf t /\ inject t = eval l.
Proof.
  pattern alpha; apply well_founded_induction with (R:=lt).
  { exact all_ord_acc. }
  { clear alpha; intros alpha IHalpha H. 
    destruct l.
    -  exists T1.zero;  simpl;   unfold nf; split; auto.
    - inversion_clear   1.
      pose (H3 := IHalpha o).
      assert (H0 : o < alpha).
      { simpl in H2; 
          subst alpha; apply lt_le_trans with (AP._phi0 o).
        - apply lt_phi0; apply le_lt_trans with (AP._phi0 o).
          + apply le_phi0.
          +  apply le_lt_trans with (2:= H); apply le_plus_l.
        -   apply le_plus_l.
      }
      assert (H4 : o < epsilon0).
      { apply lt_trans with alpha; auto. }
      specialize (H3 H0 H4);  destruct (cnf_exists o) as [x H5].
      specialize (IHalpha (eval l)).
      assert (H6 : eval l < alpha). {
        simpl in H2;   subst alpha;   apply sorted_lt;  auto. }
      assert (H7 : eval l < epsilon0).
      { apply lt_trans with alpha; auto. }
      destruct (H3 _ H5) as [x0 H8].
      destruct H8 as [H8 H9]; specialize  (IHalpha H6 H7).
      + destruct (IHalpha l).
        * split; trivial.
          eapply sorted_tail; eauto.
        *   destruct H10 as [H10 H11];  exists (phi0 x0 + x1)%t1.
            split.    
            -- apply plus_nf ; eauto with T1.
            -- simpl eval;  rewrite <- H11;  rewrite inject_plus; auto with T1.
               simpl (inject (phi0 x0)); rewrite H9;  destruct H5.
               rewrite <- H12;  rewrite alpha_plus_zero; auto.
  }
Qed.


Theorem inject_lt_epsilon0_ex  (alpha : Ord) (H  : alpha < epsilon0) :
  exists t: T1,  nf t /\ inject t = alpha.
Proof.
  destruct (cnf_exists alpha) as [l Hl].
  destruct (inject_lt_epsilon0_ex_cnf alpha H l Hl) as [t [H1 H2]].
  exists t; split ; [trivial | ].
  destruct Hl; congruence.
Qed.


Theorem inject_lt_epsilon0_ex_unique  (alpha : Ord) (H : alpha < epsilon0) :
  exists! t: T1,  nf t /\ inject t =  alpha.
Proof.
  destruct (inject_lt_epsilon0_ex alpha H ) as [t [H0 H1]].
  exists t; split.
  - now split.
  - intros t' [H2 H3].
    rewrite <- H3 in H1;  now apply inject_injective.
Qed.

Theorem embedding : fun_bijection (nf: Ensemble T1)  (members epsilon0) inject.
Proof.
  split.
  -   intros x Hx; apply inject_lt_epsilon0.
  -  intros y Hy; destruct (inject_lt_epsilon0_ex y Hy) as [x [Hx Hx1]];
       exists x; auto.
  -  intros x x' Hx Hx' H; apply inject_injective; auto.
Qed.


Instance Epsilon0_correct :
  ON_correct epsilon0 Epsilon0  (fun alpha => inject (cnf alpha)).
Proof.
  split.
  - intro a; apply embedding; red; apply cnf_ok.
  - intros; destruct (inject_lt_epsilon0_ex_unique _ H) as [x [[H0 H1] H2]].
    exists (mkord H0);now cbn.
  - intros a b; destruct (compare_correct a b).
   + now subst.
   + apply inject_mono;destruct H; tauto.
   + apply inject_mono;  destruct H; tauto.
Qed.

(** Correctness of E0.plus *)

Theorem  E0_plus_correct :  ON_op_ok  E0.plus plus.
Proof.
  red; destruct x,y; cbn.
  rewrite inject_plus; auto.
Qed.


(* Pierre Castéran, LaBRI and University of Bordeaux  *)

Require Import Hydra_Lemmas Epsilon0 Canon Paths Relation_Operators.
Require Import O2H.

(** 
 *)

Open Scope t1_scope.

(** **  Bounded variants *)

Class BoundedVariant (B:Battle) :=
  {
  mu:T1 ;
  m: Hydra -> T1;
  mu_nf: nf mu;
  Hvar: Hvariant T1_wf B m;
  m_bounded: forall h, m h o< mu
  }.




Section Bounded.
  
  Context (B: Battle)
          (Hy : BoundedVariant B ).

  Hypothesis m_decrease : forall  i h h',
      round_n i h h'   -> m h' o< m h.

  Lemma  nf_m : forall h, nf (m h).
  Proof.
    intro h0; now destruct (m_bounded h0).
  Qed.

  Hint Resolve Rem0 : hydra.
  


  
  Lemma mu_positive : mu <> T1.zero.
  Proof. 
    intro H; subst;  specialize (m_bounded (hyd1 head)).
    rewrite H.
    intro H0;  destruct (not_LT_zero H0). 
  Qed.


  Lemma m_ge_0 alpha:  nf alpha -> alpha o<= m (iota alpha).
  Proof.
    transfinite_induction_lt alpha; 
      clear alpha; intros alpha Hrec H.
    destruct (T1_eq_dec alpha T1.zero).
    + subst;  repeat split; auto with T1.
      now apply nf_m . 
    +   destruct (T1.zero_limit_succ_dec H).
        * destruct s.
          { subst ; now destruct n. }
          { eapply strict_lub_lub with (s := fun i => canonS alpha i).
            apply canonS_limit_lub; auto. 
            intro i0.   assert (round_n i0 (iota alpha) (iota (canonS alpha i0))). 
            {   apply canonS_iota_i;  auto. }
            apply LE_trans with (m (iota (canonS alpha i0))); auto.
            { apply Hrec; auto. 
              - apply nf_canonS;  auto.
              - destruct (canonS_limit_lub H); auto. 
                destruct (H1 i0);   tauto.
              - eapply nf_canonS;auto.
            }  
            apply LE_r; eapply m_decrease; eapply  H0.
          }
        *  destruct s as [x [H0 e]]; subst.
           assert (x o< m (iota (T1.succ x))).
           { 
             apply LE_LT_trans with (m (iota x)).
             apply Hrec; auto. 
             apply lt_succ; auto.
             eapply m_decrease.
             clear Hrec; destruct x.
             - left;  apply iota_succ_R1; eauto.
             - left;  apply iota_succ_R1; eauto.
           }
           now  apply LT_succ_LE.
           Unshelve.
           exact 0.
  Qed.

  Definition big_h := iota mu.
  Definition beta_h := m big_h.
  Definition small_h := iota beta_h.

  
  

  Lemma mu_beta_h : acc_from mu beta_h.
  Proof.
    apply LT_acc_from,  m_bounded. 
  Qed.

  
  
  
  Corollary m_ge_generic : m big_h o<= m small_h.
  Proof.      
    apply m_ge_0, nf_m.
  Qed.

End Bounded.


Arguments big_h {B Hy}.
Arguments small_h {B Hy}. 
Arguments beta_h {B Hy}.

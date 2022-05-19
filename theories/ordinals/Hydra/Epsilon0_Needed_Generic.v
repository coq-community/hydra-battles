
(**  Pierre Castéran, LaBRI and University of Bordeaux  *)

(** Technical definitions and lemmas about variants bounded by some ordinal 
    les than [epsilon0] 
 *)


From hydras Require Import Hydra_Lemmas Epsilon0 Canon Paths O2H.
From Coq Require Import Relation_Operators.

Open Scope t1_scope.

(* begin snippet theContext:: no-out *)
Section Bounded.
  
  Context (B: Battle)
          (mu: T1)
          (Hmu: nf mu)
          (m : Hydra -> T1)
          (Var : Hvariant  T1_wf B m)
          (Hy : BoundedVariant  Var mu).

  Hypothesis m_decrease : forall  i h h', round_n i h h'-> m h' t1< m h.
  (* end snippet theContext *)
  
  Lemma  nf_m : forall h, nf (m h).
  Proof. intro h0; now destruct (m_bounded h0). Qed.

  #[local] Hint Resolve Rem0 : hydra.
  


  
  Lemma mu_positive : mu <> T1.zero.
  Proof. 
    intro H; subst;  specialize (m_bounded (hyd1 head)).
    intro H0;  destruct (not_LT_zero H0). 
  Qed.

  (* begin snippet mGe0:: no-out *)
  Lemma m_ge_0 alpha:  nf alpha -> alpha t1<= m (iota alpha). 
  (* end snippet mGe0 *)
 Proof.
    transfinite_induction_lt alpha; 
      clear alpha; intros alpha Hrec H.
    destruct (T1_eq_dec alpha T1.zero).
    + subst;  repeat split; auto with T1.
      now apply nf_m . 
    +   destruct (T1.zero_limit_succ_dec H).
        * destruct s.
          { subst ; now destruct n. }
          { eapply strict_lub_lub with (s := fun i => canon alpha (S i)).
            apply canonS_limit_lub; auto. 
            intro i0;
              assert (round_n i0 (iota alpha) (iota (canon alpha (S i0)))). 
            {   apply canonS_iota_i;  auto. }
            apply LE_trans with (m (iota (canon alpha (S i0)))); auto.
            { apply Hrec; auto. 
              - apply nf_canon;  auto.
              - destruct (canonS_limit_lub H); auto. 
                destruct (H1 i0);   tauto.
              - eapply nf_canon;auto.
            }  
            apply LE_r; eapply m_decrease; eapply  H0.
          }
        *  destruct s as [x [H0 e]]; subst.
           assert (x t1< m (iota (T1.succ x))).
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
 
 

 (* begin snippet mGeGeneric:: no-out  *)
 Definition big_h := iota mu.
 Definition beta_h := m big_h.
 Definition small_h := iota beta_h.

 Lemma mu_beta_h : acc_from mu beta_h.
 Proof. apply LT_acc_from, m_bounded.  Qed.
 
 Corollary m_ge_generic : m big_h t1<= m small_h.
 Proof. apply m_ge_0, nf_m. Qed.

End Bounded.
(* end snippet mGeGeneric *)




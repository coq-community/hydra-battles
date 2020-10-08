(** * A hierarchy of rapidly growing functions
    After Wainer, Ketonen, Solovay, etc .

    Pierre Casteran, LaBRI, University of  Bordeaux *)

From hydras.Prelude  Require Import  Iterates  Simple_LexProd Exp2.
From hydras.Epsilon0 Require Import  E0 Canon Paths.
Import RelationClasses Relations.

From Coq Require Import ArithRing Lia.

From Equations Require Import Equations.


(** ** The Wainer hierarchy 

*)



Instance Olt : WellFounded Lt := E0.Lt_wf.

Fail Equations F_ (alpha: E0) (i:nat) :  nat  by wf  alpha Lt :=
  F_ alpha  i with E0_eq_dec alpha Zero :=
    { | left _ =>  i ;
      | right nonzero
          with Utils.dec (Limitb alpha) :=
          { | left _ =>  F_ (Canon alpha i)  i ;
            | right notlimit =>  iterate (F_ (Pred alpha))  (S i) i}}.

Definition call_lt (c c' : E0 * nat) :=
  lexico Lt (Peano.lt) c c'.

Lemma call_lt_wf : well_founded call_lt.
  unfold call_lt; apply Inverse_Image.wf_inverse_image,  wf_lexico.
  -  apply E0.Lt_wf.
  -  unfold Peano.lt; apply Nat.lt_wf_0. 
Qed.

Instance WF : WellFounded call_lt := call_lt_wf.


(** 

   [F_star (alpha,i)] is intended to be the i-th iterate of [F_ alpha].
 
   It is easy to define [F_star] using the [coq-equations] plug-in  *)

Equations  F_star (c: E0 * nat) (i:nat) :  nat by wf  c call_lt :=
  F_star (alpha, 0) i := i;
  F_star (alpha, 1) i
    with E0_eq_dec alpha Zero :=
    { | left _ => S i ;
      | right nonzero
          with Utils.dec (Limitb alpha) :=
          { | left _ => F_star (Canon alpha i,1) i ;
            | right notlimit =>
              F_star (Pred alpha, S i)  i}};
  F_star (alpha,(S (S n))) i :=
    F_star (alpha, 1) (F_star (alpha, (S n)) i).

Next Obligation.
  left; cbn ; auto with E0. 
Defined.

Next Obligation.
  left; cbn; auto with E0.   
Defined.

Next Obligation.
  right; cbn; auto with arith. 
Defined.

Next Obligation.
  right; cbn; auto with arith.
Defined.


(**  Finally, [F_ alpha] is defined as its first iterate  ! *)

Definition F_  alpha i := F_star (alpha, 1) i.

(** We get the "usual" equations for F *)

Lemma F_zero_eqn : forall i, F_ Zero i = S i.
Proof.
  intro i. unfold F_; rewrite F_star_equation_2.
  destruct (E0_eq_dec Zero Zero).
  - now cbn.
  - now destruct n.
Qed.

About F_zero_eqn.


Print Assumptions F_zero_eqn. 


Lemma F_star_zero_eqn : forall alpha i, F_star (alpha, 0) i = i.
Proof.
  intros; now rewrite F_star_equation_1.
Qed.

Lemma Fstar_S : forall alpha n i, F_star (alpha ,S (S n)) i =
                                  F_ alpha  (F_star (alpha, S n) i).
Proof.  
  unfold F_; intros; now rewrite F_star_equation_3.
Qed.

Lemma F_eq2 : forall alpha i,
    Succb alpha -> 
    F_ alpha i = F_star (Pred alpha, S i) i.
Proof.
  unfold F_; intros; rewrite F_star_equation_2.
  destruct (E0_eq_dec alpha Zero).
  - subst alpha; discriminate H.
  - cbn; destruct (Utils.dec (Limitb alpha)) .
    + assert (true=false) by 
       ( now  destruct (Succ_not_Limitb _ H)). 
      discriminate.
    + now cbn.
Qed.

Lemma F_lim_eqn : forall alpha i,  Limitb alpha ->
                               F_ alpha i = F_ (Canon alpha i) i.
Proof.
  unfold F_; intros. rewrite F_star_equation_2.
  destruct (E0_eq_dec alpha Zero).
  - now  destruct (Limit_not_Zero  H).
  - cbn; destruct (Utils.dec (Limitb alpha)) .
    + cbn; auto.
    + red in H. rewrite e in H; discriminate.
Qed.

(** Derived lemmas about F_ functions *)


Lemma F_star_Succ:  forall alpha n i,
    F_star (alpha, S n) i = 
    F_ alpha (F_star (alpha, n) i).
Proof.
  destruct n.
  - intros; now rewrite F_star_zero_eqn.
  - intros i; unfold F_; now rewrite Fstar_S.  
Qed.

Lemma F_star_iterate : forall alpha n i,
    F_star (alpha, n) i =  iterate (F_ alpha) n i.
Proof.
  induction n; intro i; simpl.
  - now rewrite F_star_zero_eqn. 
  - specialize (IHn i); rewrite F_star_Succ in *;  now rewrite <- IHn.
Qed.

Lemma F_succ_eqn : forall alpha i,
    F_ (Succ alpha) i = iterate (F_ alpha) (S i) i.
Proof with auto with E0.
  intros;rewrite F_eq2,  F_star_iterate ...
  -  now rewrite Pred_of_Succ.
Qed.


(** performs an induction only on the occ1-th and occ2_th occurrences of n *)

Tactic Notation "undiag2" constr(n) integer(occ1) integer(occ2) :=
  let n' := fresh "n" in
  generalize n at occ1 occ2; intro n'; induction n'.

Lemma LF1 : forall n,  F_ 1 n = S (2 * n).
Proof.
    intro n; unfold Fin; rewrite FinS_Succ_eq, F_succ_eqn.
    rewrite iterate_rw, F_zero_eqn.  
    simpl; rewrite iterate_ext with (g := S).
    - undiag2 n 1 3.
      + simpl; abstract lia.
      + simpl; auto.
    - intro; now rewrite F_zero_eqn.
Qed. 

Lemma LF2 : forall i, (exp2 i * i < F_ 2 i)%nat.
Proof.
  intro i; ochange (Fin 2) (Succ 1); rewrite F_succ_eqn.
  undiag2 i 1 3.
  -  intros. cbn;  intros; cbn.  repeat rewrite LF1. abstract lia. 
  - intros; simpl exp2; ring_simplify. simpl (2+n)%nat.
      rewrite iterate_S_eqn, LF1; abstract lia.
Qed.


Lemma Canon_plus_first_step: forall i alpha beta, 
    Canon_plus (S i) (Succ alpha) beta ->
    alpha = beta \/ Canon_plus (S i) alpha beta.
Proof.
  destruct alpha, beta.
  unfold Canon_plus, Paths.const_path; simpl ;intros H.
  destruct (Paths.const_pathS_first_step H).
  - rewrite Canon.canonS_succ in e; auto.
    subst cnf0;  assert (cnf_ok0 =cnf_ok).
    apply nf_proof_unicity.
    subst cnf_ok0; left;auto. 
  - rewrite Canon.canonS_succ in c;[ right;auto | auto].
Qed.

Lemma Canon_plus_first_step_lim:
  forall i alpha beta, Limitb alpha ->
                       Canon_plus (S i) alpha beta  ->
                       beta = CanonS alpha i \/
                       Canon_plus (S i) (CanonS alpha i) beta.
Proof.
  destruct alpha, beta.
  unfold Canon_plus, Paths.const_path; simpl.
  intros H H0; destruct (const_pathS_first_step H0).
  -  left;  unfold CanonS;   f_equal;  f_equal. simpl; subst cnf0.
     f_equal; apply nf_proof_unicity.
  - right; auto.
Qed.

Lemma F_alpha_0_eq : forall alpha: E0, F_ alpha 0 = 1.
  intro alpha. pattern alpha; apply well_founded_induction with E0.Lt.
  - apply E0.Lt_wf.
  - clear alpha; intros alpha Halpha.
    destruct (Zero_Limit_Succ_dec alpha).
    destruct s.
    + subst alpha; now rewrite F_zero_eqn.
    +  rewrite F_lim_eqn;auto; unfold Canon; now rewrite F_zero_eqn. 
    +  destruct s; subst; rewrite F_succ_eqn; simpl; apply Halpha, Lt_Succ.
Qed.

(** Properties of [F_ alpha]  *)

Section Properties.
  Record P (alpha:E0) : Prop :=
    mkP {
        PA : strict_mono (F_ alpha);
        PB : forall n, (n < F_ alpha n)%nat;
        PC : F_ alpha <<= F_ (Succ alpha);
        PD : dominates_from 1 (F_ (Succ alpha)) (F_ alpha);
        PE : forall beta n, Canon_plus n alpha beta -> 
                            (F_ beta n <= F_ alpha n)%nat}.

  
  Section The_induction.

    (** Base step : (sequential) proof of (P 0) *)
    
    Lemma mono_F_Zero : strict_mono (F_ Zero).
    Proof. 
      intros n p H; repeat rewrite F_zero_eqn; auto with arith. 
    Qed. 

    Lemma Lt_n_F_Zero_n : forall n:nat, (n < F_ Zero n)%nat. 
    Proof. intros n ; rewrite F_zero_eqn; auto with arith. Qed.

    Lemma F_One_Zero_dom : dominates_from 1 (F_ 1) (F_ Zero).
    Proof.
      red;intros.
      rewrite F_zero_eqn. rewrite LF1; abstract lia.
    Qed.

    Hint Resolve F_One_Zero_dom mono_F_Zero Lt_n_F_Zero_n : T1.

    Lemma F_One_Zero_ge :  F_ Zero <<= F_ 1.
    Proof.
      intro n; destruct n;
        rewrite F_zero_eqn, LF1; abstract lia.  
    Qed. 

    Hint Resolve  F_One_Zero_ge : T1.

    Lemma PZero : P Zero.
    Proof. 
      split; auto with T1; ord_eq  (Succ Zero) (Fin 1).
      all: try (rewrite H;auto with T1).
      unfold Canon_plus; intros beta n H0;
        unfold Zero in H0; simpl in H0.
      destruct n.
      - inversion H0. 
      - destruct (const_pathS_zero  H0). 
    Qed.   

    Variable alpha : E0.
    Hypothesis Halpha : forall beta, Lt beta alpha -> P beta.

    Ltac hdecomp := destruct Halpha.
    Section alpha_Succ.
      Variable beta: E0.
      Hypothesis alpha_def : alpha = Succ beta.

      Remark R1 : strict_mono (F_ alpha).
      Proof.
        destruct (Halpha beta).
        subst alpha; apply Lt_Succ.
        red; intros.
        subst alpha.
        repeat rewrite F_succ_eqn.
        induction H.
        
        rewrite (iterate_S_eqn (F_ beta) (S n)).
        apply Lt.lt_le_trans with (F_ beta (iterate (F_ beta) (S n) n)).
        auto. 
        apply mono_weak; auto.
        
        apply Nat.lt_le_incl.
        apply iterate_mono;auto.
        destruct (Halpha beta).
        apply Lt_Succ.
        
        
        transitivity (iterate (F_ beta) (S m) m);auto.
        rewrite (iterate_S_eqn (F_ beta) (S m)).
        apply Lt.lt_le_trans with (F_ beta (iterate (F_ beta) (S m) m)).
        auto.
        apply mono_weak; auto.
        apply Nat.lt_le_incl.
        apply iterate_mono;auto.
      Qed.

      Remark RB : forall n, (n < F_ alpha n)%nat.
      Proof.
        subst  alpha.
        intro n. 
        rewrite F_succ_eqn.
        destruct (Halpha beta).
        apply Lt_Succ.
        change n with (iterate (F_ beta) 0 n) at 1.
        apply iterate_lt;auto with arith.
        split; auto.
      Qed.
      
      Remark RD : dominates_from 1 (F_ (Succ alpha)) (F_ alpha).
        generalize RB; intro RB'.
        rewrite alpha_def .
        
        destruct (Halpha beta).
        rewrite alpha_def ;apply Lt_Succ.
        intros n Hn.
        rewrite (F_succ_eqn (Succ beta)).
        apply Nat.lt_le_trans with (F_ (Succ beta) (F_ (Succ beta) n)).
        
        rewrite <- alpha_def.
        apply RB'.
        rewrite iterate_S_eqn2.
        change (F_ (Succ beta) (F_ (Succ beta) n)) with
            (iterate (F_ (Succ beta)) 1 (F_ (Succ beta) n)).
        apply iterate_le.

        generalize R1; intro R1'.
        rewrite <- alpha_def. auto.
        assumption.
      Qed.


      Remark RE : forall beta n, Canon_plus n alpha beta -> 
                                 (F_ beta n <= F_ alpha n)%nat.
      Proof.
        destruct n. repeat rewrite F_alpha_0_eq. 
        reflexivity.
        intros. 
        transitivity (F_ beta (S n)).
        rewrite alpha_def in H.
        - destruct (Canon_plus_first_step _ _ _ H).
          subst beta0; reflexivity.
          destruct (Halpha beta).
          rewrite alpha_def.
          apply Lt_Succ.
          apply PE0.
          auto.
        - destruct (Halpha beta).
          rewrite alpha_def.
          apply Lt_Succ.
          rewrite alpha_def.
          apply Nat.lt_le_incl.
          apply PD0.
          auto with arith.
      Qed.

      Remark RC : F_ alpha <<= F_ (Succ alpha).
      Proof.
        intro n; destruct n.
        repeat rewrite F_alpha_0_eq. auto with arith.
        apply Nat.lt_le_incl.
        apply RD. auto with arith.
      Qed.

      Remark RP : P alpha.
        split.
        apply R1.
        apply RB.
        apply RC.
        apply RD.
        apply RE.
      Qed.

    End alpha_Succ.


    Section alpha_limit.
      Hypothesis Hlim : Limitb alpha.


      Remark RBlim : forall n, (n < F_ alpha n)%nat.
        intro n.
        rewrite F_lim_eqn.
        destruct (Halpha (Canon alpha n)).
        apply Canon_lt. 
        now apply Limit_not_Zero.
        auto.
        auto.
      Qed.
      
      Remark RAlim : strict_mono (F_ alpha).
      Proof.
        red;intros m n H; destruct m.
        - rewrite (F_lim_eqn alpha n);auto.
          rewrite F_alpha_0_eq. (* bad name *)
          destruct n. inversion H.
          unfold Canon.
          apply Nat.le_lt_trans with (S n).
          auto with arith.
          destruct (Halpha (CanonS alpha n)).
          apply CanonS_lt. 
          now apply Limit_not_Zero.
          now apply PB0.
          
        - destruct n. inversion H.
          rewrite (F_lim_eqn alpha (S n));auto.
          rewrite (F_lim_eqn alpha (S m));auto.
          assert (Canon_plus 1 (Canon alpha (S n)) (Canon alpha (S m))).
          apply KS_thm_2_4_E0; auto.
          auto with arith.
          assert (Canon_plus (S n) (Canon alpha (S n)) (Canon alpha (S m))).
          eapply Cor12_E0 with 0; auto with arith.
          apply canonS_limit_mono; auto with T1.
          auto with arith.
          auto with E0.
          auto with arith.
          apply Nat.le_lt_trans with (F_ (Canon alpha (S n)) (S m) ).
          destruct (Halpha (Canon alpha (S n))).
          apply Canon_lt. 
          now apply Limit_not_Zero.
          apply PE0. auto. auto.
          eapply Cor12_E0 with 0; auto with arith.
          apply canonS_limit_mono; auto with T1.
          auto with arith.
          destruct (Halpha (Canon alpha (S n))).
          apply Canon_lt. 
          now apply Limit_not_Zero.
          auto with E0.
  auto with arith.
  apply PA.
  apply Halpha.
  apply CanonS_lt.
  auto with E0.
 auto with arith.
      Qed.



      Remark RClim : F_ alpha <<= F_ (Succ alpha).
      Proof.
        intro n; destruct n.
        - repeat rewrite F_alpha_0_eq; auto with arith.
        -  apply Nat.lt_le_incl;  rewrite F_succ_eqn.
           change (F_ alpha (S n)) with (iterate (F_ alpha) 1 (S n)).
           apply iterate_lt. split.
          +  apply RAlim.
          +  red;intros; apply RBlim.
          +  auto with arith.
      Qed.

      Remark RDlim : dominates_from 1 (F_ (Succ alpha)) (F_ alpha).
      Proof.
        red;intros; rewrite F_succ_eqn.
        change (F_ alpha p) with (iterate (F_ alpha) 1 p);
        apply iterate_lt. split; auto.
        -   apply RAlim.
        -   red;intros; apply RBlim.
        -   auto with arith.
      Qed.

      Remark RElim : forall beta n, Canon_plus n alpha beta -> 
                                    (F_ beta n <= F_ alpha n)%nat.
      Proof.
        destruct n.
        - now  repeat rewrite F_alpha_0_eq. 
        - intros H;  destruct (Canon_plus_first_step_lim _ _  _ Hlim H).
          +  rewrite (F_lim_eqn alpha _).
             * now rewrite H0.
             * auto.
          +  rewrite (F_lim_eqn alpha _);auto.
             destruct (Halpha (Canon alpha (S n))); auto.
             apply CanonS_lt;  now apply Limit_not_Zero.
      Qed.

    End alpha_limit.

    Lemma LL : P alpha.
    Proof. 
      destruct (Zero_Limit_Succ_dec alpha).
      destruct s.
      - subst; apply PZero.
      - split.
        apply RAlim; auto.
        apply RBlim; auto.
        apply RClim; auto.
        apply RDlim; auto.
        apply RElim; auto.
      - destruct s; split.
        eapply R1;eauto.
        eapply RB;eauto.
        eapply RC;eauto.
        eapply RD;eauto.
        eapply RE;eauto.
    Qed.

  End The_induction.


  Theorem TH_packed : forall alpha, P alpha.
  Proof.
    intro alpha; apply well_founded_induction with E0.Lt.
    - exact E0.Lt_wf.
    - apply LL.
  Qed.

End Properties.


  Theorem F_alpha_mono alpha : strict_mono (F_ alpha).
  Proof. now  destruct  (TH_packed alpha). Qed.

  
  Theorem F_alpha_ge_S alpha : forall n, (n < F_ alpha n)%nat.
  Proof. now  destruct  (TH_packed alpha). Qed.

  Theorem F_alpha_Succ_le alpha : F_ alpha <<= F_ (Succ alpha).
  Proof. now  destruct  (TH_packed alpha). Qed.

  Theorem F_alpha_dom alpha : dominates_from 1 (F_ (Succ alpha)) (F_ alpha).
  Proof. now  destruct  (TH_packed alpha). Qed.

  Theorem F_alpha_beta alpha : forall beta n, Canon_plus n alpha beta -> 
                                        (F_ beta n <= F_ alpha n)%nat.
  Proof. now  destruct  (TH_packed alpha). Qed.





Lemma LF2_0 : dominates_from 0 (F_ 2) (fun i => exp2 i * i)%nat.
Proof.
  red. intros ; apply LF2 ; auto.  
Qed.


Lemma LF3_2  : dominates_from 2  (F_ 3) (fun  n => iterate exp2 (S n) n).
Proof.  
 intros p H; assert (H0:= LF2_0).
  ochange (Fin 3) (Succ 2); rewrite F_succ_eqn.
   eapply iterate_dom_prop; eauto with arith. 
   - apply exp2_ge_S.
   - apply exp2_mono.
   - apply F_alpha_mono.
   - red; intros; transitivity (exp2 p0 * p0)%nat; auto.
   {  rewrite <- Nat.mul_1_r at 1; apply Nat.mul_lt_mono_pos_l; auto.
      apply exp2_positive.
   }
   apply LF2_0; abstract lia.
Qed.

(** From Ketonen and Solovay, page 284, op. cit. *)

Section Proposition_page_284.

  Variables alpha beta : E0.
  Hypothesis H_beta_alpha : Lt beta alpha.


  Section case_eq.
    Hypothesis Heq : alpha = Succ beta.

    Fact F2 : forall i, (1 <= i ->  F_ beta i < F_ alpha i)%nat.
    Proof.
      subst alpha; intros i H; apply (F_alpha_dom beta i H).
    Qed.

  End case_eq.


  Section case_lt.
    Variable n: nat.
    Hypothesis Hlt :  Lt (Succ beta) alpha.
    
    Hypothesis Hd : Canon_plus (S n) alpha beta.

    Fact F5 : Canon_plus (S (S n)) alpha (Succ beta).
      destruct alpha, beta. simpl.
      apply L2_6_2; auto.
    Qed.

    
    Fact F6 : forall i, (S n < i)%nat ->  Canon_plus i alpha (Succ beta).
    Proof.
      destruct alpha, beta; unfold lt, Canon_plus in *; simpl in *.
      intros.
      destruct i.
      inversion H.
      destruct i.
      inversion H.
      inversion H1.
      apply Cor12_3 with (S (S n)); auto.
      auto with arith.
      apply L2_6_2; auto.
    Qed.   

    Fact F7 : forall i, (S n < i -> F_ (Succ beta) i <= F_ alpha i)%nat.
    Proof.
      intros; apply  F_alpha_beta.  
      apply F6; auto.
    Qed.

    Fact F8 : forall i, (S n < i -> F_ beta i < F_ (Succ beta) i)%nat.
    Proof.
      intros i H; apply  (F_alpha_dom beta i); abstract lia.
    Qed.

    Fact F9 : forall i, (S n < i -> F_ beta i < F_ alpha i)%nat.
    Proof.
      intros; eapply Nat.lt_le_trans.
      eapply F8;eauto.
      apply F7;auto.
    Qed.

  End case_lt.


  Lemma Propp284_0 : forall n, Canon_plus (S n) alpha beta ->
                             forall i, (S n < i -> F_ beta i < F_ alpha i)%nat.
  Proof.
    assert (Le (Succ beta) alpha) by (now apply Lt_succ_le).
    assert ({alpha = Succ beta}+{Lt (Succ beta) alpha}). {
      rewrite <- lt_Succ_inv in H.
      apply Lt_succ_le in H; destruct (E0.le_lt_eq_dec  H); auto.
    }
    destruct H0.
    - intros; apply F2; [trivial | lia].
    - intros; eapply F9; eauto.
  Qed.

  
  Lemma Propp284: dominates (F_ alpha) (F_ beta).
  Proof.
    destruct (Lemma2_6_1_E0  H_beta_alpha) as [i Hi].
    exists (S (S i)); intros p Hp; apply Propp284_0 with i;  auto.
  Qed.

  
End Proposition_page_284.



 

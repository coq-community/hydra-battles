(** * The Wainer hierarchy of rapidly growing functions (variant)


    After Wainer, Ketonen, Solovay, etc .
 *)


From hydras  Require Import  Iterates  Simple_LexProd Exp2.
From hydras Require Import  E0 Canon Paths primRec Hprime.
Import RelationClasses Relations.

From Coq Require Import ArithRing Lia.

From Equations Require Import Equations.

From hydras Require Import primRec.

(** For masking primRec's iterate *)

Import Prelude.Iterates.



(** ** Definition, using [coq-equations] 

The following definition is not accepted by the [equations] plug-in.

 *)

#[global] Instance Olt : WellFounded E0lt := E0lt_wf.

(* begin snippet FailDemo *)

Fail Equations F_ (alpha: E0) (i:nat) :  nat  by wf  alpha E0lt :=
  F_ alpha  i with E0_eq_dec alpha E0zero :=
    { | left _zero =>  i ;
      | right _nonzero
          with Utils.dec (Limitb alpha) :=
          { | left _limit =>  F_ (Canon alpha i)  i ;
            | right _notlimit =>  iterate (F_ (Pred alpha)) (S i) i}}.

(* end snippet FailDemo *)

(**

    Indeed, we define the $n$-th iterate of [F_ alpha] by well-founded
    recursion  on the pair (alpha,n), then [F_ alpha] as the first iterate 
    of the defined function.
 *)



(* begin snippet goodDefa:: no-out *)
Definition call_lt (c c' : E0 * nat) :=
  lexico E0lt (Peano.lt) c c'.

Lemma call_lt_wf : well_founded call_lt.
  unfold call_lt; apply Inverse_Image.wf_inverse_image,  wf_lexico.
  -  apply E0lt_wf.
  -  unfold Peano.lt; apply Nat.lt_wf_0. 
Qed.

#[ global ] Instance WF : WellFounded call_lt := call_lt_wf.

(*  F_star (alpha,i) is intended to be the i-th iterate of F_ alpha *)

Equations  F_star (c: E0 * nat) (i:nat) :  nat by wf  c call_lt :=
  F_star (alpha, 0) i := i;
  F_star (alpha, 1) i
    with E0_eq_dec alpha E0zero :=
    { | left _zero => S i ;
      | right _nonzero
          with Utils.dec (Limitb alpha) :=
          { | left _limit => F_star (Canon alpha i,1) i ;
            | right _notlimit =>
              F_star (Pred alpha, S i)  i}};
  F_star (alpha,(S (S n))) i :=
    F_star (alpha, 1) (F_star (alpha, (S n)) i).
(* end snippet goodDefa *)


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

(* begin snippet goodDefb *)
Definition F_ alpha i := F_star (alpha, 1) i.
(* end snippet goodDefb *)

(** ** We get the "usual" equations for [F_]  *)

(** *** Relations between [F_star] and [F_] *)

Lemma F_star_zero_eqn : forall alpha i, F_star (alpha, 0) i = i.
Proof.
  intros; now rewrite F_star_equation_1.
Qed.

Lemma Fstar_S : forall alpha n i, F_star (alpha, S (S n)) i =
                                  F_ alpha  (F_star (alpha, S n) i).
Proof.  
  unfold F_; intros; now rewrite F_star_equation_3.
Qed.

Lemma F_eq2 : forall alpha i,
    E0succb alpha -> 
    F_ alpha i = F_star (Pred alpha, S i) i.
Proof.
  unfold F_; intros; rewrite F_star_equation_2.
  destruct (E0_eq_dec alpha E0zero).
  - subst alpha; discriminate H.
  - cbn; destruct (Utils.dec (Limitb alpha)) .
    + assert (true=false) by 
          ( now  destruct (Succ_not_Limitb _ H)). 
      discriminate.
    + now cbn.
Qed.

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


(** *** Usual equations for [F_] *)

(* begin snippet FEquations *)

Lemma F_zero_eqn : forall i, F_ E0zero i = S i.  (* .no-out *)
(*| .. coq:: none |*)
Proof.
  intro i. unfold F_; rewrite F_star_equation_2.
  destruct (E0_eq_dec E0zero E0zero).
  - now cbn.
  - now destruct n.
Qed.
(*||*)

Lemma F_lim_eqn : forall alpha i,
    Limitb alpha ->
    F_ alpha i = F_ (Canon alpha i) i. (* .no-out *)
(*| .. coq:: none |*)
Proof.
  unfold F_; intros. rewrite F_star_equation_2.
  destruct (E0_eq_dec alpha E0zero).
  - now  destruct (Limit_not_Zero  H).
  - cbn; destruct (Utils.dec (Limitb alpha)) .
    + cbn; auto.
    + red in H. rewrite e in H; discriminate.
Qed.
(*||*)

Lemma F_succ_eqn : forall alpha i,
    F_ (E0succ alpha) i = iterate (F_ alpha) (S i) i. (* .no-out *)
(*| .. coq:: none |*)
Proof with auto with E0.
  intros;rewrite F_eq2,  F_star_iterate ...
  -  now rewrite Pred_of_Succ.
Qed.
(*||*)
(* end snippet FEquations *)

(** ** First steps of the hierarchy *)


(** performs an induction only on the occ1-th and occ2_th occurrences of n *)

Tactic Notation "undiag2" constr(n) integer(occ1) integer(occ2) :=
  let n' := fresh "n" in
  generalize n at occ1 occ2; intro n'; induction n'.

(* begin snippet FirstValues *)

Lemma LF1 : forall i,  F_ 1 i = S (2 * i). (* .no-out *)
(*| .. coq:: none |*)
Proof.
  intro i; unfold Fin; rewrite FinS_Succ_eq, F_succ_eqn.
  rewrite iterate_rw, F_zero_eqn.  
  simpl; rewrite iterate_ext with (g := S).
  - undiag2 i 1 3.
    + simpl; abstract lia.
    + simpl; auto.
  - intro; now rewrite F_zero_eqn.
Qed. 
(*||*)

Lemma LF2 : forall i, exp2 i * i < F_ 2 i. (* .no-out *)
(*| .. coq:: none |*)
Proof.
  intro i; ochange (Fin 2) (E0succ 1); rewrite F_succ_eqn.
  undiag2 i 1 3.
  -  intros. cbn;  intros; cbn.  repeat rewrite LF1. abstract lia. 
  - intros; simpl exp2; ring_simplify. simpl (2+n)%nat.
    rewrite iterate_S_eqn, LF1; abstract lia.
Qed.
(*||*)
(* end snippet FirstValues *)

Corollary LF2' : forall i,  1 <= i -> exp2 i < F_ 2 i.
Proof.
  intros;  apply Lt.le_lt_trans with (exp2 i * i).
  - destruct (mult_O_le (exp2 i) i).
    + lia.
    + now rewrite mult_comm.
  -  apply LF2.
Qed.




Lemma F_alpha_0_eq : forall alpha: E0, F_ alpha 0 = 1.
  intro alpha. pattern alpha; apply well_founded_induction with E0lt.
  - apply E0lt_wf.
  - clear alpha; intros alpha Halpha.
    destruct (Zero_Limit_Succ_dec alpha).
    destruct s.
    + subst alpha; now rewrite F_zero_eqn.
    +  rewrite F_lim_eqn;auto; unfold Canon. rewrite Halpha. auto.
       Search (Canon ?a _ o< ?a).
       apply  (@Canon_lt 0 alpha). 
       intro Heq; subst. discriminate. 
    +  destruct s; subst; rewrite F_succ_eqn; simpl; apply Halpha, Lt_Succ.
Qed.

(** Properties of [F_ alpha]  *)
(* begin hide *)

Section Properties.
  Record P (alpha:E0) : Prop :=
    mkP {
        PA : strict_mono (F_ alpha);
        PB : forall n, n < F_ alpha n;
        PC : F_ alpha <<= F_ (E0succ alpha);
        PD : dominates_from 1 (F_ (E0succ alpha)) (F_ alpha);
        PE : forall beta n, Canon_plus n alpha beta -> 
                            F_ beta n <= F_ alpha n}.

  
  Section The_induction.

    (** Base step : (sequential) proof of (P 0) *)
    
    Lemma mono_F_Zero : strict_mono (F_ E0zero).
    Proof. 
      intros n p H; repeat rewrite F_zero_eqn; auto with arith. 
    Qed. 

    Lemma Lt_n_F_Zero_n : forall n:nat, n < F_ E0zero n. 
    Proof. intros n ; rewrite F_zero_eqn; auto with arith. Qed.

    Lemma F_One_Zero_dom : dominates_from 1 (F_ 1) (F_ E0zero).
    Proof.
      red;intros.
      rewrite F_zero_eqn. rewrite LF1; abstract lia.
    Qed.

    Local Hint Resolve F_One_Zero_dom mono_F_Zero Lt_n_F_Zero_n : T1.

    Lemma F_One_Zero_ge :  F_ E0zero <<= F_ 1.
    Proof.
      intro n; destruct n;
        rewrite F_zero_eqn, LF1; abstract lia.  
    Qed. 

    Local Hint Resolve  F_One_Zero_ge : T1.

    Lemma PZero : P E0zero.
    Proof. 
      split; auto with T1; ord_eq  (E0succ E0zero) (Fin 1).
      all: try (rewrite H;auto with T1).
      unfold Canon_plus; intros beta n H0;
        unfold E0zero in H0; simpl in H0.
      destruct n.
      - inversion H0. 
      - destruct (const_pathS_zero  H0). 
    Qed.   

    Variable alpha : E0.
    Hypothesis Halpha : forall beta, E0lt beta alpha -> P beta.

    Ltac hdecomp := destruct Halpha.
    Section alpha_Succ.
      Variable beta: E0.
      Hypothesis alpha_def : alpha = E0succ beta.

      Remark R1 : strict_mono (F_ alpha).
      Proof.
        destruct (Halpha beta).
        subst alpha; apply Lt_Succ.
        red; intros.
        subst alpha.
        repeat rewrite F_succ_eqn.
        induction H.
        
        rewrite (iterate_S_eqn (F_ beta) (S n)).
        apply Lt.lt_le_trans with (F_ beta
                                      (iterate (F_ beta) (S n) n)).
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

      Remark RB : forall n, n < F_ alpha n.
      Proof.
        subst  alpha.
        intro n. 
        rewrite F_succ_eqn.
        destruct (Halpha beta).
        apply Lt_Succ.
        change n with (iterate (F_ beta) 0 n) at 1.
        apply iterate_lt;auto with arith.
      Qed.
      
      Remark RD : dominates_from 1 (F_ (E0succ alpha)) (F_ alpha).
        generalize RB; intro RB'.
        rewrite alpha_def .
        
        destruct (Halpha beta).
        rewrite alpha_def ;apply Lt_Succ.
        intros n Hn.
        rewrite (F_succ_eqn (E0succ beta)).
        apply Nat.lt_le_trans with (F_ (E0succ beta) (F_ (E0succ beta) n)).
        
        rewrite <- alpha_def.
        apply RB'.
        rewrite iterate_S_eqn2.
        change (F_ (E0succ beta) (F_ (E0succ beta) n)) with
            (iterate (F_ (E0succ beta)) 1 (F_ (E0succ beta) n)).
        apply iterate_le.

        generalize R1; intro R1'.
        rewrite <- alpha_def. auto.
        assumption.
      Qed.


      Remark RE : forall beta n, Canon_plus n alpha beta -> 
                                 F_ beta n <= F_ alpha n.
      Proof.
        destruct n.
        repeat rewrite F_alpha_0_eq. 
        reflexivity.
        intros. 
        transitivity (F_ beta (S n)).
        rewrite alpha_def in H.
        - destruct (Canon_plus_first_step  H).
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

      Remark RC : F_ alpha <<= F_ (E0succ alpha).
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


      Remark RBlim : forall n, n < F_ alpha n.
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
          destruct (Halpha (Canon alpha (S n))).
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



      Remark RClim : F_ alpha <<= F_ (E0succ alpha).
      Proof.
        intro n; destruct n.
        - repeat rewrite F_alpha_0_eq; auto with arith.
        -  apply Nat.lt_le_incl;  rewrite F_succ_eqn.
           change (F_ alpha (S n)) with (iterate (F_ alpha) 1 (S n)).
           apply iterate_lt. 
           +  apply RAlim.
           +  red;intros; apply RBlim.
           +  auto with arith.
      Qed.

      Remark RDlim : dominates_from 1 (F_ (E0succ alpha)) (F_ alpha).
      Proof.
        red;intros; rewrite F_succ_eqn.
        change (F_ alpha p) with (iterate (F_ alpha) 1 p);
          apply iterate_lt. 
        -   apply RAlim.
        -   red;intros; apply RBlim.
        -   auto with arith.
      Qed.

      Remark RElim : forall beta n, Canon_plus n alpha beta -> 
                                    F_ beta n <= F_ alpha n.
      Proof.
        destruct n.
        - now  repeat rewrite F_alpha_0_eq. 
        - intros H;  destruct (Canon_plus_first_step_lim  Hlim H).
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
    intro alpha; apply well_founded_induction with E0lt.
    - exact E0lt_wf.
    - apply LL.
  Qed.

End Properties.

(* end hide *)

(* begin snippet FalphaThms *)

Theorem F_alpha_mono alpha : strict_mono (F_ alpha). (* .no-out *)
(*| .. coq:: none |*)
Proof. now  destruct  (TH_packed alpha). Qed.
(*||*)

Theorem F_alpha_gt alpha : forall n, n < F_ alpha n. (* .no-out *)
(*| .. coq:: none |*)
Proof. now  destruct  (TH_packed alpha). Qed.
(*||*)

 #[deprecated(note="use F_alpha_gt")]
   Notation F_alpha_ge_S := StrictOrder_Transitive (only parsing).


Corollary F_alpha_positive alpha :  forall n, 0 < F_ alpha n. (* .no-out *)
(*| .. coq:: none |*)
Proof.
  intro n; apply Lt.le_lt_trans with n; auto with arith.
  apply F_alpha_gt.
Qed.



Theorem F_alpha_Succ_le alpha : F_ alpha <<= F_ (E0succ alpha). 
(*| .. coq:: none |*)
Proof. now  destruct  (TH_packed alpha). Qed.
(*||*)


Theorem F_alpha_dom alpha :
  dominates_from 1 (F_ (E0succ alpha)) (F_ alpha). (* .no-out *)
(*| .. coq:: none |*)
Proof. now  destruct  (TH_packed alpha). Qed.
(*||*)

(** [F_] is not mononotonous in [alpha] in general. 
      Nevertheless, this lemma may help (from [KS]) *)


Theorem F_restricted_mono_l alpha :
  forall beta n, Canon_plus n alpha beta -> 
                 F_ beta n <= F_ alpha n. (* .no-out *)
(*| .. coq:: none |*)
Proof. now  destruct (TH_packed alpha). Qed.
(*||*)

(* end snippet FalphaThms *)

Lemma LF2_0 : dominates_from 0 (F_ 2) (fun i => exp2 i * i).
Proof.
  red. intros ; apply LF2 ; auto.  
Qed.


Lemma LF3_2  : dominates_from 2  (F_ 3) (fun  n => iterate exp2 (S n) n).
Proof.  
  intros p H; assert (H0:= LF2_0).
  ochange (Fin 3) (E0succ 2); rewrite F_succ_eqn.
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

(* begin snippet FDomContext *)

Section Compatibility_F_dominates.

  Variables alpha beta : E0.
  Hypothesis H'_beta_alpha : E0lt beta alpha.

  (* end snippet FDomContext *)
  
  (* begin hide *)
  Section case_eq.
    Hypothesis Heq : alpha = E0succ beta.

    Fact F2 : forall i, (1 <= i ->  F_ beta i < F_ alpha i)%nat.
    Proof.
      subst alpha; intros i H; apply (F_alpha_dom beta i H).
    Qed.

  End case_eq.


  Section case_lt.
    Variable n: nat.
    Hypothesis Hlt :  E0lt (E0succ beta) alpha.
    
    Hypothesis Hd : Canon_plus (S n) alpha beta.

    Fact F5 : Canon_plus (S (S n)) alpha (E0succ beta).
    Proof.
      destruct alpha, beta; cbn;  now apply L2_6_2.  
    Qed.

    
    Fact F6 : forall i, (S n < i)%nat ->  Canon_plus i alpha (E0succ beta).
    Proof.
      destruct alpha, beta; unfold lt, Canon_plus in *; simpl in *.
      intros i H; destruct i.
      - inversion H.
      - destruct i.
        + inversion H. lia. 
        + apply Cor12_3 with (S (S n)); auto.
          apply L2_6_2; auto.
    Qed.   

    Fact F7 : forall i, (S n < i -> F_ (E0succ beta) i <= F_ alpha i)%nat.
    Proof.
      intros; apply  F_restricted_mono_l; apply F6; auto.
    Qed.

    Fact F8 : forall i, (S n < i -> F_ beta i < F_ (E0succ beta) i)%nat.
    Proof.
      intros i H; apply  (F_alpha_dom beta i); abstract lia.
    Qed.

    Fact F9 : forall i, (S n < i -> F_ beta i < F_ alpha i)%nat.
    Proof.
      intros ? ?; eapply Nat.lt_le_trans.
      - eapply F8;eauto.
      - apply F7;auto.
    Qed.

  End case_lt.

  (* end hide *)
  
  Lemma F_mono_l_0 : forall n,
      Canon_plus (S n) alpha beta ->
      forall i, (S n < i -> F_ beta i < F_ alpha i)%nat.
  Proof.
    assert (H: E0le (E0succ beta) alpha) by (now apply Lt_Succ_Le).
    assert (H0: {alpha = E0succ beta} + {E0lt (E0succ  beta) alpha}).
    {
      rewrite <- lt_Succ_inv in H.
      apply Lt_Succ_Le in H; destruct (E0.le_lt_eq_dec  H); auto.
    }
    destruct H0.
    - intros; apply F2; [trivial | lia].
    - intros; eapply F9; eauto.
  Qed.

  (* begin snippet FDom *)
  
  Lemma F_mono_l: dominates (F_ alpha) (F_ beta). (* .no-out *)
  (*| .. coq:: none |*)
  Proof.
    destruct (Lemma2_6_1_E0  H'_beta_alpha) as [i Hi].
    exists (S (S i)); intros p Hp; apply F_mono_l_0 with i;  auto.
  Qed.
  (*||*)
  
End Compatibility_F_dominates.
(* end snippet FDom *)


(** * Comparison with the Hardy hierarchy 
       
      [(F_ alpha (S n) <= H'_ (Phi0 alpha) (S n))]
*)



Section H'_F.
  
Let P (alpha: E0) := forall n,  (F_ alpha (S n) <= H'_ (phi0 alpha) (S n))%nat.

 Variable alpha: E0.

 Hypothesis IHalpha : forall  beta, beta o< alpha -> P beta.

 Lemma HF0 : P E0zero.
 Proof.
   intro n; rewrite F_zero_eqn.
   replace (phi0 E0zero) with (Fin 1).
   - now rewrite H'_Fin.
   - now apply E0_eq_intro.
 Qed.

 Lemma HFsucc : E0succb alpha -> P alpha.
 Proof.
   intro H; destruct (Succb_Succ _ H) as [beta Hbeta]; subst.
   intro n; rewrite H'_Phi0_succ.
   unfold H'_succ_fun; rewrite F_succ_eqn.
   specialize (IHalpha beta (Lt_Succ beta));  unfold P in IHalpha.
   - apply iterate_mono_1 with 1.
     + apply F_alpha_mono.
     + intro k; apply F_alpha_gt.
     + intros; destruct n0.
       * lia.
       * apply IHalpha.
     +lia.
 Qed.


  (** The following proof is far from being trivial.
      It uses some lemmas from the Ketonen-Solovay machinery *)
 
  Lemma HFLim : Limitb alpha -> P alpha.
  Proof.
    intros Halpha n; rewrite H'_eq3.
    - rewrite CanonS_phi0_lim; [| trivial].
      rewrite F_lim_eqn; auto.
      + transitivity (H'_ (phi0 (Canon alpha (S n))) (S n)).
        *  apply IHalpha.
           apply CanonS_lt.
           now apply Limit_not_Zero.
        * (** Not trivial, since [H'_ ] is not monotonous ! *)

          apply H'_restricted_mono_l.
          
          red; cbn; apply KS_thm_2_4_lemma5.
          -- apply Cor12_1 with 0.
           ++ apply nf_canon, cnf_ok.
           ++ apply canonS_limit_mono.
              ** apply cnf_ok.
              ** destruct alpha; cbn; assumption. 
              ** auto with arith. 
           ++ auto with arith.
           ++ apply KS_thm_2_4.
              ** apply cnf_ok.
              ** destruct alpha; auto.
              ** auto with arith. 
          --  apply nf_canon, cnf_ok.
          --  apply limitb_canonS_not_zero.
              ++ apply cnf_ok.
              ++ now destruct alpha.
    - apply Limitb_phi0.
      apply Limit_not_Zero; auto. 
Qed.

End H'_F.

(* begin snippet HprimeF:: no-out  *)

Lemma H'_F alpha : forall n,  F_ alpha (S n) <= H'_ (phi0 alpha) (S n).
Proof.
  pattern alpha; apply well_founded_induction with E0lt.
(* end snippet HprimeF *)
  - apply E0lt_wf.  
  -  clear alpha; intros alpha IHalpha.
     destruct (Zero_Limit_Succ_dec alpha) as [[Hzero | Hlim] | Hsucc].
    + subst; apply HF0.
    + apply HFLim; auto.
    + destruct Hsucc; subst; apply HFsucc.
      intros; apply IHalpha; auto.
      apply Succ_Succb.
  Qed.


(** * A variant (Lob-Wainer hierarchy) 
***************************************)


Equations  f_star (c: E0 * nat) (i:nat) :  nat by wf c call_lt :=
  f_star (alpha, 0) i := i;
  f_star (alpha, 1) i
    with E0_eq_dec alpha E0zero :=
    { | left _zero => S i ;
      | right _nonzero
          with Utils.dec (Limitb alpha) :=
          { | left _limit => f_star (Canon alpha i,1) i ;
            | right _successor =>
              f_star (Pred alpha, i)  i}};
  f_star (alpha,(S (S n))) i :=
    f_star (alpha, 1) (f_star (alpha, (S n)) i).

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


(**  Finally, [f_ alpha] is defined as its first iterate  ! *)

Definition f_ alpha i := f_star (alpha, 1) i.

(** ** We get the "usual" equations for [F_]  *)

(** *** Relations between [F_star] and [F_] *)

Lemma f_star_zero_eqn : forall alpha i, f_star (alpha, 0) i = i.
Proof.
  intros; now rewrite f_star_equation_1.
Qed.

Lemma fstar_S : forall alpha n i, f_star (alpha, S (S n)) i =
                                  f_ alpha  (f_star (alpha,  S n) i).
Proof.  
  unfold F_; intros; now rewrite f_star_equation_3.
Qed.

Lemma f_eq2 : forall alpha i,
    E0succb alpha -> 
    f_ alpha i = f_star (Pred alpha,  i) i.
Proof.
  unfold f_; intros; rewrite f_star_equation_2.
  destruct (E0_eq_dec alpha E0zero).
  - subst alpha; discriminate H.
  - cbn; destruct (Utils.dec (Limitb alpha)) .
    + assert (true=false) by 
          ( now  destruct (Succ_not_Limitb _ H)). 
      discriminate.
    + now cbn.
Qed.

Lemma f_star_Succ:  forall alpha n i,
    f_star (alpha, S n) i = 
    f_ alpha (f_star (alpha, n) i).
Proof.
  destruct n.
  - intros; now rewrite f_star_zero_eqn.
  - intros i; unfold f_; now rewrite fstar_S.  
Qed.

Lemma f_star_iterate : forall alpha n i,
    f_star (alpha, n) i =  iterate (f_ alpha) n i.
Proof.
  induction n; intro i; simpl.
  - now rewrite f_star_zero_eqn. 
  - specialize (IHn i); rewrite f_star_Succ in *;  now rewrite <- IHn.
Qed.



(** *** Usual equations for [f_] *)

Lemma f_zero_eqn : forall i, f_ E0zero i = S i.
Proof.
  intro i. unfold f_; rewrite f_star_equation_2.
  destruct (E0_eq_dec E0zero E0zero).
  - now cbn.
  - now destruct n.
Qed.


Lemma f_lim_eqn : forall alpha i,  Limitb alpha ->
                                   f_ alpha i = f_ (Canon alpha i) i.
Proof.
  unfold f_; intros. rewrite f_star_equation_2.
  destruct (E0_eq_dec alpha E0zero).
  - now  destruct (Limit_not_Zero  H).
  - cbn; destruct (Utils.dec (Limitb alpha)) .
    + cbn; auto.
    + red in H; rewrite e in H; discriminate.
Qed.


Lemma f_succ_eqn : forall alpha i,
    f_ (E0succ alpha) i = iterate (f_ alpha) i i.
Proof with auto with E0.
  intros;rewrite f_eq2,  f_star_iterate ...
  -  now rewrite Pred_of_Succ.
Qed.


Lemma id_le_f_alpha (alpha: E0) : forall i, i <= f_ alpha i. 
Proof.
 pattern alpha; apply (well_founded_induction E0lt_wf);
   clear alpha; intros alpha IHalpha.
 destruct (Zero_Limit_Succ_dec alpha) as [[HZero | Hlim] | Hsucc].
   - subst; intros i ; rewrite !f_zero_eqn; auto with arith. 
   - intros i.  rewrite !(f_lim_eqn alpha).
     + apply IHalpha,  Canon_lt; now apply Limit_not_Zero.
     + apply Hlim.
   - destruct Hsucc as [beta Hbeta]; subst; intro i; rewrite f_succ_eqn. 
     generalize i at 1 3; induction i. 
     + intros; cbn; auto with arith.  
     + intros; cbn; transitivity (iterate (f_ beta) i i0); auto. 
     apply (IHalpha beta (Lt_Succ beta)). 
Qed.


Section Properties_of_f_alpha.

Record  Q (alpha:E0) : Prop :=
    mkQ {
        QA : strict_mono (f_ alpha);
        QD : dominates_from 2 (f_ (E0succ alpha)) (f_ alpha);
        QE : forall beta n, Canon_plus n alpha beta -> 
                            f_ beta n <= f_ alpha n}.

Section The_induction.
  
  Lemma QA0 : strict_mono (f_ E0zero).
  Proof. 
    intros n p H; repeat rewrite f_zero_eqn; auto with arith. 
  Qed. 



  Lemma QD0 : dominates_from 2 (f_ (E0succ E0zero)) (f_ E0zero).
  Proof. 
    intros p Hp; rewrite f_succ_eqn, f_zero_eqn. 
    apply Lt.lt_le_trans with (iterate S p p).
    - replace (iterate S p p) with (p + p).
      + lia.
      + clear Hp; generalize p at 2 4; induction p. 
        * cbn; reflexivity.
        * intro p0; cbn; now rewrite IHp. 
    -  apply Nat.eq_le_incl, iterate_ext. intros ?; now rewrite f_zero_eqn.
  Qed.

  
  (** TODO : Study the equality F_ alpha i = Nat.pred (f_ alpha (S i)) *)


  
End The_induction.

End Properties_of_f_alpha.

(* begin  snippet DemoAssumptions *)
Print Assumptions F_zero_eqn.

(* end snippet DemoAssumptions *)


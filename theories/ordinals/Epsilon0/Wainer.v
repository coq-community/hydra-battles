(** * The Wainer hierarchy of rapidly growing functions


    After Wainer, Ketonen, Solovay, etc .

   [f_ alpha] is a variant of [F_ alpha] 
 *)

(** In development *)


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

Instance Olt : WellFounded Lt := E0.Lt_wf.


Fail Equations f_ (alpha: E0) (i:nat) :  nat  by wf  alpha Lt :=
  f_ alpha  i with E0_eq_dec alpha Zero :=
    { | left _ =>  i ;
      | right nonzero
          with Utils.dec (Limitb alpha) :=
          { | left _ =>  f_ (Canon alpha i)  i ;
            | right notlimit =>  iterate (f_ (Pred alpha)) i i}}.

(**

    Indeed, we define the $n$-th iterate of [f_ alpha] by well-founded
    recursion  on the pair (alpha,n), then [f_ alpha] as the first iterate 
    of the defined function.
 *)





Definition call_lt (c c' : E0 * nat) :=
  lexico Lt (Peano.lt) c c'.

Lemma call_lt_wf : well_founded call_lt.
  unfold call_lt; apply Inverse_Image.wf_inverse_image,  wf_lexico.
  -  apply E0.Lt_wf.
  -  unfold Peano.lt; apply Nat.lt_wf_0. 
Qed.

Instance WF : WellFounded call_lt := call_lt_wf.


(** 

   [f_star (alpha,i)] is intended to be the i-th iterate of [f_ alpha]. 
 *)


Equations  f_star (c: E0 * nat) (i:nat) :  nat by wf  c call_lt :=
  f_star (alpha, 0) i := i;
  f_star (alpha, 1) i
    with E0_eq_dec alpha Zero :=
    { | left _ => S i ;
      | right nonzero
          with Utils.dec (Limitb alpha) :=
          { | left _ => f_star (Canon alpha i,1) i ;
            | right notlimit =>
              f_star (Pred alpha, i) i}};
  f_star (alpha,(S (S n))) i :=
    f_star (alpha, 1) (f_star (alpha, S n) i).

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

Definition f_  alpha i := f_star (alpha, 1) i.

(** ** We get the "usual" equations for [f_]  *)

(** *** Relations between [f_star] and [f_] *)

Lemma f_star_zero_eqn : forall alpha i, f_star (alpha, 0) i = i.
Proof.
  intros; now rewrite f_star_equation_1.
Qed.

Lemma Fstar_S : forall alpha n i, f_star (alpha, S (S n)) i =
                                  f_ alpha  (f_star (alpha,S  n) i).
Proof.  
  unfold f_; intros; now rewrite f_star_equation_3.
Qed.

Lemma f_eq2 : forall alpha i,
    Succb alpha -> 
    f_ alpha i = f_star (Pred alpha,  i) i.
Proof.
  unfold f_; intros; rewrite f_star_equation_2.
  destruct (E0_eq_dec alpha Zero).
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
  - intros i.   now rewrite Fstar_S.  
Qed.

Lemma f_star_iterate : forall alpha n i,
    f_star (alpha, n) i =  iterate (f_ alpha) n i.
Proof.
  induction n; intro i; simpl.
  - now rewrite f_star_zero_eqn. 
  - specialize (IHn i); rewrite f_star_Succ in *;  now rewrite <- IHn.
Qed.


(** *** Usual equations for [f_] *)

Lemma f_zero_eqn : forall i, f_ Zero i = S i.
Proof.
  intro i. unfold f_; rewrite f_star_equation_2.
  destruct (E0_eq_dec Zero Zero).
  - now cbn.
  - now destruct n.
Qed.


Lemma f_lim_eqn : forall alpha i,  Limitb alpha ->
                                   f_ alpha i = f_ (Canon alpha i) i.
Proof.
  unfold f_; intros. rewrite f_star_equation_2.
  destruct (E0_eq_dec alpha Zero).
  - now  destruct (Limit_not_Zero  H).
  - cbn; destruct (Utils.dec (Limitb alpha)) .
    + cbn; auto.
    + red in H. rewrite e in H; discriminate.
Qed.


Lemma f_succ_eqn : forall alpha i,
    f_ (Succ alpha) i = iterate (f_ alpha)  i i.
Proof with auto with E0.
  intros;rewrite f_eq2,  f_star_iterate ...
  -   rewrite Pred_of_Succ.
      reflexivity.
Qed.

(** ** First steps of Wainer hierarchy *)


(** performs an induction only on the occ1-th and occ2_th occurrences of n *)

Tactic Notation "undiag2" constr(n) integer(occ1) integer(occ2) :=
  let n' := fresh "n" in
  generalize n at occ1 occ2; intro n'; induction n'.

Lemma LF1 : forall i,  f_ 1 i = (2 * i).
Proof.
  intro i; unfold Fin; rewrite FinS_Succ_eq, f_succ_eqn.
  - replace (2 * i) with (i + i).
    + generalize i at 2 4; induction i.
      * cbn; trivial.
      * intro i0; rewrite iterate_rw, f_zero_eqn.  
        rewrite IHi; lia.
    + lia.
Qed. 

Lemma LF2 : forall i,  f_ 2 i = exp2 i * i.
Proof.
  intro i; ochange (Fin 2) (Succ 1); rewrite f_succ_eqn.
  undiag2 i 1 3.
  -  intros. cbn;  intros; cbn.  repeat rewrite LF1. abstract lia. 
  - intros; simpl exp2; ring_simplify. simpl (2+n)%nat.
    rewrite iterate_S_eqn, LF1; abstract lia.
Qed.



Lemma f_alpha_0_eq : forall alpha: E0, f_ alpha 0 <= 1.
  intro alpha. pattern alpha; apply well_founded_induction with E0.Lt.
  - apply E0.Lt_wf.
  - clear alpha; intros alpha Halpha.
    destruct (Zero_Limit_Succ_dec alpha).
    destruct s.
    + subst alpha; now rewrite f_zero_eqn.
    +  rewrite f_lim_eqn;auto; unfold Canon; now rewrite f_zero_eqn. 
    +  destruct s; subst; rewrite f_succ_eqn; simpl. auto with arith.
Qed.




Goal forall alpha k,  H'_ (Phi0 alpha) k = f_ alpha k.
 intro alpha. pattern alpha; apply well_founded_induction with E0.Lt.
- apply E0.Lt_wf.
  - clear alpha; intros alpha Halpha.
    destruct (Zero_Limit_Succ_dec alpha).
   destruct s.
   + subst.
     intros. 
     rewrite f_zero_eqn.
    Search (H'_ (Fin _)).
    replace (Phi0 Zero) with (Fin 1).
    rewrite H'_Fin.
     auto.
     now apply E0_eq_intro.
      + 
Abort.

(** Properties of [f_ alpha]  *)
(* begin hide *)

Section Properties.
  Record P (alpha:E0) : Prop :=
    mkP {
        PA : strict_mono (f_ alpha);
        PB : forall n, n < f_ alpha n;
        PC : forall n, f_ alpha (S n) <= f_ (Succ alpha) (S n);
        PD : dominates_from 2 (f_ (Succ alpha)) (f_ alpha);
        PE : forall beta n, Canon_plus n alpha beta -> 
                            f_ beta n <= f_ alpha n}.

  
  Section The_induction.

    (** Base step : (sequential) proof of (P 0) *)
    
    Lemma mono_f_Zero : strict_mono (f_ Zero).
    Proof. 
      intros n p H; repeat rewrite f_zero_eqn; auto with arith. 
    Qed. 

    Lemma Lt_n_f_Zero_n : forall n:nat, n < f_ Zero n. 
    Proof. intros n ; rewrite f_zero_eqn.  auto with arith. Qed.

    Lemma f_One_Zero_dom : dominates_from 2 (f_ 1) (f_ Zero).
    Proof.
      red;intros.
      rewrite f_zero_eqn. rewrite LF1. abstract lia.
    Qed.

    Local Hint Resolve f_One_Zero_dom mono_f_Zero Lt_n_f_Zero_n : T1.

   (* Lemma f_One_Zero_ge :  f_ Zero <<= f_ 1.
    Proof.
      intro n; destruct n;
        rewrite f_zero_eqn, LF1. abstract lia.  
    Qed. 
*)
    (* Local Hint Resolve  f_One_Zero_ge : T1. *)

    Lemma PZero : P Zero.
    Proof. 
      split; auto with T1; ord_eq  (Succ Zero) (Fin 1).
      all: try (rewrite H;auto with T1).
      unfold Canon_plus. Search (f_ Zero). intro; rewrite f_zero_eqn, LF1.
      lia.
      intros beta n H0;
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

      Remark R1 : strict_mono (f_ alpha).
      Proof.
        destruct (Halpha beta).
        subst alpha; apply Lt_Succ.
        red; intros.
        subst alpha.
        repeat rewrite f_succ_eqn.
        induction H.
        
        rewrite (iterate_S_eqn (f_ beta)  n).
        Search iterate.
        About iterate_mono.
        
        apply Lt.lt_le_trans with (f_ beta
                                      (iterate (f_ beta)  n n)).
        auto. 
        
        apply mono_weak; auto.
        
        apply Nat.lt_le_incl.
        apply iterate_mono;auto.
        
        
        transitivity (iterate (f_ beta) m m);auto.
        rewrite (iterate_S_eqn (f_ beta)  m).
        
        apply Lt.lt_le_trans with (iterate (f_ beta) m (S m)).
        apply iterate_mono;auto.
        apply Nat.lt_le_incl.
        apply PB0.
      Qed.

      (* ICI *)
      
      
      Remark RB : forall n, 0 < n -> n < f_ alpha n.
      Proof.
        subst  alpha.
        intros n Hn. 
        rewrite f_succ_eqn.
        destruct (Halpha beta).
        apply Lt_Succ.
        change n with (iterate (f_ beta) 0 n) at 1.
        apply iterate_lt;auto with arith.
      Qed.


      Remark RD : dominates_from 2 (f_ (Succ alpha)) (f_ alpha).
        generalize RB; intro RB'.
        rewrite alpha_def .
        
        destruct (Halpha beta).
        rewrite alpha_def ;apply Lt_Succ.
        intros n Hn.
        rewrite (f_succ_eqn (Succ beta)).
        change (f_ (Succ beta) n) with
            (iterate (f_ (Succ beta)) 1 n).
        Search (iterate ?f _ ?x < iterate ?f _ ?x).


        apply iterate_lt_from with 2.
        rewrite <- alpha_def; apply R1.
        Search (f_ (Succ _)).
        
        intros; rewrite  f_succ_eqn.
        change n0 with (iterate (f_ beta) 0 n0) at 1.
apply iterate_lt_from with 2.
auto. 
intros;apply PB0.
 auto with arith. 
auto.
auto. 
auto.
Qed. 



      Remark RE : forall beta n, Canon_plus n alpha beta -> 
                                 f_ beta n <= f_ alpha n.
      Proof.
        destruct n. intro.  rewrite f_alpha_0_eq. Check   (f_alpha_0_eq alpha).
        reflexivity.
        intros. 
        transitivity (f_ beta (S n)).
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

      Remark RC : f_ alpha <<= f_ (Succ alpha).
      Proof.
        intro n; destruct n.
        repeat rewrite f_alpha_0_eq. auto with arith.
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


      Remark RBlim : forall n, n < f_ alpha n.
        intro n.
        rewrite f_lim_eqn.
        destruct (Halpha (Canon alpha n)).
        apply Canon_lt. 
        now apply Limit_not_Zero.
        auto.
        auto.
      Qed.
      
      Remark RAlim : strict_mono (f_ alpha).
      Proof.
        red;intros m n H; destruct m.
        - rewrite (f_lim_eqn alpha n);auto.
          rewrite f_alpha_0_eq. (* bad name *)
          destruct n. inversion H.
          unfold Canon.
          apply Nat.le_lt_trans with (S n).
          auto with arith.
          destruct (Halpha (CanonS alpha n)).
          apply CanonS_lt. 
          now apply Limit_not_Zero.
          now apply PB0.
          
        - destruct n. inversion H.
          rewrite (f_lim_eqn alpha (S n));auto.
          rewrite (f_lim_eqn alpha (S m));auto.
          assert (Canon_plus 1 (Canon alpha (S n)) (Canon alpha (S m))).
          apply KS_thm_2_4_E0; auto.
          auto with arith.
          assert (Canon_plus (S n) (Canon alpha (S n)) (Canon alpha (S m))).
          eapply Cor12_E0 with 0; auto with arith.
          apply canonS_limit_mono; auto with T1.
          auto with arith.
          auto with E0.
          auto with arith.
          apply Nat.le_lt_trans with (f_ (Canon alpha (S n)) (S m) ).
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



      Remark RClim : f_ alpha <<= f_ (Succ alpha).
      Proof.
        intro n; destruct n.
        - repeat rewrite f_alpha_0_eq; auto with arith.
        -  apply Nat.lt_le_incl;  rewrite f_succ_eqn.
           change (f_ alpha (S n)) with (iterate (f_ alpha) 1 (S n)).
           apply iterate_lt. 
           +  apply RAlim.
           +  red;intros; apply RBlim.
           +  auto with arith.
      Qed.

      Remark RDlim : dominates_from 1 (f_ (Succ alpha)) (f_ alpha).
      Proof.
        red;intros; rewrite f_succ_eqn.
        change (f_ alpha p) with (iterate (f_ alpha) 1 p);
          apply iterate_lt. 
        -   apply RAlim.
        -   red;intros; apply RBlim.
        -   auto with arith.
      Qed.

      Remark RElim : forall beta n, Canon_plus n alpha beta -> 
                                    f_ beta n <= f_ alpha n.
      Proof.
        destruct n.
        - now  repeat rewrite f_alpha_0_eq. 
        - intros H;  destruct (Canon_plus_first_step_lim  Hlim H).
          +  rewrite (f_lim_eqn alpha _).
             * now rewrite H0.
             * auto.
          +  rewrite (f_lim_eqn alpha _);auto.
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

(* end hide *)


Theorem f_alpha_mono alpha : strict_mono (f_ alpha).
Proof. now  destruct  (TH_packed alpha). Qed.


Theorem f_alpha_ge_S alpha : forall n, n < f_ alpha n.
Proof. now  destruct  (TH_packed alpha). Qed.

Corollary f_alpha_positive alpha :
  forall n, 0 < f_ alpha n.
Proof.
  intro n; apply Lt.le_lt_trans with n; auto with arith.
  apply f_alpha_ge_S.
Qed.

Theorem f_alpha_Succ_le alpha : f_ alpha <<= f_ (Succ alpha).
Proof. now  destruct  (TH_packed alpha). Qed.

Theorem f_alpha_dom alpha : dominates_from 1 (f_ (Succ alpha)) (f_ alpha).
Proof. now  destruct  (TH_packed alpha). Qed.

(** [f_] is not mononotonous in [alpha] in general. 
      Nevertheless, this lemma may help (from [KS]) *)


Theorem f_restricted_mono_l alpha : forall beta n, Canon_plus n alpha beta -> 
                                            f_ beta n <= f_ alpha n.
Proof. now  destruct  (TH_packed alpha). Qed.





Lemma LF2_0 : dominates_from 0 (f_ 2) (fun i => exp2 i * i).
Proof.
  red. intros ; apply LF2 ; auto.  
Qed.


Lemma LF3_2  : dominates_from 2  (f_ 3) (fun  n => iterate exp2 (S n) n).
Proof.  
  intros p H; assert (H0:= LF2_0).
  ochange (Fin 3) (Succ 2); rewrite f_succ_eqn.
  eapply iterate_dom_prop; eauto with arith. 
  - apply exp2_ge_S.
  - apply exp2_mono.
  - apply f_alpha_mono.
  - red; intros; transitivity (exp2 p0 * p0)%nat; auto.
    {  rewrite <- Nat.mul_1_r at 1; apply Nat.mul_lt_mono_pos_l; auto.
       apply exp2_positive.
    }
    apply LF2_0; abstract lia.
Qed.

(** From Ketonen and Solovay, page 284, op. cit. *)

Section Compatibility_f_dominates.

  Variables alpha beta : E0.
  Hypothesis H_beta_alpha : Lt beta alpha.

  (* begin hide *)
  Section case_eq.
    Hypothesis Heq : alpha = Succ beta.

    Fact F2 : forall i, (1 <= i ->  f_ beta i < f_ alpha i)%nat.
    Proof.
      subst alpha; intros i H; apply (f_alpha_dom beta i H).
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

    Fact F7 : forall i, (S n < i -> f_ (Succ beta) i <= f_ alpha i)%nat.
    Proof.
      intros; apply  f_restricted_mono_l.  
      apply F6; auto.
    Qed.

    Fact F8 : forall i, (S n < i -> f_ beta i < f_ (Succ beta) i)%nat.
    Proof.
      intros i H; apply  (f_alpha_dom beta i); abstract lia.
    Qed.

    Fact F9 : forall i, (S n < i -> f_ beta i < f_ alpha i)%nat.
    Proof.
      intros; eapply Nat.lt_le_trans.
      eapply F8;eauto.
      apply F7;auto.
    Qed.

  End case_lt.

  (* end hide *)
  
  Lemma f_mono_l_0 : forall n, Canon_plus (S n) alpha beta ->
                               forall i, (S n < i -> f_ beta i < f_ alpha i)%nat.
  Proof.
    assert (Le (Succ beta) alpha) by (now apply Lt_Succ_Le).
    assert ({alpha = Succ beta}+{Lt (Succ beta) alpha}). {
      rewrite <- lt_Succ_inv in H.
      apply Lt_Succ_Le in H; destruct (E0.le_lt_eq_dec  H); auto.
    }
    destruct H0.
    - intros; apply F2; [trivial | lia].
    - intros; eapply F9; eauto.
  Qed.

  
  
  Lemma f_mono_l: dominates (f_ alpha) (f_ beta).
  Proof.
    destruct (Lemma2_6_1_E0  H_beta_alpha) as [i Hi].
    exists (S (S i)); intros p Hp; apply f_mono_l_0 with i;  auto.
  Qed.

  
End Compatibility_f_dominates.


(** * Comparison with the Hardy hierarchy 
       
      [(f_ alpha (S n) <= H_ (Phi0 alpha) (S n))]
*)



Section H_F.
  
Let P (alpha: E0) := forall n,  (f_ alpha (S n) <= H_ (Phi0 alpha) (S n))%nat.

 Variable alpha: E0.

 Hypothesis IHalpha : forall  beta, beta o< alpha -> P beta.

 Lemma HF0 : P Zero.
 Proof.
   intro n; rewrite f_zero_eqn.
   replace (Phi0 Zero) with (Fin 1).
   - now rewrite H_Fin.
   - now apply E0_eq_intro.
 Qed.

 Lemma HFsucc : Succb alpha -> P alpha.
 Proof.
   intro H; destruct (Succb_Succ _ H) as [beta Hbeta]; subst.
   intro n; rewrite H_Phi0_succ.
   unfold H_succ_fun; rewrite f_succ_eqn.
   specialize (IHalpha beta (Lt_Succ beta));  unfold P in IHalpha.
   - apply iterate_mono_1 with 1.
     + apply f_alpha_mono.
     + intro k; apply f_alpha_ge_S.
     + intros; destruct n0.
       * lia.
       * apply IHalpha.
     +lia.
 Qed.


  (** The following proof is far from being trivial.
      It uses some lemmas from the Ketonen-Solovay machinery *)
 
  Lemma HFLim : Limitb alpha -> P alpha.
  Proof.
    intros Halpha n; rewrite H_eq3.
    - rewrite CanonS_Canon;
      rewrite CanonS_Phi0_lim; [| trivial].
      rewrite f_lim_eqn, CanonS_Canon; auto.
      + transitivity (H_ (Phi0 (CanonS alpha n)) (S n)).
        *  apply IHalpha.
           apply CanonS_lt.
           now apply Limit_not_Zero.
        * (** Not trivial, since [H_ ] is not monotonous ! *)
          
          apply H_restricted_mono_l.
          
          red; cbn; apply KS_thm_2_4_lemma5.
          -- apply Cor12_1 with 0.
           ++ apply nf_canonS, cnf_ok.
           ++ apply canonS_limit_mono.
              ** apply cnf_ok.
              ** destruct alpha; cbn; assumption. 
              ** auto with arith. 
           ++ auto with arith.
           ++ apply KS_thm_2_4.
              ** apply cnf_ok.
              ** destruct alpha; auto.
              ** auto with arith. 
          --  apply nf_canonS, cnf_ok.
          --  apply limitb_canonS_not_zero.
              ++ apply cnf_ok.
              ++ now destruct alpha.
    - apply Limitb_Phi0.
      apply Limit_not_Zero; auto. 
Qed.

End H_F.

(** Proof using transfinite induction (prepared in the previous section) *)

Lemma H_F alpha : forall n,  (f_ alpha (S n) <= H_ (Phi0 alpha) (S n))%nat.
Proof.
  pattern alpha; apply well_founded_induction with Lt.
  - apply Lt_wf.  
  -  clear alpha; intros alpha IHalpha.
     destruct (Zero_Limit_Succ_dec alpha) as [[Hzero | Hlim] | Hsucc].
    + subst; apply HF0.
    + apply HFLim; auto.
    + destruct Hsucc; subst; apply HFsucc.
      intros; apply IHalpha; auto.
      apply Succ_Succb.
  Qed.


(** * A variant (Lob-Wainer hierarchy) *)


Equations  f_star (c: E0 * nat) (i:nat) :  nat by wf  c call_lt :=
  f_star (alpha, 0) i := i;
  f_star (alpha, 1) i
    with E0_eq_dec alpha Zero :=
    { | left _ => S i ;
      | right nonzero
          with Utils.dec (Limitb alpha) :=
          { | left _ => f_star (Canon alpha i,1) i ;
            | right notlimit =>
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

Definition f_  alpha i := f_star (alpha, 1) i.

(** ** We get the "usual" equations for [f_]  *)

(** *** Relations between [f_star] and [f_] *)

Lemma f_star_zero_eqn : forall alpha i, f_star (alpha, 0) i = i.
Proof.
  intros; now rewrite f_star_equation_1.
Qed.

Lemma fstar_S : forall alpha n i, f_star (alpha, S (S n)) i =
                                  f_ alpha  (f_star (alpha,  S n) i).
Proof.  
  unfold f_; intros; now rewrite f_star_equation_3.
Qed.

Lemma f_eq2 : forall alpha i,
    Succb alpha -> 
    f_ alpha i = f_star (Pred alpha,  i) i.
Proof.
  unfold f_; intros; rewrite f_star_equation_2.
  destruct (E0_eq_dec alpha Zero).
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

Lemma f_zero_eqn : forall i, f_ Zero i = S i.
Proof.
  intro i. unfold f_; rewrite f_star_equation_2.
  destruct (E0_eq_dec Zero Zero).
  - now cbn.
  - now destruct n.
Qed.


Lemma f_lim_eqn : forall alpha i,  Limitb alpha ->
                                   f_ alpha i = f_ (Canon alpha i) i.
Proof.
  unfold f_; intros. rewrite f_star_equation_2.
  destruct (E0_eq_dec alpha Zero).
  - now  destruct (Limit_not_Zero  H).
  - cbn; destruct (Utils.dec (Limitb alpha)) .
    + cbn; auto.
    + red in H. rewrite e in H; discriminate.
Qed.


Lemma f_succ_eqn : forall alpha i,
    f_ (Succ alpha) i = iterate (f_ alpha) i i.
Proof with auto with E0.
  intros;rewrite f_eq2,  f_star_iterate ...
  -  now rewrite Pred_of_Succ.
Qed.

(** TODO : Study the equality f_ alpha i = Nat.pred (f_ alpha (S i)) *)


(*
Goal forall alpha i, f_ alpha i = Nat.pred (f_ alpha (S i)).
intro alpha.
pattern alpha; apply well_founded_induction with Lt.
- apply Lt_wf.
- clear alpha; intros alpha IHalpha.
  Search Succ Zero.
  destruct (Zero_Limit_Succ_dec alpha) as [[HZero | HSucc] | Hlim].
  + subst. intro i; now rewrite f_zero_eqn, f_zero_eqn.
  + intro i. rewrite f_lim_eqn, f_lim_eqn.
    rewrite IHalpha.
Abort.
 *)

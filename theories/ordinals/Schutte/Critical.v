(* Pierre Casteran, LaBRI,  University of  Bordeaux *)

(**

 We  adapt Schutte's definition of critical ordinals :

   - Cr(zero) = AP   (the set of additive principal ordinals )

   - if zero < alpha, then
       Cr(alpha) is the   intersection of all the sets of fixpoints
       of the ordering functions of Cr(beta) for beta < alpha.
*)


From Coq Require Import Arith Logic.Epsilon  Ensembles Classical.
From hydras Require Export Schutte_basics  Ordering_Functions
     Countable  Schutte.Addition AP CNF Well_Orders MoreEpsilonIota.

Set Implicit Arguments.


(**  Let us define a functional, the fixpoint of which we shall consider *)

(* begin snippet CrDef *)

Definition Cr_fun : forall alpha : Ord,
    (forall beta : Ord, beta < alpha -> Ensemble Ord) ->
    Ensemble Ord
  :=
    fun (alpha :Ord)
        (Cr : forall beta,
            beta < alpha -> Ensemble Ord)
        (x : Ord) => (
        (alpha = zero /\ AP x) \/
        (zero < alpha /\
         forall beta (H:beta < alpha),
           In (the_ordering_segment (Cr beta H)) x /\
           ord (Cr beta H) x = x)).

Definition Cr (alpha : Ord) : Ensemble Ord :=
  (Fix  all_ord_acc
        (fun (_:Ord) => Ensemble Ord) Cr_fun) alpha.

(* end snippet CrDef *)

(* begin snippet Gamma0Def *)

Definition strongly_critical alpha := In (Cr alpha) alpha.

Definition maximal_critical alpha : Ensemble Ord :=
  fun gamma =>
    In (Cr alpha) gamma /\
    forall xi, alpha < xi -> ~ In (Cr xi) gamma.

Definition Gamma0 := the_least strongly_critical.

(* end snippet Gamma0Def *)

(**  See Gamma0.Gamma0.phi *)

(* begin snippet phiDef *)

Definition phi (alpha : Ord) : Ord -> Ord
    :=  ord (Cr alpha).

Definition A_ (alpha : Ord) : Ensemble Ord :=
  the_ordering_segment (Cr alpha).

(* end snippet phiDef *)


Lemma Cr_extensional :
  forall (x:Ord)
         (f g : forall y : Ord, y < x -> (fun _ : Ord => Ensemble Ord) y),
    (forall (y : Ord) (p : y < x), f y p = g y p) ->
    ((Cr_fun  f  :Ensemble Ord) =  (Cr_fun  g :Ensemble Ord)).
Proof.
  intros x f g  H0; apply Extensionality_Ensembles; split.
  -  unfold Cr_fun;red; unfold In;intros x0 H;  case H.
     + auto.
     +  right; split.
        *  case H1; auto.
        *  intros beta H2;  decompose [and] H1.
           rewrite <- (H0 beta H2); auto.
  -  unfold Cr_fun;red; unfold In;intros x0 H;  case H.
     + auto.
     + right; split.
       * case H1;auto.
       * intros beta H2;  decompose [and] H1;
           rewrite (H0 beta H2); case (H4 beta H2); auto.
Qed.


Lemma Cr_equation (alpha : Ord) :
  Cr  alpha =
  Cr_fun
    (fun (y : Ord) (h : y < alpha) =>  Cr y).

Proof.
  generalize (@Fix_eq Ord  lt  all_ord_acc
                      (fun _ : Ord => Ensemble Ord));
    intros H; apply  (H Cr_fun Cr_extensional alpha).
Qed.


Lemma Cr_inv (alpha x : Ord):
  Cr alpha x ->
  ((alpha = zero /\ (Cr  alpha x <-> AP x)) \/
   (zero < alpha /\
    (forall beta (H:beta < alpha),
        A_ beta  x /\  ord (Cr  beta ) x = x))).
Proof.
  rewrite (Cr_equation alpha);  unfold Cr_fun at 1.
  intros H;  case H;auto.
  case H;intros H0 _.
  +  left; split.
     * destruct H0; auto.
     * split.
       {  intro H1; destruct H0;auto. }
       { intros H1; left; auto. }
  +  auto.
Qed.


Lemma Cr_zero : forall x, AP x -> Cr zero  x.
Proof.
  intros x  H0; rewrite Cr_equation;  left; auto.
Qed.

Lemma Cr_pos : forall alpha,
    zero < alpha ->
    forall x : Ord ,
      (forall beta (H:beta < alpha),
          A_  beta  x /\   ord (Cr  beta) x = x) ->
      Cr alpha x.
Proof.
  intros; rewrite Cr_equation; right . split; auto.
Qed.


Lemma Cr_zero_inv : forall x, Cr zero x -> AP x.
Proof.
  intros x H; destruct (Cr_inv zero x H) as  [[_ H1]  | [H2 H3]].
  -  tauto.
  -  destruct (lt_irrefl  H2).
Qed.

(* begin snippet CrZeroAP *)

Lemma Cr_zero_AP :  Cr zero = AP. (* .no-out *)
(*| .. coq:: none |*)
Proof.
  apply Extensionality_Ensembles;  split.
  - red; intros; red; apply Cr_zero_inv; auto.
  - red; intros;  apply Cr_zero; auto.
Qed.
(*||*)
(* end snippet CrZeroAP *)


Lemma Cr_pos_inv (alpha : Ord) :
  zero < alpha ->
  forall x,
    Cr alpha x ->
    (forall beta (H:beta < alpha), In (A_ beta) x /\ phi beta x = x).
Proof.
  intros H x H0 beta H1; case (Cr_inv alpha x H0).
  - destruct 1; subst alpha; case (@not_lt_zero beta);  auto.
  - destruct 1;  eauto.
Qed.

Lemma Cr_pos_iff (alpha : Ord) :
  zero < alpha ->
  forall x,
    (Cr alpha x <->
     (forall beta (H:beta < alpha), In (A_ beta) x /\ phi beta x = x)).
Proof.
  split.
  - intros; apply Cr_pos_inv with alpha; auto.
  - intros; apply Cr_pos; auto.
Qed.

Lemma A_Cr (alpha beta:Ord) : In (A_ alpha) beta ->  phi alpha beta = beta ->
                             In (Cr alpha) beta.
  unfold A_; intros H H0; rewrite <- H0.
  unfold phi; destruct (ord_ok (Cr alpha)).
  specialize (OF_total _ H); auto.
Qed.

Lemma Cr_lt : forall alpha beta,
    beta < alpha -> forall x, Cr alpha x -> Cr beta x.
Proof.
  intros alpha beta H x H0.
  assert (H1 : zero < alpha).
  { apply le_lt_trans with beta; auto with schutte. }
  specialize (Cr_pos_inv H1);  intro H2; specialize (H2 _ H0 _ H).
  apply A_Cr; tauto.
Qed.

Lemma Cr_incl (alpha beta : Ord) (H :beta <= alpha) :
  Included (Cr alpha)  (Cr beta).
Proof.
  case (le_disj H).
  -  intro;subst beta; auto with schutte.
  -  red; intros; apply Cr_lt with alpha; auto.
Qed.


Lemma phi0_well_named : forall alpha, phi0 alpha = phi 0 alpha.
Proof.
  intro alpha;unfold phi, finite;  now  rewrite Cr_zero_AP.
Qed.

Lemma Cr_1_equiv (alpha : Ord):
  Cr 1 alpha <->  AP alpha /\ phi0 alpha = alpha.
Proof.
  generalize (Cr_pos_inv  (alpha := F 1)).
  intro H;  assert (H01 : zero < F 1).
  { simpl;  apply lt_succ; split. }
  split.
  +  intros H0;  generalize (H H01 alpha H0).
     intros H1;  generalize (H1 zero H01).
     intros (H5,H6);  split.
     *  rewrite <- H6; rewrite <- phi0_well_named.
       apply AP_phi0.
     *  unfold _phi0;  replace AP with (Cr zero); auto.
        apply Extensionality_Ensembles.
        split.
        { red; red; intros x H2.
          red;  intros;  apply Cr_zero_inv;  auto.
        }
        {  red;  red;  intros;apply Cr_zero;  auto.
        }
  + intros (H2,H3); apply Cr_pos;  auto.
    split.
    *  intros;  assert (beta=zero).
       {  simpl in H0;  generalize (lt_succ_le_2 zero  H0).
          intro H4;rewrite (le_alpha_zero H4); trivial.
       }
       subst beta;  red.
       rewrite Cr_zero_AP, AP_o_segment.
       split.

    *   rewrite phi0_well_named in H3.
        assert (beta=zero).
        { simpl in H0;  generalize (lt_succ_le_2 zero  H0).
          intro H4;rewrite (le_alpha_zero H4); auto.
        }
        subst beta;  unfold phi in H3;  auto.
Qed.


(* begin snippet epsilon0Cr1 *)

Lemma epsilon0_Cr1 : In (Cr 1) epsilon0. (* .no-out *)
(*| .. coq:: none |*)
Proof.
  red;rewrite Cr_1_equiv; split.
  - apply epsilon0_AP.
  - apply epsilon0_fxp.
Qed.
(*||*)

(* end snippet epsilon0Cr1 *)

(** Lemma 5, p 82 of Schutte's book *)

(* TO DO : make the proof cleaner and shorter !!!! *)

Section Proof_of_Lemma5.
  Let P (alpha:Ord) := Unbounded (Cr alpha) /\ Closed (Cr alpha).


  Lemma Lemma5_0 : P zero.
  Proof.
    red;rewrite Cr_zero_AP; split.
    - apply AP_unbounded.
    - apply AP_closed.
  Qed.

  Section Alpha_positive.
    Variable alpha : Ord.
    Hypothesis alpha_pos : zero < alpha.
    Hypothesis IHalpha : forall xi, xi < alpha -> P xi.


    Section Proof_unbounded.
      Variable beta : Ord.

      Fixpoint gamma_ (n:nat) : Ord :=
        match n with
          O => succ beta
        | S n => sup
                   (fun (y : Ord) =>
                      exists xi: Ord, xi  < alpha /\
                                      y = phi xi (gamma_ n))
        end.

      Let gamma := omega_limit gamma_.


      Lemma Lemma5_01 : beta < gamma.
      Proof.
        unfold omega_limit in gamma.
        apply lt_le_trans with (gamma_ 0).
        simpl;  auto with schutte.
        unfold gamma;  apply sup_upper_bound.
        apply seq_range_countable.
        now exists 0.
      Qed.

      Lemma Lemma5_02 : forall xi, xi < alpha ->
                                    phi xi gamma = gamma.
        intros xi Hxi.
        assert (forall n,  phi xi (gamma_ n) <= gamma).
        {
          intro n; apply le_trans with (gamma_ (S n)).
          cbn; apply sup_upper_bound.
          generalize (@countable_image _ _
                                       (members alpha)
                                       (fun x =>  phi x (gamma_ n))).
          intros H;
            apply CountableTypes.countable_downward_closed with
                (image (members alpha)
                       (fun x =>  phi x  (gamma_ n))).
          apply H.
          apply countable_members.
          destruct 1.
          destruct H.
          apply countable_members.
          exists x0.
          split; auto.
          destruct H0; auto.
          destruct H0;auto.
          exists xi; split; auto.
          unfold gamma;  apply sup_upper_bound.
          apply seq_range_countable.
          exists (S n); auto.
        }
        assert (sup (seq_range (fun n => phi xi (gamma_ n))) <= gamma).
        {
          apply sup_least_upper_bound.
          apply seq_range_countable.
          intros y [n [_ Hn]].
          subst;  apply H.
        }

        assert (phi xi gamma <= gamma).
        { unfold gamma at 1; unfold omega_limit.
          assert (continuous (phi xi) ordinal (Cr xi)).
          { apply Th_13_5_2.

            replace ordinal with (the_ordering_segment (Cr xi)).
            apply ord_ok.
            apply segment_unbounded.
            eapply ordering_function_seg with (Cr xi).
            exists (phi xi).
            apply ord_ok;  auto.
            assert (Unbounded (Cr xi)) by(now destruct (IHalpha  Hxi)).
            rewrite
              (@ ordering_unbounded_unbounded (A_ xi) (Cr xi) (phi xi)) in H1.
            auto.
            apply ord_ok.
            destruct (IHalpha Hxi); auto.
          }
          destruct H1.
          destruct H2.
          rewrite <- H3.
          -  apply sup_least_upper_bound.
             apply countable_image.
             apply seq_range_countable.
             intros y [x [H4 H5]].
             destruct H4 as [z [_ H6]].  subst x y; apply H.
          -  split.
          -  exists (gamma_ 0), 0;auto.
          -  apply seq_range_countable.
        }
        assert (gamma <= phi xi gamma).
        {
          eapply ordering_le.
         -  apply ord_ok.
         -  assert (Unbounded (Cr xi)) by ( now destruct (IHalpha  Hxi)).
            replace (the_ordering_segment (Cr xi)) with ordinal.
          + split.
          + rewrite  (@ordering_unbounded_unbounded (A_ xi) (Cr xi) (phi xi))
            in H2.
           *  unfold A_ in H2;  symmetry;  apply segment_unbounded; auto.
              apply segment_the_ordering_segment; auto.
           *  apply ord_ok.
        }
        apply le_antisym; auto.
      Qed.


      Lemma Lemma5_03 : In (Cr alpha) gamma.
      Proof.
        red;  apply Cr_pos; auto.
        intros xi Hxi;  unfold P in IHalpha; split.
        - red; assert (Unbounded (Cr xi)) by (now destruct (IHalpha  Hxi)).
          rewrite (@ ordering_unbounded_unbounded (A_ xi) (Cr xi) (phi xi))
          in H.
        replace (the_ordering_segment (Cr xi)) with ordinal .
        + split.
        + symmetry; apply segment_unbounded.
          * eapply ordering_function_seg with (Cr xi).
            exists (phi xi); apply ord_ok; auto.
          * auto.
        + apply ord_ok.
       - apply Lemma5_02; auto.
      Qed.

      Remark A_full : forall xi, xi < alpha -> A_ xi = ordinal.
        unfold A_; intros.
        replace (the_ordering_segment (Cr xi)) with ordinal .
        split.
        symmetry; apply segment_unbounded.
        eapply ordering_function_seg with (Cr xi).
        unfold the_ordering_segment, the.
        apply iota_ind.
        apply ordering_segment_ex_unique.
        destruct 1; auto.
        rewrite   <-  (@ ordering_unbounded_unbounded (A_ xi) (Cr xi) (phi xi)).
        destruct (IHalpha H);auto.
        apply ord_ok.
      Qed.



      Lemma Lemma5_04 : exists gamma,  In (Cr alpha) gamma /\ beta < gamma.
        exists gamma; split.
        apply Lemma5_03.
        apply Lemma5_01.
      Qed.

    End Proof_unbounded.


    Lemma Lemma5_1 : Unbounded (Cr alpha).
      intros beta; apply Lemma5_04. Qed.


    Section closedness.
      Variable M : Ensemble Ord.
      Hypothesis HM : Inhabited M.
      Hypothesis CM : countable M.
      Hypothesis IM : Included  M (Cr alpha).




      Lemma Lemma5_2 : forall xi eta,  xi < alpha ->
                                        In M eta  ->
                                        phi xi eta = eta.
      Proof.
        intros.
        Check (Cr_pos_iff alpha_pos).
        assert (Cr alpha eta).
        now apply IM.
        rewrite (Cr_pos_iff alpha_pos) in H1.
        now destruct (H1 _ H).
      Qed.



      Lemma Lemma5_7 : In (Cr alpha) (sup M).
      Proof.
        red; apply Cr_pos; auto.
        intros xi H; split.
        rewrite (A_full H). split.
        assert (continuous (phi xi) ordinal (Cr xi)).
        { apply Th_13_5_2.
          replace ordinal with (the_ordering_segment (Cr xi)).
          apply ord_ok.
          apply segment_unbounded.
          eapply ordering_function_seg with (Cr xi).
          exists (phi xi); apply ord_ok.
          assert (Unbounded (Cr xi)).
          now destruct (IHalpha  H).
          rewrite (@ ordering_unbounded_unbounded (A_ xi) (Cr xi) (phi xi))
            in H0.
          auto.
          apply ord_ok.
          destruct (IHalpha H); auto.
        }
        destruct H0.
        destruct H1.
        unfold phi in H2.
        rewrite <- H2.
        f_equal; apply Extensionality_Ensembles.
        split.
        intro x.
        destruct 1.
        destruct H3.
        subst; fold (phi xi x0); rewrite Lemma5_2; auto.
        intros x Hx;   exists x; split; auto.
        fold (phi xi x); rewrite Lemma5_2; auto.
        split.
        auto.
        auto.
      Qed.


    End closedness.


    Lemma induct_step : P alpha.
      split.
      - apply Lemma5_1.
      - red; intros; apply Lemma5_7; auto.
    Qed.

  End Alpha_positive.

  Lemma Lemma5 : forall alpha, P alpha.
    intro alpha; apply transfinite_induction; red.
    clear alpha; intro alpha;  destruct (zero_or_positive alpha).
    subst; intros _; apply Lemma5_0.
    intro; apply induct_step; auto.
  Qed.

End Proof_of_Lemma5.

(* begin snippet Lemma5 *)

Theorem Unbounded_Cr alpha : Unbounded (Cr alpha). (* .no-out *)
(*| .. coq:: none |*)
Proof.
  now destruct (Lemma5 alpha).
Qed.
(*||*)

Theorem Closed_Cr alpha : Closed (Cr alpha). (* .no-out *)
(*| .. coq:: none |*)
Proof.
  now destruct (Lemma5 alpha).
Qed.
(*||*)

(* end snippet Lemma5 *)

Theorem Th13_8 alpha : normal (phi alpha) (Cr alpha).
Proof.
  eapply TH_13_6R with (A_ alpha).
  apply ord_ok.
  apply Closed_Cr.
  apply Unbounded_Cr.
Qed.


Corollary Th13_8_1 alpha : A_ alpha = ordinal.
Proof.
  destruct Th13_8 with alpha.
  eapply A_full with (succ alpha).
  - intros; apply Lemma5.
  - auto with schutte.
Qed.

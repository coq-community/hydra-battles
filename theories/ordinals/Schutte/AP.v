

(** * Additive principal ordinals *)

(** Pierre Casteran, LaBRI, Universite de Bordeaux *)

  
(**

In this library, we define the exponential of basis omega, also called [phi0].

In fact,  #<math> &omega; <sup> &alpha; </sup> </math># , written  [phi0 alpha] in Coq, 
 is defined as the [alpha]-th _additive principal_ ordinal. 

 *)

(* begin hide *)
From Coq Require Import Arith  Logic.Epsilon  Ensembles  Lia.
From hydras Require Export Countable  Schutte_basics
     Ordering_Functions.
Import  PartialFun  MoreEpsilonIota .
From hydras Require Export Schutte.Addition  Well_Orders.


Set Implicit Arguments.

(* end hide *)

(** ** Main Definitions

 *** Additive principal ordinals 
 *)

Definition AP : Ensemble Ord :=
  fun alpha => 
    zero < alpha /\
    (forall beta, beta < alpha ->  beta + alpha = alpha).

(**  *** Exponential of basis omega
 *)

Definition _phi0 := ord AP.
Notation "'phi0'" := _phi0 : schutte_scope.

Notation "'omega^'" := phi0 (only parsing) : schutte_scope.


(**  *** Omega-towers
 *)

Fixpoint omega_tower (i : nat) : Ord :=
  match i with
    0 =>  1
  | S j => phi0 (omega_tower j)
  end.

(** *** The limit ordinal [epsilon0] 
 *)

Definition epsilon0 := omega_limit omega_tower.

(** ** Proofs, proofs, proofs ... *)

(** ** About additive principals *)

Lemma AP_one : In AP 1.
Proof with auto with schutte.
  split.
  -  simpl (F 1) ...
  -  simpl (F 1); intros beta H.
     assert (H0: beta <= zero).
     { apply lt_succ_le_2 ... }
     rewrite (le_alpha_zero H0), zero_plus_alpha...
Qed.

(** [F 1] is the least additive principal *)

Lemma least_AP :least_member  lt AP 1. 
Proof with auto with schutte.
  repeat split ...
  - simpl (F 1) ...
  - intros beta H;  assert (beta = zero).
    { simpl (F 1) in H; apply le_alpha_zero,  lt_succ_le_2 ...
    }
    subst beta; rewrite zero_plus_alpha ...
  - intros x  H0; tricho x (F 1) H3 ...
    simpl (F 1) in H3; assert (x = zero).
    { apply le_alpha_zero, lt_succ_le_2 ... }
    subst x; destruct H0; case (@lt_irr zero) ...
    subst x; left; trivial.
    right; auto.
Qed.



Lemma AP_omega : In AP omega.
Proof with auto with schutte.
  repeat split.
  - apply lt_trans with (F 1).
    +  simpl (F 1) ...
    + apply finite_lt_omega.
  - intros beta H; case (@lt_omega_finite _  H).
    intros;subst beta;apply finite_plus_infinite ...
Qed.


Hint Resolve zero_lt_omega : schutte.

Lemma AP_finite_eq_one : forall n: nat, AP n -> n = 1.
Proof with auto with schutte.
  intro n;  case n.
  -  inversion 1.
     simpl in H0; case (@lt_irr zero);auto.
  -  intro n0;case n0; trivial.
     inversion_clear 1.
     generalize (H1 (F 1)); intros; absurd (F 1 + F (S (S n1)) = F (S (S n1))).
     +  rewrite <- plus_FF;simpl; intro H2.
        case (@lt_irr (succ (succ (F n1)))).
        pattern (succ (succ (F n1))) at 2; rewrite <- H2 ...
     + apply H, finite_mono; auto with arith.
Qed.

(** Thus, omega is the second additive principal *)

Lemma omega_second_AP :
  least_member   lt 
                 (fun alpha => 1 < alpha /\ In AP alpha)
                 omega.
Proof with auto with schutte.
  split  ...
  split ...
  - apply finite_lt_omega.
  -  apply AP_omega.
  -  intros x  H0.  case (@trichotomy x omega).  
     intro H1.
     case (lt_omega_finite  H1).
     intros; subst x.
     destruct  H0 as [H2 H3];     generalize (AP_finite_eq_one _ H3).
     intro;subst x0;now destruct  (@lt_irr (F 1)).
     auto.
     red.
     intuition.
Qed.




Lemma AP_plus_closed (alpha beta gamma : Ord): 
  In AP alpha ->   beta < alpha -> gamma < alpha ->
  beta + gamma < alpha.
Proof with auto with schutte.
  intros  H  H0 H1; case H;  intros H2 H3.
  generalize (@plus_mono_r  beta gamma alpha); intro H4.
  replace alpha with (beta+alpha) ...
Qed.

Lemma AP_mult_Sn_closed (alpha beta: Ord)  :
  AP alpha -> beta < alpha -> forall n,  mult_Sn beta n  < alpha.
  intros H H0; induction n.
  - now simpl.
  -   simpl. now  apply AP_plus_closed.
Qed.

Lemma AP_mult_fin_r_closed  (alpha beta: Ord)  :
  AP alpha -> beta < alpha -> forall n,  beta * n  < alpha.
Proof.
  destruct n.
  - simpl; eapply le_lt_trans ; eauto with schutte.
  - simpl; now apply AP_mult_Sn_closed.
Qed.

(* begin hide *)

Section AP_Unbounded.
  Variable alpha : Ord.
  
  Let seq := (fix seq (n:nat)  := 
                match n with 0 => succ alpha
                        | S p => (seq p) + (seq p)
                end).
  

  Let beta := omega_limit seq.

  Remark mono_seq : forall i, seq i < seq (S i).
  Proof with eauto with schutte.
    induction i.
    - simpl;  pattern (succ alpha) at 1 ...
      rewrite <- alpha_plus_zero ...
      apply plus_mono_r ...
    -   simpl in *.
        pattern (seq i + seq i) at 1; rewrite <- alpha_plus_zero ...
        apply plus_mono_r ...
  Qed.

  
  Lemma mono_seq2 : forall i j, (i < j)%nat -> seq i < seq j.
  Proof with auto.
    induction  1.
    - apply mono_seq ...
    - apply lt_trans with (seq m) ...
      apply mono_seq ...
  Qed.

  Lemma mono_seq_weak2 : forall i j, (i <= j)%nat -> seq i <= seq j.
  Proof with eauto with schutte.
    intros i j H; destruct (le_lt_eq_dec _ _ H).
    - right; now apply mono_seq2.
    - subst j;  left ...
      
  Qed.

  Hint Resolve mono_seq mono_seq2 : schutte.


  Remark alpha_lt_beta : alpha < beta.
  Proof with auto with schutte.
    apply lt_trans with (seq 0).
    -  simpl ...
    - unfold beta;  apply lt_omega_limit ...
  Qed.

  Remark zero_lt_beta : zero < beta.
  Proof with eauto with schutte.
    apply le_lt_trans with alpha ...
    apply alpha_lt_beta.
  Qed.

  Section ksi_fixed.
    Variable ksi: Ord.
    Hypothesis lt_ksi : ksi < beta.

    Remark lt_beta_exists : exists n, ksi < seq n.
    Proof. 
      case (@lt_omega_limit_lt_exists_lt ksi seq mono_seq); auto.   
      intros;exists x;auto.
    Qed.


    Let n := some (fun n => ksi < seq n).


    Remark ksi_plus_seq_n : forall (m:nat), (n <= m)%nat -> ksi + seq m <= beta.
    Proof with eauto with schutte.
      intros m H; apply le_trans with (seq (S m)).
      -  simpl; apply plus_mono_weak_l.
         +  apply le_trans with (seq n).
            *  right; unfold n, some;  
                 pattern (epsilon InHWit (fun n0 : nat => ksi < seq n0));
                 apply epsilon_ind.
               apply lt_beta_exists.
               elim H;  auto.
            *  destruct (le_lt_eq_dec n m H).
               right; apply mono_seq2;  auto.  
               subst m;left; split ...
      -  right;apply lt_omega_limit.
         + apply seq_mono_intro ...
    Qed.

    Lemma ksi_plus_seq_n' : forall (m:nat), ksi + seq m <= beta.  
    Proof.
      intro m ; destruct  (le_or_lt n m) as [H | H].
      -  apply ksi_plus_seq_n;auto.
      -   apply le_trans with (ksi + seq n).
          +  apply plus_mono_r_weak;auto.
             apply mono_seq_weak2;  auto with arith.
          +  apply ksi_plus_seq_n;  auto with arith.
    Qed.


    Lemma ksi_plus_beta : ksi + beta <= beta.
    Proof.
      unfold beta at 1; unfold omega_limit.
      rewrite alpha_plus_sup. 
      -  apply sup_least_upper_bound; eauto with schutte.
         +  apply R1 with ordinal (ge ksi).
            * apply plus_ordering; auto.
            *  apply seq_range_countable;auto.
            *  intro; split.
         +  intros y [z [H1 H2]]; subst y.
            destruct H1 as [x [_ H2]];  subst z; apply ksi_plus_seq_n'.
      - now exists (seq 0), 0.
      -  eauto with schutte.
    Qed.

    Lemma ksi_plus_beta_eq : ksi + beta = beta.
    Proof.
      apply le_antisym.
      -  apply ksi_plus_beta.
      -  apply le_plus_r;auto.
    Qed.

  End ksi_fixed.


  Lemma AP_unbounded_0 : alpha < beta /\ AP beta.
  Proof.
    split.
    -  apply alpha_lt_beta. 
    -  split.
       + apply zero_lt_beta.
       +  intros; apply ksi_plus_beta_eq; eauto with schutte.
  Qed.

End AP_Unbounded.

(* end hide *)

Theorem AP_unbounded : Unbounded AP.
Proof.
  intro x;  pose (H := AP_unbounded_0 x).
  exists (omega_limit
            (fix seq (n : nat) : Ord :=
               match n with
               | O => succ x
               | S p => seq p + seq p
               end)).
  now destruct H.
Qed.

(* begin hide *)

Section AP_closed.
  Variable M : Ensemble Ord.
  Hypothesis OM : Included M AP.
  Hypothesis inhM : Inhabited _ M.
  Hypothesis denM : countable M.
  
  Remark supM_gt0 : zero < |_| M.
  Proof.
    destruct inhM as [x H]; apply lt_le_trans with x.
    -  now  destruct (OM H).
    -  apply sup_upper_bound; auto with schutte.
  Qed.
  
  Lemma AP_sup : In AP (|_| M).
  Proof.
    split.
    - apply supM_gt0.
    -  intros ksi Hksi;
         destruct (@lt_sup_exists_lt M denM ksi Hksi)
         as [alpha [Malpha ksialpha]].
       apply le_antisym.
       +  rewrite alpha_plus_sup; auto.
          *  apply sup_mono; auto.
             { apply R1 with ordinal (ge ksi); auto.
               - apply plus_ordering; eauto with schutte.
               - split.
             }
             { intros x H; destruct  H as [beta [Mbeta ebeta]].
               case (@lt_or_ge beta alpha);auto with schutte.
               - exists alpha;    split;auto.
                 subst x; case (OM Mbeta).
                 intros H1 H2; right.
                 apply lt_le_trans with (ksi + alpha).
                 + apply plus_mono_r; eauto with schutte.
                 + left.
                   destruct (OM Malpha) as [H3 H4]; now apply H4.
               -  exists beta; split; auto.
                  left; subst x.
                  case (OM Mbeta);  intros H1 H2;  apply H2.
                  apply lt_le_trans with alpha;auto.
             }
       + apply le_plus_r;eauto with schutte.
  Qed.
  
End AP_closed.  

(* end hide *)


Theorem AP_closed : Closed AP.
  split.
  -  apply AP_sup;auto.
  -  intros;  apply AP_sup;auto.
Qed.



Lemma AP_o_segment :  the_ordering_segment AP = ordinal.
Proof.
  intros;apply segment_unbounded.
  eapply SA2.
  eapply ord_ok;eauto.
  generalize 
    (ordering_unbounded_unbounded 
       (A:=the_ordering_segment AP) 
       (B:=AP) 
       (f:=phi0)); intro H.
  generalize (H (ord_ok  AP)); intro H0;  rewrite <- H0.
  now  apply AP_unbounded.
Qed.

(** ** Properties of [phi0] *)

Theorem normal_phi0 : normal phi0 AP.
Proof.
  apply TH_13_6R with ordinal.
  -  unfold _phi0; rewrite <- AP_o_segment; apply ord_ok.
  - apply AP_closed.
  - apply AP_unbounded.
Qed.


Lemma phi0_ordering :  ordering_function phi0 ordinal AP.
Proof.
  intros;   unfold _phi0; rewrite <- AP_o_segment;
    apply ord_ok.
Qed.

Lemma phi0_elim : forall P : (Ord->Ord)->Prop,
    (forall f: Ord->Ord, 
        ordering_function f ordinal AP -> P f) ->
    P phi0.
Proof.
  intros P H; apply H, phi0_ordering.
Qed.

Lemma AP_phi0 (alpha : Ord) : In AP (phi0 alpha).
Proof.
  pattern phi0; apply phi0_elim.
  destruct 1 as [H [H0 H1]];  apply H0;auto.
  split.
Qed. 

Lemma phi0_zero : phi0 zero =  1.
Proof.
  generalize (order_function_least_least  phi0_ordering),least_AP;
    intros H H0;  rewrite (least_member_unicity AX1  H H0);eauto.
Qed.


Lemma phi0_mono (alpha beta : Ord) :
  alpha < beta ->  phi0 alpha < phi0 beta.
Proof.
  intro H; pattern phi0; apply phi0_elim.
  intros;eapply ordering_function_mono;eauto with schutte.
Qed.

Lemma phi0_mono_weak (alpha beta : Ord) :
  alpha <= beta ->  phi0 alpha <= phi0 beta.
Proof.
  destruct 1.
  -  subst beta; auto with schutte.
  -  right;apply phi0_mono;auto.
Qed.

Lemma phi0_mono_R (alpha beta : Ord) :
  phi0 alpha < phi0 beta -> alpha < beta.
Proof.
  pattern phi0; apply phi0_elim.
  intros;eapply ordering_function_monoR; eauto.
  all : split.
Qed.

Lemma phi0_mono_R_weak : forall alpha beta, 
    phi0 alpha <= phi0 beta -> alpha <= beta.
Proof.
  intros alpha beta;  pattern phi0; apply phi0_elim.
  intros.
  eapply ordering_function_mono_weakR;eauto.
  all : split.
Qed.

Lemma phi0_inj (alpha beta : Ord) :
  phi0 alpha = phi0 beta -> alpha = beta.
Proof.
  intros; apply le_antisym; apply phi0_mono_R_weak;auto with schutte.
Qed.



Lemma phi0_positive (alpha : Ord):  zero < phi0 alpha.
Proof.
  intros.
  apply lt_le_trans with (phi0 zero).
  rewrite phi0_zero.
  eauto with schutte arith.
  
  pattern phi0 ; apply phi0_elim.
  intros.
  eapply ordering_function_mono_weak; eauto with schutte.
Qed.

Lemma plus_lt_phi0 : forall ksi alpha, ksi < phi0 alpha ->
                                       ksi + phi0 alpha = phi0 alpha.
Proof.
  intros ksi alpha ;  pattern (phi0 alpha);  apply phi0_elim.
  intros f Hf;  assert (AP (f alpha)).
  {  destruct Hf as [H0 [H1 [H2 H3]]]. 
     apply H1 ; split. }
  destruct H;  auto. 
Qed.


Lemma phi0_alpha_phi0_beta : forall alpha beta, alpha < beta ->
                                                phi0 alpha + phi0 beta =
                                                phi0 beta.
Proof.
  intros.
  apply plus_lt_phi0; eauto with schutte.
  apply phi0_mono.
  auto.
Qed.

Lemma phi0_sup : forall U,  Inhabited _ U ->
                            countable U ->
                            phi0 (|_| U) = |_| (image U phi0).
Proof.
  intros U H0 H1;  case normal_phi0.
  destruct 2 as [H2 [H3 H4]]; symmetry; auto.
  apply H4; auto;  split.
Qed.

Lemma phi0_of_limit (alpha : Ord)  :
  is_limit alpha ->  phi0 alpha = sup (image (members alpha) phi0).
Proof.
  intro H; pattern alpha at 1; rewrite  (is_limit_sup_members H);
    destruct  normal_phi0 as [H0 H1].
  destruct H1 as [H1 H2] ;symmetry;auto.
  destruct H2 as [H2 H3]; apply H3.
  - intro; split.
  - exists zero; tricho zero alpha HH; auto.
    +  subst alpha; destruct H as [H _]; now destruct H.
    + destruct (not_lt_zero HH). 
  - apply countable_members;auto.
Qed.


Lemma AP_to_phi0 (alpha : Ord) :
  AP alpha -> exists beta,  alpha = phi0 beta.
Proof.
  intro H; pattern phi0;apply phi0_elim.
  destruct 1 as [H0 [H1 [H2 H3]]].  
  case (H2 _ H); intros x [_ H4]; exists x; now rewrite H4.
Qed.



Lemma AP_plus_AP (alpha beta gamma : Ord) :
  zero < beta -> 
  phi0 alpha + beta = phi0 gamma ->
  alpha < gamma /\  beta = phi0 gamma.
Proof.
  intros H H0;  tricho alpha gamma H3.
  -  split;auto.
     tricho beta (phi0 gamma) H4.
     +  case (@lt_irr (phi0 gamma)).
        pattern (phi0 gamma) at 1; rewrite <- H0.
        * apply AP_plus_closed; auto.
          apply AP_phi0;  eauto with schutte.
          apply phi0_mono;auto.
     + auto.
     +  rewrite <- H0 in H4;  case (@lt_irr beta).
        eapply le_lt_trans;eauto.
        apply le_plus_r.
  -  subst gamma;  case (@lt_irr (phi0 alpha)).
     pattern (phi0 alpha) at 2;  rewrite <- H0.
     pattern (phi0 alpha) at 1; rewrite <- alpha_plus_zero.
     apply plus_mono_r;auto.
  - assert(H1 :  phi0 alpha <= phi0 gamma).
    { rewrite <- H0; apply le_plus_l. }
    case (le_not_gt H1);  apply phi0_mono;auto.
Qed.


Lemma is_limit_phi0 (alpha : Ord) :
  zero < alpha ->  is_limit (phi0 alpha).
Proof.
  intros  H; split.
  - intro H0; case (@lt_irr zero).
    apply lt_le_trans with alpha;auto.
    rewrite <- H0;  pattern phi0; apply phi0_elim.
    intros f H1; eapply ordering_le;eauto.
    split. 
  - intro H0; destruct H0 as [x H0].
    generalize (@AP_phi0 alpha).
    intro H1; destruct H1 as [H1 H2]; rewrite H0 in H2.
    assert (H3 : x < succ x) by auto with schutte.
    generalize (H2 _ H3);  intros H4;
      assert (H5 :zero < x).
    { tricho zero x H8.
      -  auto.
      -  subst x;  replace (succ zero) with (F 1) in H0. 
         + rewrite <- phi0_zero in H0.
           case (@lt_irr (phi0 zero)).
           pattern (phi0 zero) at 2; rewrite <- H0.
           apply phi0_mono;auto.
         +  simpl;auto.
      -  case (@not_lt_zero x); auto.
    }
    assert (H6 : x < x + x).
    { pattern x at 1;rewrite <- alpha_plus_zero.
      apply plus_mono_r;auto.
    }
    generalize (succ_mono  H6);  rewrite <- H4.
    intros H7; apply lt_irr with (succ (x+x));  auto.
    now rewrite plus_of_succ in H7.
Qed. 


Lemma omega_eqn : omega = phi0 1. (** [omega^ 1] *)
Proof. 
  destruct (AP_to_phi0 (AP_omega)) as [beta Hbeta]; rewrite Hbeta;
    tricho beta (F 1) H. 
  -   destruct (finite_lt_inv 1 H ) as [i [H0 H1]].
      inversion H0.
      +  subst i beta; simpl in Hbeta; rewrite  phi0_zero in Hbeta.
         specialize (finite_lt_omega 1); intro H1; rewrite Hbeta in H1.
         destruct (lt_irr H1).
      + inversion H3.
  -  now subst.
  -  specialize (phi0_mono H); intro H0;
       rewrite <- Hbeta in H0.
     specialize (lt_omega_finite H0);intros [i Hi].
     specialize (@is_limit_phi0 (F 1));  intro H2.
     rewrite Hi in H2;   destruct (finite_not_limit i).
     apply H2,  lt_succ.
Qed.


Lemma le_phi0 (alpha : Ord) : alpha <= phi0 alpha.
Proof.
  eapply (@ordering_le  phi0 ordinal AP).
  apply phi0_ordering.
  split.
Qed.

(** ** Properties of [epsilon0] *)

Lemma epsilon0_fxp : phi0 epsilon0 = epsilon0.
Proof.
  unfold epsilon0, omega_limit; rewrite phi0_sup.
  assert (D1: countable (image (seq_range omega_tower) phi0)).
  { exists (fun alpha i =>  alpha = omega_tower i).
    split.
    -  red; destruct 1 as [x [H H0]].
       destruct H as [i [_ H]];   exists (S i);
         cbn; rewrite H; auto.
    - red;  destruct 1;  destruct H;  split. 
    -  red; intros; congruence.
  }
  assert (D2: countable (seq_range omega_tower)).
  { apply Countable.seq_range_countable. }
  -  apply le_antisym.
     +  apply sup_mono; trivial.
        * destruct 1 as [x0 [[i [_ H]] H0]].
          exists (phi0 x0); split.
          {  exists (S i); split; auto; simpl; auto ; now f_equal. }
          left; auto.
     + apply sup_mono; trivial.
       intros alpha [i H];  exists (phi0 alpha); split; auto.
       exists alpha; split; auto.
       * exists i; auto.
       * apply le_phi0.
  - exists (phi0 zero), 0; simpl; rewrite phi0_zero; split; auto. 
  - apply Countable.seq_range_countable.
Qed.


Lemma epsilon0_AP : AP epsilon0.
Proof.
  rewrite <- epsilon0_fxp;  apply AP_phi0.
Qed.


Lemma omega_tower_mono (i : nat) : omega_tower i < omega_tower (S i).
Proof.
  induction i;  simpl.
  -  rewrite succ_is_plus_1, zero_plus_alpha;
       rewrite <- omega_eqn;   apply finite_lt_omega.
  -  simpl in IHi; now apply phi0_mono.
Qed.


Lemma lt_phi0 (alpha : Ord):
  alpha < epsilon0 -> alpha < phi0 alpha.
Proof.
  unfold epsilon0;  intros H.
  specialize (@omega_limit_least_gt alpha omega_tower omega_tower_mono H);
    intro H0.
  destruct H0 as [i [H0 H1]].
  destruct i as [|j].
  -   red in H0;  simpl in H0;
        assert (H2 : alpha = zero).
      {
        specialize (lt_succ_le_2  _ H0); intro H3; apply le_alpha_zero; auto.
      }
      subst alpha; rewrite phi0_zero; auto.
  - assert (H2 : omega_tower j <= alpha).
    {
      tricho  alpha (omega_tower j) H2.
      -   specialize (H1 _ H2);  elimtype False.
          destruct H1; abstract lia.
      -   left; auto.
      -   right;auto.
    }
    assert (omega_tower (S j) <= phi0 alpha).
    {   simpl.   now apply phi0_mono_weak. }
    apply lt_le_trans with (omega_tower (S j)); auto.
Qed.

Theorem epsilon0_lfp : least_fixpoint lt phi0 epsilon0.
Proof.
  split.
  - apply epsilon0_fxp.
  - intros alpha H; tricho alpha epsilon0 H0.
    + specialize (lt_phi0 H0); intro H1.
      rewrite  H in H1; destruct (lt_irr H1).
    + subst alpha; now left.
    + now right.
Qed.

Lemma phi0_lt_epsilon0 (alpha : Ord) :
  alpha < epsilon0 -> phi0 alpha < epsilon0.
Proof.
  intro; rewrite <- epsilon0_fxp; now apply phi0_mono.
Qed.


Lemma phi0_lt_epsilon0_R (alpha : Ord):
  phi0 alpha < epsilon0  -> alpha < epsilon0.
Proof.
  intro H; rewrite <- epsilon0_fxp in H; now  apply phi0_mono_R.     
Qed.

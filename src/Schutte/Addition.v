(* (C) Pierre Castéran ,Labri, Université Bordeaux 1 *)

From Coq Require Import Arith  Logic.Epsilon  Ensembles.
From hydras Require Export Schutte_basics  Ordering_Functions  PartialFun
        Countable  MoreEpsilonIota.
Set Implicit Arguments.


(** * Definitions

 **  addition, multiplication by a positive integer *)

Definition plus alpha := ord (ge alpha).

Notation "alpha + beta " := (plus alpha beta) : schutte_scope.

(** returns [alpha * (S n)]
*)
                       

Fixpoint mult_Sn (alpha:Ord)(n:nat){struct n} :Ord :=
 match n with 0 => alpha
            | S p => mult_Sn alpha p + alpha
 end.


Definition mult_n alpha n :=
  match n with
      0 => zero
    | S p => mult_Sn alpha p
  end.

Notation "alpha * n" := (mult_n alpha n) : schutte_scope.


(** * Proofs, proofs, proofs 
*)


Lemma Unbounded_ge (alpha : Ord)  :   Unbounded (ge alpha).
Proof with auto with schutte.
  red. intros   x ; tricho alpha x H3.
 -  exists (succ x);split ...
    right;  apply lt_trans with x; trivial ...
 -  subst alpha; exists (succ x) ; split ...
    red;red ...
 - exists (succ alpha); split.
  +  red;red ...
  +  apply lt_trans with alpha ...
Qed.

Lemma ge_o_segment (alpha : Ord) :
 the_ordering_segment (ge alpha) = ordinal.
Proof.
  intros;apply segment_unbounded.
  - pattern  (the_ordering_segment (ge alpha)); apply iota_ind.
    +  generalize  (ordering_segment_ex_unique (ge alpha));
         intros. destruct  H. 
       destruct H.
       exists x; split;auto.
    +  destruct 1;eapply ordering_function_seg;eauto.
  -     generalize 
          (ordering_unbounded_unbounded 
             (A:=the_ordering_segment (ge alpha)) 
             (B:=ge alpha) 
             (f:=plus alpha));  intros H.
        apply H.
        unfold plus; intros;  apply ord_ok. 
        apply Unbounded_ge;auto.
Qed.

Lemma plus_ordering (alpha : Ord) :
  ordering_function (plus alpha)
                    ordinal
                    (ge alpha).
Proof.
 unfold plus;  generalize (@ord_ok (ge alpha));
    rewrite  ge_o_segment;auto.
Qed.

Lemma plus_elim (alpha : Ord) :
  forall P : (Ord->Ord)->Prop,
    (forall f: Ord->Ord, 
        ordering_function f ordinal (ge alpha)-> P f) ->
    P (plus alpha).
Proof.
 intros  P H0; now apply H0, plus_ordering.
Qed.

Lemma normal_plus_alpha (alpha : Ord) : 
  normal (plus alpha) (ge alpha).
Proof.
 unfold plus;pattern (ord (ge alpha)).
 unfold ord, some;apply epsilon_ind. 
 -  rewrite ge_o_segment; trivial.
   +  exists (plus alpha);apply (plus_ordering alpha); auto.
-  intros a H0; rewrite ge_o_segment in H0; trivial.
   split; trivial.
   apply Th_13_5_2; trivial.
+   intros M H1 H2 H3;  destruct H2; apply le_trans with x;auto.
       *  specialize (H1 _ H);  apply H1.
       *  apply sup_upper_bound;auto. 
Qed.

(** ** Basic properries of addition 
 *)

Lemma alpha_plus_zero (alpha: Ord):   alpha + zero = alpha.
Proof.
 pattern  (plus alpha); apply plus_elim;eauto.
 intros f H0 ; case (order_function_least_least H0).
  intros H1 H3; case (H3 alpha);auto.
 -  red;red; auto with schutte.
 -  intro H4; case H1.
  +  symmetry;tauto.
  +  intro; case (@lt_irr alpha);auto.
     apply lt_trans with (f zero);auto.
Qed.

Remark ge_zero : (ge zero : Ensemble Ord) = ordinal.
Proof with eauto with schutte.
  apply Extensionality_Ensembles.
  split.
   +  red; split.  
   + unfold ge ...
Qed.


Lemma zero_plus_alpha (alpha : Ord) : zero + alpha = alpha.
Proof with auto with schutte.
  pattern (plus zero);  apply plus_elim ...
 intros f H0; assert (H1:ordering_function (fun o => o) ordinal ordinal).
 {  (repeat split) ...
     -  eauto with schutte.
 }
 rewrite ge_zero in H0.
 generalize (ordering_function_unicity H0 H1); destruct 1; auto.
 apply H2; split.
Qed.


Lemma le_plus_l (alpha beta : Ord) : alpha <= alpha + beta.
Proof.
  pattern alpha at 1;  rewrite  <- alpha_plus_zero;auto.
  pattern (plus alpha);apply plus_elim;auto.
  intros;eapply ordering_function_mono_weak;eauto with schutte.
Qed.

Lemma le_plus_r (alpha beta : Ord) :  beta <= alpha + beta.
Proof.
 pattern (plus alpha);  apply plus_elim;auto.
 intros; eapply ordering_le; eauto.  
 split.
Qed.


Lemma plus_mono_r (alpha beta gamma : Ord) : 
    beta < gamma -> alpha + beta < alpha + gamma.
Proof.
 intro  H; pattern (plus alpha); apply plus_elim;auto.
 intros; eapply ordering_function_mono;eauto with schutte.
Qed.

 
Lemma plus_mono_r_weak (alpha beta gamma : Ord) :
  beta <= gamma ->  alpha + beta <= alpha + gamma.
Proof.
  intros  H;  case (le_disj H).
 - intros; subst gamma; auto with schutte.    
 - right;  apply plus_mono_r;auto.
Qed.


Lemma plus_reg_r (alpha beta gamma : Ord) :
  alpha + beta = alpha + gamma  ->  beta = gamma.
Proof with trivial.
 intros  H;   tricho beta gamma H0 ...
 -  case (@lt_irr (alpha+beta)).
    pattern (alpha+beta) at 2; rewrite H; apply plus_mono_r ...
 -  case (@lt_irr (alpha+beta)).
    pattern (alpha+beta) at 1; rewrite H; apply plus_mono_r ...
Qed.


Lemma plus_of_succ (alpha beta : Ord) :
    alpha + (succ beta) = succ (alpha + beta).
Proof with trivial.
 pattern (plus alpha); apply plus_elim ...
 intros plus_alpha Hp;
   assert (H1 :plus_alpha beta < plus_alpha (succ beta)).
 {  eapply ordering_function_mono;eauto.
    red;auto with schutte.
    split.
    apply lt_succ; auto.
 }
 generalize (@lt_succ_le (plus_alpha  beta) (plus_alpha  (succ beta))).
 intros H2.
 generalize (H2 H1);  intro H5; case (le_disj H5) ; auto. 
 intro H6;case Hp;intros H7 H8; decompose [and] H8.
 case (H3 (succ (plus_alpha beta))).
 -  red; apply le_trans with (plus_alpha  beta).
   +  generalize (H beta );  unfold In,  ge;  auto.
      intro H9; apply H9; split.
   +  right; apply lt_succ;  auto.
 -  intros x [Hx Ex]; clear H8; absurd ( beta < x /\ x < succ beta).
    + intro H8; decompose [and] H8;clear H8.
      assert (H8: succ beta <= x) by (apply lt_succ_le; eauto with schutte).
      case (@lt_irr (succ beta)).
      eapply le_lt_trans;eauto.
    +  split.
   *  eapply ordering_function_monoR;eauto.
      split.
      rewrite Ex; auto with schutte.
   *  rewrite <- Ex in H6; eapply ordering_function_monoR;eauto.
     auto with schutte.
Qed.

Lemma succ_is_plus_1 alpha :  succ alpha = alpha +  1.
Proof. 
   rewrite  <- alpha_plus_zero  at 1; change (F 1) with (succ zero).
   rewrite   plus_of_succ;   now repeat rewrite alpha_plus_zero.
Qed. 


Lemma alpha_plus_sup (alpha : Ord) (A : Ensemble Ord) :
    Inhabited _ A ->
    countable A ->
    alpha + |_| A = |_| (image A (plus alpha)).
Proof.
 intros  H0 H1 ;  generalize (@normal_plus_alpha alpha ).
 intros [H [H2 [H3 H4]]];  rewrite  H4; auto.
 split.
Qed.


Lemma plus_limit (alpha beta : Ord)
  : is_limit beta ->
    alpha + beta =  |_| (image (members beta) (plus alpha)).
Proof.
 intros H ; generalize (is_limit_sup_members H);intro e.
 generalize (@normal_plus_alpha alpha ); intro H2.
 pattern beta at 1;rewrite e; destruct H2 as [H0 [H1 [H2 H3]]].  
 rewrite <- H3;auto.
 -  red;split.
 - case H. exists zero.
   red; auto with schutte.
   generalize (zero_le  beta).
   intro H6; case (le_disj H6).
   +  intro; subst beta; now destruct H4.
   + intros; now red.
 - apply countable_members; auto.
Qed.


Lemma plus_FF : forall i j, F (i + j) = F i + F j.
Proof. 
 induction i.
 -  simpl.
     intros;rewrite zero_plus_alpha;auto with schutte.
 -  simpl; induction j.
    +  simpl.
       rewrite alpha_plus_zero;auto with schutte.
       now rewrite <- (plus_n_O i).
    +  rewrite IHi.
       replace (F (S j)) with (succ (F j)).
       * rewrite plus_of_succ, plus_of_succ, <- IHi, IHj; auto with schutte.
       * now simpl.
Qed.



Lemma one_plus_omega :  1 + omega = omega.
Proof.
 rewrite plus_limit; auto with schutte.
 -  apply le_antisym; auto with schutte.
  +    unfold omega_limit;  apply sup_mono;auto with schutte.
   *   apply Ordering_Functions.R1 with ordinal (ge (F 1)).
       apply plus_ordering.  
       apply    countable_members;auto with schutte.
       red; split. 
   *      intros x [a [H1 H2]]. 
          red in H1; case (@lt_omega_finite _  H1).
          intros n e; exists (F (S n)).
          subst x; split;auto with schutte.
          exists (S n); trivial.
          subst a. split;auto.
        subst a. left;  now rewrite <- plus_FF . 
  + unfold omega_limit; apply sup_mono.
  *    apply seq_range_countable; auto with schutte.
  *  simpl; auto with schutte.
     apply Ordering_Functions.R1 with ordinal (ge (succ zero)).
     apply plus_ordering; auto with schutte.
     apply countable_members; auto with schutte.
     red; split. 
  *  intros x [x0 [_ Hx]]; subst x.
     exists (F (S x0));split;auto with schutte.
     exists (F x0);split;auto with schutte.
     red;  red;  apply finite_lt_omega.
     rewrite <- plus_FF; trivial.
 - apply is_limit_omega.
Qed.


Lemma minus_exists (alpha beta : Ord) :
  alpha <= beta ->
  exists gamma, alpha + gamma = beta.
Proof.
 intro H; pattern (plus alpha); apply plus_elim;auto.
 intros f H2; case H2;intros H3 H4; decompose [and] H4; clear H4.
 case (H5 beta H).  intros;exists x;auto.
 now destruct H1.
Qed.


Section proof_of_associativity.
  Variables alpha beta : Ord.
  
  Lemma plus_assoc1 (gamma : Ord) :
    alpha + beta <= alpha + (beta + gamma) .
  Proof.
    intros;apply plus_mono_r_weak;auto.
    -  apply le_plus_l; auto.
  Qed.

  Lemma plus_assoc2 (gamma : Ord) :
    alpha + beta <= gamma ->
    exists khi,  gamma = alpha + (beta + khi).
  Proof.
    intros  H0; assert (H1 : alpha <= gamma).
    {  apply le_trans with (alpha + beta);auto.
       apply le_plus_l; auto.
    }  case (minus_exists H1); intros z Hz .
    assert (H2 :beta <= z).
    {  tricho beta z HH.
       -  right;auto.
       -  left;auto.
       -  case (@lt_irr gamma).
          pattern gamma at 1; rewrite <- Hz.
          apply lt_le_trans with (alpha + beta);auto.
          + apply plus_mono_r;auto.
    }
    case (minus_exists H2);intros u Hu.
    exists u;auto.
    rewrite Hu;auto.
  Qed.

  Let f_alpha_beta := plus (alpha + beta).

  Let g_alpha_beta gamma := alpha + (beta + gamma).

  Remark of_g : ordering_function g_alpha_beta ordinal (ge (alpha+beta)).
  Proof.
    repeat split.
    - intros;red; red; unfold g_alpha_beta; now apply plus_assoc1.
    -   intros b H;
          case (plus_assoc2  H). intros x H'x;  exists x.
        unfold g_alpha_beta;split;auto.
        split.
    -  unfold g_alpha_beta;intros.
       + apply plus_mono_r;auto with schutte.
         apply plus_mono_r;auto with schutte.
  Qed.


  Lemma of_u : fun_equiv f_alpha_beta g_alpha_beta ordinal ordinal.
  Proof.
    eapply ordering_function_unicity.
    - unfold f_alpha_beta; apply plus_ordering.
    - apply of_g.
  Qed.

  Lemma plus_assoc3 (gamma : Ord) :
    f_alpha_beta  gamma =  g_alpha_beta gamma.
  Proof.
    case of_u; intros H0 H1; apply H1; auto.
    split.
  Qed.

  Lemma plus_assoc' (gamma : Ord) :
    alpha + (beta + gamma) = (alpha + beta) + gamma.
  Proof.
    intros; generalize plus_assoc3; unfold f_alpha_beta, g_alpha_beta.
    intros;symmetry;apply H.
  Qed.

End proof_of_associativity.
 
Theorem plus_assoc (alpha beta gamma : Ord) :
  alpha + (beta + gamma) = (alpha + beta) + gamma.
Proof.
  apply plus_assoc'; auto.
Qed.

Lemma one_plus_infinite (alpha : Ord) :
  omega <= alpha ->  1 + alpha = alpha. 
Proof.
 intros  H.
 generalize (minus_exists H); intros [gamma e];  subst alpha ;
  auto with schutte.
 rewrite plus_assoc;auto with schutte; now rewrite one_plus_omega.
Qed.

Lemma finite_plus_infinite (n : nat) (alpha : Ord) :
  omega <= alpha -> n + alpha = alpha.
Proof.
 induction n.
 - simpl; intros;rewrite zero_plus_alpha;trivial; eauto with schutte.
 -  intros; simpl; replace (succ (F n)) with (F 1 + F n).
    + rewrite <- plus_assoc; eauto with schutte.
      rewrite IHn;auto.
      apply one_plus_infinite;eauto with schutte.
  + now   rewrite <- plus_FF.
Qed.


Example L_3_plus_omega : 3 + omega = omega.
Proof.
 apply finite_plus_infinite, le_refl.
Qed.

Lemma plus_mono_weak_l : forall alpha beta gamma,
                          alpha <= beta -> alpha + gamma <= beta + gamma.
Proof with  eauto with schutte.
 intros alpha beta gamma  H0;
 assert (H1 : ordinal alpha) by ( eauto with schutte).
 assert (H2 :ordinal beta) by ( eauto with schutte).
 case (minus_exists H0); intros  khi  ekhi;  subst beta.
 rewrite <- plus_assoc ... 
 apply plus_mono_r_weak ... 
 apply le_plus_r ...
Qed.

Lemma plus_mono_bi : forall alpha beta gamma delta, 
                        alpha <= gamma ->
                        beta < delta -> 
                        alpha + beta < gamma + delta.
Proof with eauto with schutte.
 intros alpha beta gamma delta H H0; apply le_lt_trans with (gamma+beta).
 apply plus_mono_weak_l ...
 apply plus_mono_r ...
Qed.

Lemma mult_n_one : forall n, (F 1) * S n = F (S n).
 Proof.
  induction n.
  -   trivial.
  -   simpl in *; rewrite IHn; rewrite plus_of_succ; auto with schutte.   
      rewrite alpha_plus_zero;auto with schutte.
 Qed.

 
Lemma mult_n_mono : forall alpha beta , alpha < beta -> 
   forall n,  alpha * S n <  beta * S n.
Proof with auto.
 induction n; simpl ...
 apply plus_mono_bi ...
 right ...
Qed.
 
Lemma le_a_mult_Sn_a : forall alpha n, ordinal alpha -> 
                                       alpha <= alpha * S n.                           
Proof.
 intros alpha n H;  case n.
 -  simpl;auto with schutte.
 -  intros;simpl;apply le_plus_r;auto with schutte.
Qed.

Lemma mult_Sn_mono2 : forall a, zero < a ->
                         forall n p, (n < p)%nat -> a * S n <  a * S p.
Proof with auto with schutte.
 intros a Ha; induction 1.
 - simpl; intros; pattern ( mult_Sn a n) at 1; rewrite <- alpha_plus_zero ...
  +   apply plus_mono_r ...
 -  simpl;apply lt_trans with (mult_Sn a m);auto.
    pattern ( mult_Sn a m) at 1; rewrite <- alpha_plus_zero ...
    apply plus_mono_r ...
Qed.

Lemma mult_Sn_mono3 : forall alpha, zero < alpha ->
                         forall n p, (n < p)%nat -> alpha * S n + alpha 
                                                    <=  alpha * S p.
Proof with auto with schutte.
 intros a Ha; induction 1 .
 - simpl; apply eq_le ...
 - simpl; apply plus_mono_weak_l ...
   apply lt_le ...
   apply  mult_Sn_mono2 ...
Qed.




  
 
  

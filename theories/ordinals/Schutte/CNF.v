
(**  Cantor normal form *)

(** Pierre Casteran, Labri and Univ Bordeaux. *)


From Coq Require Import Arith List Sorting.Sorted
     Logic.Epsilon Ensembles.
From hydras Require Export Schutte_basics  Ordering_Functions
     PartialFun  Countable Schutte.Addition AP.
Require Export  Classical.


Set Implicit Arguments.

(** A Cantor normal form for a countable ordinal [alpha] is just a sorted
list [l] (in decreasing order) such that  [alpha]  is equal to the sum of the terms [phi0 beta], for every term [beta] in [l].


Note that, if [alpha] is greater or equal than [epsilon0], the members of [l]
are less _or equal_ than [alpha].

For instance, the Cantor Normal Form of [epsilon0] is just [epsilon0 :: nil].

*)

(* begin snippet Defs *)

Definition cnf_t := list Ord.

Fixpoint eval (l : cnf_t) : Ord :=
  match l with nil => zero
              | beta :: l' => phi0 beta + eval l'
  end.

Definition sorted (l: cnf_t) :=
  LocallySorted (fun alpha beta => beta <= alpha) l.


Definition is_cnf_of (alpha : Ord)(l : cnf_t) : Prop :=
  sorted l /\ alpha = eval l.

(* end snippet Defs *)


Definition exponents_lt (alpha: Ord) :=
        Forall (fun beta =>  beta < alpha).

Definition exponents_le (alpha : Ord) :=
        Forall (fun beta => beta <= alpha).


(* begin hide *)

#[global] Hint Constructors LocallySorted : schutte.
#[global] Hint Unfold sorted : schutte.

(* end hide *)

Lemma exponents_lt_eval alpha l:   exponents_lt alpha l ->
                                      eval l < phi0 alpha.
Proof.
 induction 1; cbn.
 -  apply phi0_positive.
 - apply AP_plus_closed; trivial.
   + apply AP_phi0; auto.
   + apply phi0_mono;auto.
Qed.


Lemma sorted_tail  alpha l:
  sorted (cons alpha l) -> sorted l.
Proof.  inversion 1; auto with schutte. Qed.

Lemma nf_bounded : forall beta  l alpha,
                        alpha <= phi0 beta  ->
                        is_cnf_of alpha l -> exponents_le beta l.
Proof.
 intros  beta   l ;  elim l.
 -  constructor.
 -  intros a l0 H alpha H0 H1; right.
   +  case H1;intros H3;  simpl in H3.
     intro ; subst alpha;  apply phi0_mono_R_weak.
     apply le_trans with (phi0 a + eval l0);auto.
     apply le_plus_l.
   +  apply H with (eval l0).
      * case H1;  intros H2 H3; simpl in H3.
        apply le_trans with alpha.
        -- subst alpha;  apply le_plus_r.
        -- auto with schutte.
      *  split; [ | trivial].
         case H1; inversion 1; auto with schutte.
Qed.



Lemma cnf_of_ap (alpha : Ord) :
  In AP alpha -> exists l,  is_cnf_of alpha l.
Proof.
 intros H;  case phi0_ordering.
 intros H0 H1 H2 H3; destruct (H2 alpha H) as [x [Hx Ex]].
 subst alpha;  exists (cons  x nil); split.
 - constructor.
 - simpl; now  rewrite alpha_plus_zero.
Qed.


Lemma sorted_lt_lt (beta: Ord) : forall l alpha,
     sorted (cons alpha l) -> alpha <  beta ->
     eval (cons alpha l) < phi0 beta.
 Proof.
  induction l.
  - simpl; inversion_clear 1.
    intro H;apply AP_plus_closed.
    +  apply AP_phi0;eauto with schutte.
    +  apply phi0_mono;eauto with schutte.
    +  apply phi0_positive.
  - inversion 1;  simpl;   simpl in IHl.
    intro;  apply AP_plus_closed.
    + apply AP_phi0;eauto with schutte.
    + apply phi0_mono;eauto with schutte.
    +   apply IHl.
        * inversion H; auto.
        * eauto with schutte.
Qed.


 Lemma sorted_lt_lt_2 l alpha :
   sorted (cons alpha l) ->
   eval (cons alpha l) < phi0 (succ alpha).
Proof.
 intros;apply (sorted_lt_lt H).
 inversion H;intros;eauto with schutte.
Qed.


Lemma cnf_head_eq alpha beta ol ol':
                         sorted (cons alpha ol) ->
                         sorted (cons beta ol') ->
                         eval (cons alpha ol) = eval (cons beta ol') ->
                         alpha = beta.
Proof.
 intros H H0 H1; tricho alpha beta H2; [ | trivial | ].
 -   generalize (sorted_lt_lt  H H2) ; intro H3.
     case (@lt_irrefl (eval (cons alpha ol))).
     apply lt_le_trans with (phi0 beta); [trivial | ].
     +   rewrite H1;  simpl ;  apply le_plus_l.
 -  generalize (sorted_lt_lt H0 H2);  intro H3.
    case (@lt_irrefl (eval (cons beta ol'))).
    apply lt_le_trans with (phi0 alpha); [trivial | ].
    + rewrite <- H1; simpl;  apply le_plus_l.
Qed.

Lemma cnf_eq  alpha beta ol ol':
  sorted (cons alpha ol) ->
  sorted (cons beta ol') ->
  eval (cons alpha ol) = eval (cons beta ol') ->
  alpha = beta /\ eval ol = eval ol'.
Proof.
 intros H H0 H1; generalize (cnf_head_eq H H0 H1).
 intro; subst beta;  split;[trivial | ].
 simpl in H1; now eapply plus_reg_r with (phi0 alpha).
Qed.


Lemma cnf_plus1 (ol : cnf_t) :
 sorted ol ->  forall alpha,
    exists ol',  is_cnf_of (phi0 alpha + eval ol) ol'.
Proof.
 induction ol.
 -  inversion_clear  1 .
    intros alpha;  simpl;  exists  (cons alpha nil).
    split.
    + constructor.
    + split ; simpl.
 -  intros H alpha;  simpl; tricho alpha a H1.
    + exists  (cons a ol);  split.
      * auto.
      *  rewrite plus_assoc, phi0_alpha_phi0_beta; [simpl|]; auto.
    + subst a; exists (cons alpha (cons alpha ol));  split.
      * constructor; eauto with schutte.
      * simpl;  auto.
    +  exists (cons alpha (cons a ol));  split.
      *  constructor;auto with schutte.
      * now simpl.
Qed.


Lemma cnf_plus2 : forall ol, sorted ol ->
                    forall ol', sorted ol' ->
                     exists ol'', is_cnf_of (eval ol + eval ol') ol''.
Proof.
 induction ol.
 - simpl; intros; rewrite zero_plus_alpha;auto.
   exists ol';split;auto.
 -  intros; simpl; assert (sorted ol).
    {  inversion H;auto with schutte. }
   destruct  (IHol H1 _ H0) as [x [H3 H4]].
   destruct  (@cnf_plus1 _ H3 a) as [x0 H5].
   exists x0; rewrite <- H4 in H5; now  rewrite <- plus_assoc.
Qed.


Lemma cnf_plus : forall ol alpha,
  is_cnf_of alpha ol -> forall ol' beta, is_cnf_of beta ol' ->
  exists ol'', is_cnf_of (alpha + beta) ol''.
Proof.
 destruct 1 as [H H0].
 destruct 1 as [H1 H2].
 rewrite H0;rewrite H2; apply cnf_plus2;auto.
Qed.

(* begin hide *)

Lemma not_AP_inv_0 : forall alpha,
                    zero < alpha ->
                    ~ (AP alpha) ->
                    exists beta,zero < beta /\
                                beta < alpha /\
                                alpha < beta + alpha .
Proof with eauto with schutte.
  intros alpha H H0; apply Classical_Prop.NNPP.
  intro H1;apply H0; split ...
  intros beta H2;  tricho (beta+alpha) alpha H3 ...
  - case (@lt_irrefl alpha).
    apply le_lt_trans with (beta+alpha) ...
    apply le_plus_r ...
  -  case H1; exists beta; split ; auto.
     tricho zero beta H4; auto with schutte.
     +  subst beta; rewrite zero_plus_alpha in H3;
          case (@lt_irrefl alpha);auto.
     +   now   case (@not_lt_zero beta).
Qed.

Lemma not_AP_inv2 : forall alpha, zero < alpha -> ~AP alpha ->
                               exists beta, exists gamma,
                                     zero < beta /\ zero < gamma /\
                                     beta < alpha /\ gamma < alpha /\
                                      alpha = beta + gamma.
Proof with eauto with schutte.
  intros alpha H H0; case (not_AP_inv_0 H H0).
  intros khi [Hkhi H'khi]; exists khi.
  case (minus_exists (alpha:=khi) (beta:= alpha)) ...
  - destruct H'khi. right;auto.
  - intros eta  H2; exists eta; split ; auto.
    split;auto.
    + tricho zero eta H3; trivial.
      *  subst eta; rewrite alpha_plus_zero in H2; trivial.
         decompose [and] H'khi; subst alpha; case (@lt_irrefl khi);auto.
      *  case (@not_lt_zero eta) ...
    +  decompose [and] H'khi; split;auto.
       split;auto.
       tricho zero khi H5 ...
       tricho eta alpha H6 ...
       subst eta; case (@lt_irrefl (khi+alpha)) ...
       case (@lt_irrefl (khi + eta)) ...
       apply lt_trans with (khi+alpha) ...
       apply plus_mono_r ...
       subst khi; case (@lt_irrefl zero);auto.
       case (@not_lt_zero khi) ...
Qed.

(* end hide *)


(** *** Every countable ordinal has (at least) a Cantor normal form

  (Proof by transfinite induction)
 *)

(* begin snippet cnfExists *)

Theorem cnf_exists (alpha : Ord) :
  exists l: cnf_t, is_cnf_of alpha l. (* .no-out *)
(*| .. coq:: none |*)
Proof.
 case (le_eq_or_lt (zero_le  alpha)).
 -  exists nil;  split.
    +  constructor.
    +  simpl;auto.
 -  pattern alpha; apply transfinite_induction;auto.
    intros a H0 H1; case (classic (AP a)).
    + intros H2;  apply cnf_of_ap; auto.
    +  intros H2; case (not_AP_inv2 H1 H2).
       intros x H3; destruct H3 as [z [H4' [H5' H6]]].
       case (H0 x).
       * case H6;auto.
       * auto.
       * intros x0 H; case (H0 z).
        --  tauto.
        --  auto.
        --  intros x1 H4;  decompose [and] H6;  subst a.
            destruct (cnf_plus H H4) as [x2 Hx2];  exists x2; auto.
Qed.
(*||*)
(* end snippet cnfExists *)

Lemma sorted_lt : forall l alpha, sorted (cons alpha l) ->
                                      eval l < phi0 alpha + eval l.
Proof.
  induction l.
  - inversion 1;  simpl; rewrite alpha_plus_zero;  apply phi0_positive;auto.
  - inversion 1;  simpl; rewrite plus_assoc.
    generalize (IHl _ H2); intro H5.
    apply le_lt_trans with (phi0 alpha + eval l).
    +  apply plus_mono_weak_l.
       now apply phi0_mono_weak.
    + rewrite <- plus_assoc; now apply plus_mono_r.
Qed.



(** *** Unicity of cnf

(Proof by induction on lists)

*)

(* begin snippet cnfUnicity *)

Lemma cnf_unicity : forall l alpha,
    is_cnf_of alpha l ->
    forall l', is_cnf_of alpha l' ->
               l=l'. (* .no-out *)
(*| .. coq:: none |*)
Proof.
 induction l.
 - destruct 1 as [H H0].
   simpl in H0; subst alpha;  destruct  l'.
   + auto.
   +  destruct 1 as [H0 H1];  simpl in H1;  case (@lt_irrefl zero).
      pattern zero at 2;rewrite H1.
      apply lt_le_trans with (phi0 o);auto with schutte.
      apply phi0_positive.
      apply le_plus_l;auto.
 -  destruct l' as [ |  o l'].
    + intro;  case H;case H0;intros H1 H2 H3 H4.
      simpl in H2, H4  ;  rewrite H2 in H4.
       assert (ordinal a) by split.
       case (@lt_irrefl zero).
       pattern zero at 2; rewrite H4.
       apply lt_le_trans with (phi0 a);auto.
       *  apply phi0_positive.
       *   apply le_plus_l;auto.
     +  intro;  case H; case H0;intros H1 H2 H3 H4;  rewrite H4 in H2.
        case (cnf_eq H3 H1 H2).
        intros; subst o;  replace l' with l;auto.
        * apply IHl with (eval l).
          split;auto.
          inversion H3; auto with schutte.
          rewrite H6;split;auto with schutte.
          inversion H1; auto with schutte.
Qed.
(*||*)
(* end snippet cnfUnicity *)


(** *** The main result *)

(* begin snippet cnfExUnique *)

(*| .. coq:: no-out |*)
Theorem cnf_exists_unique (alpha:Ord) :
  exists! l: cnf_t, is_cnf_of alpha l.
Proof.
    destruct (cnf_exists alpha) as [l Hl]; exists l; split; auto.
    now apply cnf_unicity.
Qed.
(*||*)
(* end snippet cnfExUnique *)


(** ** Cantor Normal Form and the ordinal epsilon0 *)

(* begin snippet cnfLtEpsilon0 *)

Lemma cnf_lt_epsilon0 : forall l alpha,
    is_cnf_of alpha l ->
    alpha < epsilon0 ->
    Forall (fun beta =>  beta < alpha) l. (* .no-out *)
(*| .. coq:: none |*)
Proof.
  induction l.
  - constructor.
  - unfold is_cnf_of.
    destruct 1 as [H e].
    intro H0; simpl.
    assert (Hlt : a < phi0 a).
    {
      apply lt_phi0;  simpl in e;  subst alpha;
       apply le_lt_trans with (phi0 a); auto with schutte.
      - apply le_phi0.
      - apply le_lt_trans with (2 := H0);  apply le_plus_l.
    }
    simpl in e; constructor.
    subst alpha;  apply lt_le_trans with (1 := Hlt).
    +  apply le_plus_l.
    +  specialize (IHl (eval l));  unfold is_cnf_of in IHl.
       apply Forall_impl with (fun o =>  o < eval l).
     * intros a0 H1;  apply lt_le_trans with (1 := H1).
       subst alpha;  apply le_plus_r.
     *  apply IHl .
        { split; auto ;   eapply sorted_tail; eauto. }
        apply le_lt_trans with (2 := H0).
        subst alpha; apply (le_plus_r).
Qed.
(*||*)

(* end snippet cnfLtEpsilon0 *)

(** The normal form of [epsilon0] is just [phi0 epsilon0]
 *)

(* begin snippet cnfOfEpsilon0 *)

(*| .. coq:: no-out |*)

Lemma cnf_of_epsilon0 : is_cnf_of epsilon0 (epsilon0 :: nil).
Proof.
  split.
  - constructor.
  - simpl; now rewrite alpha_plus_zero, epsilon0_fxp.
Qed.
(*||*)

(* end snippet cnfOfEpsilon0 *)

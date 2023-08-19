
(**  Ordinals of the first and second class,
   After Kurt Schuttes book : Proof theory

 *)

(**   Pierre Casteran, Univ. Bordeaux and  LaBRI *)



From Coq Require Import Relations  Classical   Classical_sets.
From hydras Require Import  Well_Orders Lub Countable.

Import   Compare_dec  Coq.Sets.Image  PartialFun MoreEpsilonIota.


Declare Scope schutte_scope.

Set Implicit Arguments.

#[global] Hint Unfold In : schutte.
Arguments Included [U] _ _.
Arguments countable [U] _.
Arguments Same_set [U] _ _.

Delimit Scope schutte_scope with sch.
Open Scope schutte_scope.

(** *  Definitions *)

(**   The type of countable ordinal numbers  *)

(* begin snippet OrdDecl *)

Parameter Ord : Type.
Parameter lt : relation Ord.
Infix "<" := lt : schutte_scope.

Definition ordinal : Ensemble Ord := Full_set Ord.
Definition big0 alpha : Ensemble Ord := fun beta =>  beta < alpha.

#[global] Hint Unfold ordinal : schutte.

(* end snippet OrdDecl *)

(* begin hide *)
Lemma ordinal_ok : forall a : Ord, ordinal a.
Proof.
  split.
Qed.

(* end hide *)

#[global] Hint Resolve ordinal_ok : schutte.

(** * The three axioms by Schutte *)

(** First Schutte's axiom  : Ord is well-ordered wrt lt *)

(* begin snippet AX1 *)

Axiom AX1 : WO lt.
(* end snippet AX1 *)


#[global] Hint Resolve AX1 : schutte.

#[global] Instance WO_ord : WO  lt := AX1.

(** Stuff for using Coq.Logic.Epsilon *)
(* begin snippet inhOrd *)

Axiom inh_Ord : inhabited Ord.

#[ global ] Instance InH_Ord : InH Ord. (* .no-out *)
Proof. (* .no-out *)
  exact inh_Ord. (* .no-out *)
Qed. (* .no-out *)
(* end snippet inhOrd *)


#[ global ] Instance Inh_OSets : InH (Ensemble Ord).
Proof.
  split; apply Empty_set.
Qed.

#[ global ] Instance Inh_Ord_Ord : InH (Ord -> Ord).
Proof.
  split;  exact (fun (alpha:Ord) => alpha).
Qed.



#[global] Hint Resolve  AX1 Inh_Ord_Ord Inh_OSets inh_Ord : schutte.

Definition le := Le lt.


Infix "<=" := le : schutte_scope.


(** Second and third axioms from Schutte

A subset X of Ord is bounded iff X is countable *)

(* begin snippet AX23 *)

Axiom AX2 :
  forall X: Ensemble Ord,
    (exists a,  (forall y, In X y -> y < a)) ->
    countable X.

Axiom AX3 :
  forall X : Ensemble Ord,
    countable X ->
    exists a,  forall y, In X y -> y < a.

(* end snippet AX23 *)

(** * First definitions
*)

Definition ge alpha : Ensemble Ord := fun beta => alpha <= beta.

Definition Unbounded (X : Ensemble Ord) :=
  forall x: Ord,  exists y, In X y /\ x < y.






(* begin snippet zeroDef *)

Definition zero := the_least ordinal.
(* end snippet zeroDef *)

(* begin snippet succDef *)

Definition succ (alpha : Ord)
  := the_least (fun beta => alpha < beta).

(* end snippet succDef *)

(** Finite ordinals *)

(* begin snippet finiteDef *)

Fixpoint finite (i:nat) : Ord :=
  match i with 0 => zero
            | S i => succ (finite i)
  end.

Notation F i := (finite i).

Coercion finite : nat >-> Ord.

(* end snippet finiteDef *)


Definition is_finite  := seq_range finite.

(** ** Limits *)

(* begin snippet supDef *)

Definition sup_spec X lambda := is_lub ordinal lt X lambda.

Definition sup (X: Ensemble Ord) : Ord := the (sup_spec X).

Notation "'|_|' X" := (sup X) (at level 29) : schutte_scope.

(* end snippet supDef *)

(**  Limit of omega-sequences *)

(* begin snippet omegaDef *)

Definition omega_limit (s:nat->Ord) : Ord
  := |_| (seq_range s).

Definition _omega := omega_limit finite.

Notation omega := (_omega).

(* end snippet omegaDef *)

(** Successor and limit ordinals *)
(* begin snippet isSuccIsLimit *)

Definition is_succ (alpha:Ord)
  := exists beta, alpha = succ beta.

Definition is_limit (alpha:Ord)
  := alpha <> zero /\ ~ is_succ alpha.
(* end snippet isSuccIsLimit *)

(** Ordinals considered as sets *)

Definition members (a:Ord) := (fun b => b < a).

Definition set_eq (X Y: Ord -> Prop) := forall a,  (X a <-> Y a).

(** Induction (after Schutte) *)

Definition progressive (P : Ord -> Prop) : Prop :=
  forall a, (forall b,  b < a -> P b) -> P a.

(* begin snippet ClosedDef *)

Definition Closed (B : Ensemble Ord) : Prop :=
  forall M, Included M B -> Inhabited _ M -> countable M ->
                            In B (|_| M).

(* end snippet ClosedDef *)

Definition  continuous (f:Ord->Ord)(A B : Ensemble Ord) : Prop :=
  fun_codomain A B f /\
  Closed A /\
  (forall U, Included U A -> Inhabited _ U ->
             countable U -> |_| (image U f) = f (|_| U)).


(** *  Basic properties

*)


Lemma Unbounded_not_countable (X: Ensemble Ord) :
    Unbounded X -> not (countable X).
Proof.
  intros  H  H1; case (AX3 H1); intros x Hx.
  destruct (H x) as [x0 [H0 H2]].
  case (Lt_irreflexive (a:=x));  eapply (Lt_trans (WO:=AX1)); eauto.
Qed.

Lemma countable_not_Unbounded : forall X,
    countable  X -> not (Unbounded X).
Proof.
  red;intros; apply Unbounded_not_countable with X;auto.
Qed.

Lemma Progressive_Acc: progressive (Acc lt).
Proof.
  split; auto.
Qed.

Theorem transfinite_induction (P: Ord->Prop) : progressive P ->
                                 forall a,  P a.
Proof.
  intros Hp; case (classic  (forall a : Ord,  P a));
  [trivial|idtac].
  intro H; case (not_all_ex_not _ (fun a =>  P a) H).
  intros x Hx.
  assert False.
  {  case (well_order  (fun z => ~ P z) _ Hx (WO := AX1)).
     intros x0 H0; assert (forall b,  b < x0 -> P b).
     {  intros.
        case H0; intros H3 H5; apply NNPP.
        intro H6.  case (H5 _ H6).
        intro;subst x0.
        case (Lt_irreflexive  (a:=b));auto.
        intro; case (Lt_irreflexive   (a:=b)).
        eapply Lt_trans; eauto.
        exact AX1.
      }
     assert (~ (P x0)) by (case H0; unfold In; tauto).
     apply H2; apply Hp;auto.
  }
  contradiction.
Qed.


(** ** Properties of [le] and [lt] *)

Lemma le_refl : forall alpha,  alpha <= alpha.
Proof.
  left;auto.
Qed.

#[global] Hint Resolve le_refl : schutte.

Lemma eq_le : forall a b : Ord,  a = b -> a <= b.
Proof.
  left;auto.
Qed.

Lemma lt_le : forall a b: Ord, a < b -> a <= b.
Proof.
  right;auto.
Qed.

Lemma lt_trans : forall a b c : Ord, a < b ->  b < c -> a < c.
Proof.
  intros; eapply Lt_trans; eauto with schutte.
Qed.

Lemma le_lt_trans : forall a b c, a <= b -> b < c -> a < c.
Proof.
  apply Le_Lt_trans; eauto with schutte.
Qed.

Lemma lt_le_trans : forall a b c, a < b -> b <= c -> a < c.
Proof (Lt_Le_trans AX1).

Lemma le_trans : forall a b c, a <= b -> b <= c -> a <= c.
Proof (Le_trans AX1).

Lemma lt_irrefl : forall a, ~ (a < a).
Proof.
  intros a Ha; now apply ( @Lt_irreflexive  Ord  lt AX1 a).
Qed.

Lemma le_antisym : forall a b, a <= b -> b <= a -> a = b.
Proof (Le_antisym AX1).

Lemma le_eq_or_lt : forall a b, a <= b -> a = b \/ a < b.
Proof.
  intros a b [H |H];auto.
Qed.


Lemma le_not_gt : forall a b, a <= b -> ~ b < a.
Proof.
  intros a b H; case (le_eq_or_lt H).
  -  intro;subst b;apply lt_irrefl.
  -  intros H0 H1;case (@lt_irrefl a);eapply lt_trans;eauto.
Qed.

#[global] Hint Resolve eq_le lt_le lt_trans le_trans le_lt_trans
     lt_le_trans lt_irrefl le_not_gt:
  schutte.


Lemma le_disj : forall alpha beta, alpha <= beta ->
                                   alpha = beta \/ alpha < beta.
Proof.
  intros alpha beta H; destruct H; tauto.
Qed.


Lemma all_ord_acc : forall alpha : Ord,  Acc lt alpha.
Proof.
  intros alpha ;  pattern alpha;  apply transfinite_induction; auto.
  apply Progressive_Acc; auto.
Qed.

Lemma trichotomy : forall a b : Ord ,
                               a < b \/ a = b \/ b < a.
Proof (Lt_connect AX1).

(* begin hide *)

Ltac tricho t u Hname :=
                         case (@trichotomy t u);
                     [
                       intro Hname |
                       intros [Hname|Hname]].

(* end hide *)


Lemma lt_or_ge : forall a b: Ord, a < b \/ b <= a.
Proof.
  intros a b ; tricho a b H;auto with schutte.
Qed.


Lemma not_gt_le : forall a b,  ~ b < a  -> a <= b.
Proof.
  intros a b  H1; tricho a b H2; auto with schutte;  contradiction.
Qed.

#[global] Hint Unfold Included : schutte.

(** ** Global properties *)


Theorem Non_denum : ~ countable (Full_set Ord).
Proof.
  red; intro H; case (AX3  H); auto.
  intros x H0; case (@lt_irrefl x);apply H0; split.
Qed.



Lemma Inh_ord : Inhabited _ ordinal.
Proof.
  destruct inh_Ord as [x];  exists x; split.
Qed.


Theorem unbounded : forall alpha,  exists beta,  alpha < beta.
Proof.
  intros alpha ; pose (X0 := fun z =>  z < alpha).
  assert (countable X0).
  { apply AX2.
    unfold X0, Included, In; intuition.
    now exists alpha.
  }
  pose (X:= Add  _ X0 alpha).
  assert (countable X).
  {  unfold X; unfold Add; apply countable_union.
     auto.
     apply countable_singleton.
  }
  case (AX3  H0);  intros x Hx.
  assert (H1: X alpha).
  {
     unfold X; right; split.
   }
  specialize (Hx alpha H1);  exists x;auto.
Qed.


Lemma the_least_ok : forall X, Inhabited Ord X ->
                               forall a, In X a -> the_least X <= a.
Proof.
  intros X H a H0;   pattern X, (the_least X).
  unfold the_least, the;apply iota_ind.
  -  apply the_least_unicity.
    now exists a.
  - intros a0 H2;  destruct H2;  now apply H1.
Qed.


(** ** About zero *)


(* begin snippet zeroLe *)

Lemma zero_le (alpha : Ord) : zero <= alpha. (* .no-out *)
Proof. (* .no-out *)
  unfold zero, the_least, the; apply iota_ind.
  -  (* .no-out *) apply the_least_unicity, Inh_ord.
  -  (* .no-out *) destruct 1 as [[_ H1] _]; apply H1; split.
Qed.

(* end snippet zeroLe *)

Lemma not_lt_zero : forall alpha,  ~ alpha < zero.
Proof.
  intros;apply le_not_gt; apply zero_le;auto.
Qed.

Lemma zero_or_greater : forall alpha : Ord,
    alpha = zero \/ exists beta, beta < alpha.
Proof.
  intros a; tricho zero a t;auto with schutte.
  -  right;exists zero;auto with schutte.
  -  case (not_lt_zero t).
Qed.

Lemma zero_or_positive : forall alpha,  alpha = zero \/ zero < alpha.
Proof.
  intros a ; tricho zero a t;auto with schutte;  case (not_lt_zero   t).
Qed.



(** **  Properties of successor *)

(* begin snippet succSpec *)

Definition succ_spec (alpha:Ord) :=
  least_member lt (fun z => alpha < z).
(* end snippet succSpec *)

(* begin snippet succOka *)

Lemma succ_ok :
  forall alpha,  succ_spec alpha  (succ alpha). (* .no-out *)
Proof. (* .no-out *)
  intro alpha; unfold succ, the_least, the; apply iota_spec.
  (* end snippet succOka *)

  (* begin snippet succOkb *)

  (*| .. coq:: no-out |*)
  destruct (@AX3 (Singleton _ alpha)).
  - apply countable_singleton.
  - unfold succ_spec; apply the_least_unicity; exists x; intuition.
Qed.
(*||*)
(* end snippet succOkb *)

(* begin snippet succProps *)

(*| .. coq:: no-out |*)

Lemma lt_succ (alpha : Ord): alpha < succ alpha.
Proof.
  destruct  (succ_ok  alpha); tauto.
Qed.

#[global] Hint Resolve lt_succ : schutte. (* .none *)

Lemma lt_succ_le (alpha beta : Ord):
  alpha < beta -> succ alpha <= beta.
Proof with eauto with schutte.
  intros  H;  pattern (succ alpha); apply the_least_ok ...
  exists (succ alpha); red;apply lt_succ ...
Qed.
(*||*)


Lemma lt_succ_le_2 (alpha beta : Ord):
  alpha < succ beta -> alpha <= beta. (* .no-out *)
 (*| .. coq:: none |*)
Proof.
  intro H;  tricho alpha beta t;eauto with schutte.
  case (@lt_irrefl alpha);  apply lt_le_trans with (succ beta).
  - assumption.
  - apply lt_succ_le;eauto with schutte.
Qed.
(*||*)

Lemma succ_mono (alpha beta : Ord):
  alpha < beta -> succ alpha < succ beta. (* .no-out *)
 (*| .. coq:: none |*)
Proof with eauto with schutte.
  intros; eapply le_lt_trans with beta  ...
  - eapply lt_succ_le ...
Qed.

Arguments succ_mono [ alpha beta].
(*||*)

Lemma succ_monoR (alpha beta : Ord) :
 succ alpha < succ beta -> alpha < beta. (* .no-out *)
 (*| .. coq:: none |*)
Proof.
  intro H;  tricho alpha beta t; auto with schutte.
  -  subst beta; case (@lt_irrefl (succ alpha)); eauto with schutte.
  - case (@lt_irrefl  (succ alpha)); eapply lt_trans;eauto.
    apply succ_mono;auto.
Qed.
(*||*)

Lemma succ_injection (alpha beta : Ord) :
  succ alpha = succ beta -> alpha = beta. (* .no-out *)
 (*| .. coq:: none |*)
Proof.
  intros  H; tricho alpha beta t;auto.
  - generalize (succ_mono t).
    rewrite H; intro; case (@lt_irrefl (succ beta));auto.
  - generalize (succ_mono  t).
   rewrite H; intro; case (@lt_irrefl (succ beta));auto.
Qed.
(*||*)

Lemma succ_zero_diff (alpha : Ord): succ alpha <> zero. (* .no-out *)
 (*| .. coq:: none |*)
Proof.
  intros  H; destruct (@not_lt_zero alpha).
  rewrite <- H; auto with schutte.
Qed.
(*||*)


Lemma zero_lt_succ : forall alpha,  zero < succ alpha. (* .no-out *)
 (*| .. coq:: none |*)
Proof.
  intros a;  apply le_lt_trans with a;eauto with schutte;
    apply zero_le;auto.
Qed.
(*||*)

Lemma lt_succ_lt (alpha beta : Ord) :
  is_limit beta ->  alpha < beta -> succ alpha < beta. (* .no-out *)
 (*| .. coq:: none |*)
Proof.
  intros (Hbeta, Hbeta') H;  case (lt_succ_le  H); [|auto].
  - intros H' ; subst ;  case Hbeta'.
    exists alpha;split; eauto with schutte.
Qed.
(*||*)

(* end snippet succProps *)

#[global] Hint Resolve zero_lt_succ zero_le : schutte.

(** Less than finite is finite ... *)

Lemma finite_lt_inv : forall i o,
    o < F i ->
    exists j:nat , (j<i)%nat /\ o = F j.
Proof.
  induction i.
  - simpl (F 0); intros ; destruct (not_lt_zero  H ).
  - simpl (F (S i));intros o H; destruct (@lt_succ_le_2 o (F i));
      auto with schutte.
    +  exists i; split; auto.
    + destruct (IHi o  H0) as [x [H1 H2]].
      exists x; case H1;auto with arith.
Qed.

Lemma finite_mono : forall i j, (i<j)%nat -> F i < F j.
Proof.
  induction 1.
  -  simpl (finite (S i)); auto with schutte.
  -  apply lt_trans  with (finite m);auto.
     simpl (finite (S m)); apply lt_succ; auto with schutte.
Qed.

#[global] Hint Resolve finite_mono : schutte.

Lemma finite_inj : forall i j, F i = F j -> i = j.
Proof.
  intros i j H; case (lt_eq_lt_dec i j).
  -  destruct 1.
     +  case (@lt_irrefl (F i)).
        *  pattern (F i) at 2 ; rewrite H.
           apply finite_mono;auto.
     + auto.
  -  intro;  case (@lt_irrefl (F i)).
     pattern (F i) at 1 ; rewrite H; apply finite_mono;auto.
Qed.

(**  ** Building limits *)

Lemma sup_exists : forall X, countable  X ->
                             ex (sup_spec  X).
Proof.
  intros X H; case (AX3 H); auto.
  intros x H'x;
  assert (H''x : forall y : Ord, X y -> y=x \/ lt y x) by  intuition.
  generalize  (@well_order   Ord lt  AX1
                             (fun z =>
                                (forall y,   X y -> y = z \/ y < z))
                             x ).
  intros H1; destruct H1 as [  x0 H0].
  {   red;  auto.  }
  exists x0; unfold least_member in H0; repeat split.
  -   case H0; intros; intuition.
        red in H1;   red;  intros; auto.
    -  intros y H1 H2;  decompose [and] H0.
       red in H2;  destruct (H4 y); auto.
       intros y0 H5;  specialize (H2 y0);  apply H2; auto with schutte.
Qed.

Lemma sup_unicity : forall X l l',
                      (countable  X /\ forall x, X x -> ordinal x) ->
                      sup_spec X l -> sup_spec X l' -> l = l'.
Proof.
  intros X l l' _ H H0; apply le_antisym.
  destruct H, H0; intuition.
  case (H4 l' H0);auto with schutte.
  destruct H, H0; intuition.
  case (H5 l H);auto with schutte.
Qed.

Lemma sup_spec_unicity (X:Ensemble Ord) (HX : countable X) :
  exists! u, sup_spec X u.
Proof.
  destruct (sup_exists  HX).
  exists x;split;auto.
  intros;  apply sup_unicity with   X;split;auto.
  1, 2, 4 : split.
  -  destruct H; tauto.
  - destruct H0; tauto.
Qed.


Lemma sup_ok1 (X: Ensemble Ord)(HX : countable X) :
  sup_spec X (sup X).
Proof.
  unfold sup, the;  apply iota_spec;  now apply sup_spec_unicity.
Qed.

Lemma sup_upper_bound (X : Ensemble Ord) (alpha : Ord):
  countable X ->  In X alpha -> alpha <= |_|  X.
Proof.
  intros  H  H1;  generalize (sup_ok1   H).
  intro H2;  destruct H2 as [H2 [H3 H4]].
  destruct (H3 alpha); auto with schutte.
Qed.


Lemma sup_least_upper_bound (X : Ensemble Ord) (alpha : Ord) :
  countable X -> (forall y, In X y -> y <= alpha) -> sup  X <= alpha.
Proof.
   intros  H H0;  specialize (sup_ok1   H) as H1.
    destruct H1 as [H1 [H2 H3]].
    destruct  (H3 alpha); auto with schutte.
    red;  intros;  apply H0; auto.
Qed.

Lemma sup_of_leq (alpha : Ord) :
    alpha = |_| (fun x : Ord =>  x <= alpha).
Proof.
 assert (DD :countable (fun x : Ord =>  x <= alpha)).
  {
    apply AX2.
    -   exists (succ alpha);
       destruct 1; apply le_lt_trans with alpha;auto with schutte.
  }
  apply le_antisym.
  - apply sup_upper_bound; auto with schutte.
  - apply sup_least_upper_bound;auto.
Qed.


Lemma sup_mono (X Y : Ensemble Ord) :
    countable X ->
    countable Y ->
    (forall x, In X x -> exists y, In Y y /\ x <= y) ->
|_| X <= |_| Y.
Proof.
  intros H H0 H1;
  apply sup_least_upper_bound; auto with schutte.
  intros x Hx; case (H1 x Hx); intros y (Hy,Hy').
  apply le_trans  with y;auto with schutte.
  apply sup_upper_bound;auto with schutte.
Qed.

Lemma sup_eq_intro (X Y : Ensemble Ord):
  countable X -> countable Y ->
  Included X Y -> Included Y X ->
|_| X = |_| Y.
Proof.
  unfold Included, In; intros; apply le_antisym;
    apply sup_mono;auto with schutte;
  intro x;exists x; unfold In;auto with schutte.
Qed.


Lemma lt_sup_exists_leq (X: Ensemble Ord) :
  countable X ->
  forall y, y < sup X ->
            exists x, In X x /\ y <= x.
Proof.
  intros;  case (not_all_not_ex _ (fun x =>  X x /\ y <= x)).
  -   intro H3;  unfold Included,In in H0.
      assert (forall n, X n -> n < y).
      { intros n H4;  apply NNPP; intro H5.
         assert (y < n).
        { case (@trichotomy n y); auto.
           - intro; case H5;auto.
           - destruct 1.
             +  subst n ; case (H3 y).
                auto with schutte.
             + auto.
         }
        case (H3 n).
        split;auto with schutte.
      }
      case ( @lt_irrefl y).
      eapply lt_le_trans with (|_|X);eauto.
      apply sup_least_upper_bound;auto with schutte.
  -  intros x Hx; exists x;auto.
Qed.

Lemma lt_sup_exists_lt (X : Ensemble Ord) :
  countable X ->
  forall y,  y < sup X -> exists x, In X x /\ y < x.
Proof.
  intros  H y H0;
  case (not_all_not_ex _ (fun x =>  X x /\ y < x)).
 -  red;intro H1;
      assert (forall n, X n -> n <= y).
    {  intros n H4; apply NNPP.
       intro H5.
       assert (y < n).
       { case (@trichotomy n y).
         -   intro H6;   case H5;auto with schutte.
         -  destruct 1.
            +   case H5;auto with schutte.
            +   auto.
       }
       case (H1 n); split;auto with schutte.
    }
    assert (sup X <= y).
    {  apply sup_least_upper_bound; auto. }
    case (@Lt_irreflexive Ord  lt AX1  y).
    eapply Lt_Le_trans;eauto with schutte.
 - intros x Hx; exists x;auto.
  Qed.

Lemma members_eq (alpha beta : Ord) :
  members alpha = members beta -> alpha = beta.
Proof.
  intros  H; tricho alpha beta H2; auto with schutte.
  -   assert (H0: members beta alpha) by auto.
      rewrite <- H in H0;  destruct (lt_irrefl H0);auto.
  - assert (H0: members alpha beta) by auto.
    rewrite  H in H0;  destruct (lt_irrefl H0);auto.
Qed.


Lemma sup_members_succ (alpha : Ord) :
  sup (members alpha) < alpha -> alpha = succ (|_| (members alpha)).
Proof.
  intros  H;pose (A := sup (members alpha)).
  fold A;  generalize (@lt_succ_le  A alpha).
  intros H0.
  case (le_eq_or_lt  (H0  H)).
  -   symmetry;auto.
  -  intro H3;   assert (succ A <= A).
     {
       unfold A;apply sup_upper_bound.
       - apply AX2; exists alpha;unfold members; auto.
       - assumption.
     }
     destruct (@lt_irrefl A); apply lt_le_trans with (succ A); auto.
    +     eapply lt_succ;auto.
Qed.


Lemma sup_members_not_succ (alpha beta : Ord) :
  alpha = sup (members alpha) ->  alpha <> succ beta.
Proof.
  intros   e e1;  generalize (sup_of_leq  beta).
  intro H; assert (sup (members alpha) = beta).
  {
    unfold members;rewrite H;
      apply sup_eq_intro.
    - apply AX2; exists alpha; auto.
    - apply AX2;  exists (succ beta);  intros y Hy;
       eauto with schutte.
    - red;   intros;  red; red in H0; rewrite e1 in H0.
      apply lt_succ_le_2;auto.
    -  unfold Included, In; intros x H1;  rewrite e1.
       eapply le_lt_trans;eauto with schutte.
  }
  case (@lt_irrefl alpha); pattern alpha at 2;rewrite e1, e, H0;
    auto with schutte.
Qed.

(** ** Sequences of ordinals *)


Definition seq_mono (s:nat -> Ord) :=
  forall i j, (i < j)%nat -> s i < s j.

Lemma seq_mono_intro (s: nat -> Ord) :
  (forall i, s i <  s (S i)) -> seq_mono s.
Proof.
  intros  H; unfold seq_mono; induction 1;  auto.
  apply (@Lt_trans Ord  lt AX1)  with (s m);auto.
Qed.


Lemma seq_mono_inj (s : nat -> Ord) :
  seq_mono s -> injective _ _ s.
Proof.
  unfold injective;intros  H i j H0.
  case (lt_eq_lt_dec i j).
  -   destruct 1; auto.
   + generalize (H _ _ l); auto.
     rewrite H0;intro;case (@Lt_irreflexive Ord  lt AX1  (s j));auto.
  - intro l;generalize (H _ _ l).
    rewrite H0;intro;case (@Lt_irreflexive  Ord lt AX1 (s j));auto.
Qed.

#[global] Hint Resolve Countable.seq_range_countable seq_mono_intro : schutte.

#[global] Hint Constructors Full_set: core.

Lemma lt_omega_limit (s : nat -> Ord) :
  seq_mono s -> forall i, s i <  omega_limit s.
Proof.
  unfold omega_limit;intros.
  apply lt_le_trans with (s (S i)).
  -  eapply H;  auto.
  -  apply sup_upper_bound;auto with schutte.
     exists (S i);split;auto.
Qed.


Lemma omega_limit_least (s : nat -> Ord) :
    seq_mono s ->
    forall y : Ord,
      (forall i, s i < y) ->
      omega_limit s <=  y.
Proof.
  intros  H y  H1.
  unfold omega_limit;apply sup_least_upper_bound;auto with schutte.
  intro y0; destruct 1 as [x [_ e]]; subst y0;auto.
  right; auto.
Qed.


Lemma lt_omega_limit_lt_exists_lt (alpha : Ord) (s : nat -> Ord) :
  (forall i, s i < s (S i)) ->
  alpha < omega_limit s ->
  exists j, alpha < s j.
Proof.
  intros H H0;  unfold omega_limit in H0.
  assert (exists y, In (seq_range s) y /\ alpha <  y).
  apply lt_sup_exists_lt; auto with schutte.
  destruct H1 as [y [[j [_ Hj]] H'y]]; subst y; now exists j.
Qed.


Lemma omega_limit_least_gt (alpha : Ord) (s : nat -> Ord)
      (Hmono : forall i, s i < s (S i))
      (H : alpha < omega_limit s) :
  exists i, least_member Peano.lt (fun j =>  alpha <  s j) i.

Proof.
  destruct (lt_omega_limit_lt_exists_lt s Hmono H ) as [i Hi].
  destruct (well_order (fun i =>  alpha < s i) i) as [x Hx]; trivial.
  now  exists x.
Qed.

(** ** Properties of omega *)

(* begin snippet omegaPropsa:: no-out *)
Lemma finite_lt_omega (i : nat) : i < omega.
(* end snippet omegaPropsa *)
Proof.
   intros; apply lt_omega_limit; auto with schutte.
Qed.


(* begin snippet omegaPropsb:: no-out *)
Lemma zero_lt_omega : zero < omega.
Proof.
  change zero with (F 0); apply finite_lt_omega.
Qed.
(* end snippet omegaPropsb *)

(* begin snippet omegaPropsc:: no-out *)
Lemma lt_omega_finite (alpha : Ord) :
  alpha < omega ->  exists i:nat, alpha = i.
(* end snippet omegaPropsc *)
Proof.
  intro H0; unfold omega_limit in H0.
  generalize (lt_sup_exists_leq (X:=(seq_range finite))  ).
  intros;  assert (countable (seq_range finite)) by
    apply seq_range_countable.
  generalize (H H1);clear H;intros.
  generalize (H _ H0);clear H;intros.
  destruct H as [x [H2 H3]].
  destruct H2 as [x0 [_ e]].  subst x.
  destruct (le_disj H3).
  -  exists x0; auto.
  - destruct  (finite_lt_inv x0 H);auto.
    exists x; tauto.
Qed.

(* begin snippet omegaPropsd:: no-out *)
Lemma is_limit_omega : is_limit omega.
(* end snippet omegaPropsd *)
Proof.
  repeat split; auto with schutte.
  - intro H;  absurd (F 1 < zero).
    +   apply not_lt_zero;auto with schutte.
    +   rewrite <- H;   apply finite_lt_omega.
  - destruct 1 as [x Hx].
  assert (x < omega).
  {  rewrite Hx;auto with schutte. }
  destruct (lt_omega_finite  H); subst x.
  assert (omega = F (S x0)) by (simpl; trivial).
  case ( @lt_irrefl omega);auto with schutte.
  pattern omega at 1;rewrite H0;auto with schutte.
  apply finite_lt_omega;auto with schutte.
Qed.


(** ** About zero, is_succ and is_limit *)

Lemma not_is_succ_zero : ~ is_succ zero.
Proof.
   intros (b, Hb);  apply (succ_zero_diff  b); now symmetry.
Qed.


Lemma not_is_limit_zero : ~ is_limit zero.
Proof.
  unfold is_limit;   tauto.
Qed.

Lemma not_is_limit_succ (alpha : Ord) :  is_succ alpha -> ~ is_limit alpha.
Proof.
  unfold is_limit;tauto.
Qed.

Lemma not_is_succ_limit (alpha : Ord) : is_limit alpha -> ~ is_succ alpha.
Proof.
  unfold is_limit;tauto.
Qed.


(** ** About members *)

Lemma countable_members (alpha : Ord): countable (members alpha).
Proof.
 apply AX2;   now exists alpha.
Qed.

#[global] Hint Resolve countable_members : schutte.

Lemma le_sup_members (alpha : Ord) :  |_| (members alpha) <= alpha.
Proof.
  intros; apply sup_least_upper_bound; auto with schutte.
Qed.

Lemma is_limit_sup_members (alpha : Ord) :
  is_limit alpha -> alpha = |_| (members alpha).
Proof.
  intros;  case (@le_sup_members alpha);auto with schutte.
  intro H0;  generalize (@sup_members_succ alpha).
  intros H1 ;  destruct  (not_is_limit_succ (alpha:=alpha));auto with schutte.
  exists (|_|members alpha); auto.
Qed.


Lemma sup_members_disj (alpha : Ord) :
  alpha = sup (members alpha) ->
  alpha = zero \/ is_limit alpha.
Proof.
  intro H;  unfold is_limit.
  case (classic (alpha=zero)).
  -   auto.
  -  right;repeat split;auto.
      red; destruct 1 as [x Hx].
      case (sup_members_not_succ  x H Hx).
Qed.


Theorem classification (alpha : Ord) :
  alpha = zero \/ is_succ alpha \/  is_limit alpha.
Proof.
 case (le_sup_members  alpha).
  - intro H;  symmetry in H; case (sup_members_disj  H);auto with schutte.
  -  right; left; exists (sup (members alpha));
       apply sup_members_succ;auto.
Qed.


(**   ** Extensional equalities on sets of ordinals *)

Lemma members_omega :  Same_set (members omega) is_finite.
Proof.
  unfold Same_set;split;
      red; unfold members, In.
  - intros x Hx; case (lt_omega_finite  Hx); intros x0; exists x0; auto.
  -   destruct 1 as [n [_ Hn]];   subst ;auto with schutte.
      apply finite_lt_omega.
Qed.


Lemma Not_Unbounded_bounded (X: Ensemble Ord):
   ~ Unbounded X ->
   exists beta : Ord, forall x, In X x -> x < beta.
Proof.
  intros  H; apply NNPP; intro H0.
  assert (forall beta,  exists x, In X x /\ beta <= x).
  { intros beta;  change (exists x:Ord, (fun y => In X y /\ beta <= y) x).
  apply not_all_not_ex.
  intro H1;  case H0;  exists beta; auto.
  - intros x H2;  tricho x beta H5;auto with schutte.
   +  case (H1 x).
      split;auto with schutte.
   +  case (H1 x);split;auto with schutte.
  }
  clear H0;  case H; intro x.
  destruct (H1 (succ x)) as [y [H2 H3]].
  exists y;split;auto with schutte.
  apply lt_le_trans with (succ x); auto with schutte.
Qed.


Lemma Not_Unbounded_countable (X : Ensemble Ord) :
  ~ Unbounded X ->   countable X.
Proof.
  intros;eapply AX2;eauto.
  case (Not_Unbounded_bounded H);auto.
  intros x H0; exists x;auto.
Qed.

Lemma not_countable_unbounded (X : Ensemble Ord):
    ~ countable X -> Unbounded X.
Proof.
  intros H;  apply NNPP; intro H0.
  apply H,  Not_Unbounded_countable;auto.
Qed.


Lemma le_alpha_zero (alpha : Ord) :
  alpha <= zero -> alpha = zero.
Proof.
  intros H;  apply le_antisym;auto.
  apply zero_le.
Qed.


Lemma finite_not_limit (i: nat): ~ is_limit i.
Proof.
 destruct i.
 -  simpl; apply not_is_limit_zero.
 -  simpl. intros [_ H0]; apply H0;   now exists (F i).
Qed.


(* begin hide *)

Module iota_demo.

  (* begin snippet iotaDemoa:: no-out  *)
  Remark R : exists! z : Ord, least_member lt  ordinal z.
  Proof.
    destruct inh_Ord as [a ];
      apply least_member_ex_unique with a.
    - apply AX1.
    - split.
  Qed.
  (* end snippet iotaDemoa *)

 (* begin snippet iotaDemob *)
  Definition zero : Ord. (* .no-out *)
  Proof. (* .no-out *)
    Fail destruct R.
  Abort.

  (* end snippet iotaDemob *)

(* end hide *)

Definition zero: Ord := iota inh_Ord (least_member lt ordinal).

Lemma zero_le (alpha : Ord) :  zero <= alpha.
Proof.
  generalize (iota_spec inh_Ord _ R).
  destruct 1 as [_ H]; apply H; split.
Qed.

(* begin snippet BadBottoma:: no-out *)
Module Bad.

  Definition bottom := the_least (Empty_set Ord).
(* end snippet BadBottoma *)

  (* begin snippet trivialProps:: no-out *)
  Lemma le_zero_bottom : zero <= bottom.
  Proof. apply zero_le. Qed.

  Lemma bottom_eq : bottom = bottom.
  Proof. trivial. Qed.
  (* end snippet trivialProps *)

  (* begin snippet Failure *)
  Lemma le_bottom_zero : bottom <= zero. (* .no-out *)
  Proof. (* .no-out *)
    unfold bottom, the_least, the; apply iota_ind.
  Abort.

End Bad.
(* end snippet Failure *)

End iota_demo.






















































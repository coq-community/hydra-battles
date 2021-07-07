(** Pierre Castéran, Univ. Bordeaux and LaBRI *)

(** This module defines a type class of ordinal notations, _i.e._, data types
    with a well-founded strict order  and a [compare] function *)


From Coq Require Import RelationClasses Relation_Operators Ensembles.
From hydras Require Import  OrdNotations Schutte_basics.
From Coq Require Export Wellfounded.Inverse_Image Wellfounded.Inclusion.
Import Relation_Definitions.
From hydras Require Export MoreOrders.
Require Export Comparable.
  
Generalizable All Variables.
Declare Scope ON_scope.
Delimit Scope ON_scope with on.
Local Open Scope ON_scope.

(**
  Ordinal notation system on type [A] :
*)

Class ON {A:Type}(lt: relation A)
      (compare: A -> A -> comparison)  :=
  {
  comp :> Comparable lt compare;
  wf : well_founded lt;
  }.

Section Definitions.
  Context  {A:Type}{lt : relation A}
           {compare : A -> A -> comparison}
           {on : ON lt compare}.
  
  #[using="All"]
   Definition ON_t := A.

  #[using="All"]
   Definition ON_compare := compare.

  #[using="All"]
   Definition ON_lt := lt.

  #[using="All"]
   Definition ON_le:  relation A := leq lt.

  #[using="All"]
   Definition measure_lt {B : Type} (m : B -> A) : relation B :=
    fun x y =>  ON_lt (m x) (m y).

  #[using="All"]
   Lemma wf_measure {B : Type} (m : B -> A) :
    well_founded (measure_lt m). 
  Proof.
    intro x; eapply Acc_incl  with (fun x y =>  ON_lt (m x) (m  y)).
    - intros y z H; apply H.
    - eapply Acc_inverse_image, wf.
  Qed.

 #[using="All"]
Definition ZeroLimitSucc_dec :=
  forall alpha,
    {Least alpha} +
    {Limit alpha} +
    {beta: A | Successor alpha beta}.


End Definitions.

Infix "o<" := ON_lt : ON_scope.
Infix "o<=" := ON_le : ON_scope.

Global Hint Resolve wf_measure : core.



Lemma le_lt_trans {A:Type}(lt : relation A)
            {compare : A -> A -> comparison}
            {on : ON lt compare}:
  forall p q r: A, leq lt p q -> lt q r -> lt p r.
Proof.
  intros * H;  destruct H; [| trivial].
  intro; now transitivity y.
Qed.   

Lemma lt_le_trans {A:Type}(lt: relation A)
            {compare : A -> A -> comparison}
            {on : ON lt compare}:
  forall p q r, lt p q -> leq lt q r -> lt p r.
Proof.
  intros * H H0; rewrite le_lt_eq in H0;  destruct H0.
  - now  transitivity q.
  - now  subst.
Qed.   


(** The segment called [O alpha] in Schutte's book *)

Definition bigO `{nA : @ON A ltA compareA}
           (a: A) : Ensemble A := fun x: A => ltA x a.

(** The segment associated with nA is isomorphic to
    the segment of ordinals strictly less than b *)

Class  SubON 
       `(OA: @ON A ltA compareA)
       `(OB: @ON B ltB compareB)
       (alpha:  B)
       (iota: A -> B):=
  {
  SubON_compare :forall x y : A,  compareB (iota x) (iota y) =
                                 compareA x y;
  SubON_incl : forall x, ltB (iota x) alpha;
  SubON_onto : forall y, ltB y alpha  -> exists x:A, iota x = y}.

(** [OA] and [OB] are order-isomporphic *)
Class  ON_Iso 
       `(OA : @ON A ltA compareA)
       `(OB : @ON B ltB compareB)
       (f : A -> B)
       (g : B -> A):=
  {
  iso_compare :forall x y : A,  compareB (f x) (f y) =
                                compareA x y;
  iso_inv1 : forall a, g (f a)= a;
  iso_inv2 : forall b, f (g b) = b
  }.

(** OA is an ordinal notation for alpha (in Schutte's model) *)

Class ON_correct `(alpha : Ord)
     `(OA : @ON A ltA compareA)
      (iota : A -> Ord) :=
  { ON_correct_inj : forall a, lt (iota a) alpha;
    ON_correct_onto : forall beta, lt beta alpha ->
                                exists b, iota b = beta;
    On_compare_spec : forall a b:A,
        match compareA a b with
          Datatypes.Lt => lt (iota a) (iota b)
        | Datatypes.Eq => iota a = iota b
        | Datatypes.Gt => lt (iota b) (iota a)
        end
  }.



(** ** Relative correctness of a constant or a function  *)

Definition SubON_same_cst `{OA : @ON A ltA  compareA}
       `{OB : @ON B ltB  compareB}
       {iota : A -> B} 
       {alpha: B}
       {_ : SubON OA OB alpha iota}
       (a : A)
       (b : B)
  := iota a = b.



Definition SubON_same_fun `{OA : @ON A ltA  compareA}
       `{OB : @ON B ltB  compareB}
       {iota : A -> B} 
       {alpha: B}
       {_ : SubON OA OB alpha iota}
       (f : A -> A)
       (g : B -> B)
  := forall x,  iota (f x) = g (iota x).


Definition SubON_same_op `{OA : @ON A ltA compareA}
       `{OB : @ON B ltB  compareB}
       {iota : A -> B} 
       {alpha: B}
       {_ : SubON OA OB alpha iota}
       (f : A -> A -> A)
       (g : B -> B -> B)
  :=
  forall x y,  iota (f x y) = g (iota x) (iota y).


(** Correctness w.r.t. Schutte's model *)


Definition ON_cst_ok  {alpha: Ord} `{OA : @ON A ltA compareA}
       `{OB : @ON B ltB  compareB}
       {iota : A -> Ord} 
       {_ : ON_correct alpha OA iota}
       (a: A)
       (b: Ord)
  := iota a = b.



Definition ON_fun_ok  {alpha: Ord} `{OA : @ON A ltA   compareA}
       `{OB : @ON B ltB   compareB}
       {iota : A -> Ord} 
       {_ : ON_correct alpha OA iota}
       (f : A -> A)
       (g : Ord  -> Ord)
  :=
    forall x,  iota (f x) = g (iota x).

Definition ON_op_ok  {alpha: Ord} `{OA : @ON A ltA  compareA}
       `{OB : @ON B ltB compareB}
       {iota : A -> Ord} 
       {_ : ON_correct alpha OA iota}
       (f : A -> A -> A)
       (g : Ord -> Ord -> Ord)
  :=
    forall x y,  iota (f x y) = g (iota x) (iota y).




Definition Iso_same_cst  `{OA : @ON A ltA  compareA}
       `{OB : @ON B ltB  compareB}
       {f : A -> B} {g : B -> A}
       {_ : ON_Iso  OA OB f g}
       (a : A)
       (b : B)
  := f a = b.



Definition Iso_same_fun  `{OA : @ON A ltA  compareA}
           `{OB : @ON B ltB  compareB}
           {f : A -> B} {g : B -> A}
           {_ : ON_Iso  OA OB f g}
           (fA : A -> A)
           (fB : B -> B)
  :=
    forall x,  f (fA x) = fB (f x).


Definition Iso_same_op  `{OA : @ON A ltA  compareA}
           `{OB : @ON B ltB  compareB}
           {f : A -> B} {g : B -> A}
           {_ : ON_Iso  OA OB f g}
           (opA : A -> A -> A)
           (opB : B -> B -> B)
     
  :=
  forall x y,  f (opA x y) = opB (f x) (f y).


(** Technical lemmas *)

Lemma compare_Eq_eq  `{OA : @ON A ltA  compareA} alpha beta :
  compareA alpha beta = Eq <-> alpha = beta.
Proof.
  split.
  - intro H; destruct (compare_correct alpha beta); auto; discriminate.
  - intro; subst.
    destruct (compare_correct beta beta); auto.
    + destruct (StrictOrder_Irreflexive beta); trivial.   
    + destruct (StrictOrder_Irreflexive beta); trivial.   
Qed.


Lemma compare_Lt_lt  `{OA : @ON A ltA  compareA} alpha beta :
  compareA alpha beta = Lt <-> ltA alpha beta.
Proof.
  split.
  -  intro H; destruct (compare_correct alpha beta); auto; discriminate.
  - intro H.
    destruct (compare_correct alpha beta); auto.
    + subst; destruct (StrictOrder_Irreflexive beta); trivial.   
    + destruct (StrictOrder_Irreflexive beta); trivial.
      now transitivity alpha.
Qed.


Lemma compare_Gt_gt  `{OA : @ON A ltA  compareA} alpha beta :
  compareA alpha beta = Gt <-> ltA beta alpha.
Proof.
  split.
  - intro H; destruct (compare_correct alpha beta); auto; discriminate.
  -   destruct (compare_correct alpha beta); auto.
      + subst.  intro H ; destruct (StrictOrder_Irreflexive beta); trivial.   
      + intro H0; destruct (StrictOrder_Irreflexive beta); trivial.
        now transitivity alpha.
Qed.

(** TODO: Move to comparable ? *)
Lemma lt_eq_lt {A:Type}{lt : relation A}
            {compare : A -> A -> comparison}
            {on : ON lt compare} : 
  forall alpha beta, lt alpha  beta \/ alpha = beta \/ lt beta alpha.
Proof.
  intros; destruct (compare_correct alpha beta); auto.
Qed.

(** TODO: Move to comparable ? *)
Definition lt_eq_lt_dec {A:Type}{lt: relation A}
            {compare : A -> A -> comparison}
            {on : ON lt compare} (alpha beta : A) :
   {lt alpha  beta} + {alpha = beta} + {lt beta  alpha}.
  case_eq (compare alpha beta); intro H.
  - left;right; now rewrite <- compare_Eq_eq.
  - left; left; now rewrite <- compare_Lt_lt.
  - right; now rewrite <- compare_Gt_gt.
Defined.

(** TODO: Move to comparable ? *)
Lemma LimitNotSucc {A:Type}{lt: relation A}
           {compare : A -> A -> comparison}
           {on : ON lt compare}
           (alpha :A)  :
  Limit alpha -> forall beta, ~ Successor alpha beta.
Proof.
  intros [[w H] H0] beta [H1 H2].
  destruct (lt_eq_lt beta w) as [H3 | [H3 | H3]].
  - apply (H2 w);auto.
  - subst w;  destruct (H0 _ H1) as [z [H3 H4]]; apply (H2 z);auto.
  - destruct (H0 beta H1) as [z [H4 H5]]; eauto.
Qed.


Section SubON_properties.
  
  Context `{OA : @ON A ltA compareA}
          `{OB : @ON B ltB compareB}
          (f : A -> B)
          (alpha : B)
          (Su : SubON OA OB alpha f).

  Lemma SubON_mono a b : ltA a b <-> ltB (f a) (f b).
  Proof.
    split;intro H.
    - apply compare_Lt_lt in H; apply compare_Lt_lt;
      now rewrite SubON_compare.
    - apply compare_Lt_lt.
      specialize (@compare_Lt_lt B ltB compareB OB (f a) (f b));
        intro H0;rewrite <- H0 in H.
      now rewrite SubON_compare in H.
  Qed.    

  Lemma SubON_inj : forall a b, f a = f b -> a = b.
  Proof.
    intros a b H; apply compare_Eq_eq;
      apply compare_Eq_eq in H;
    now   rewrite SubON_compare in H.
  Qed.

  Lemma SubON_successor : forall a b,  Successor a b <-> Successor (f a) (f b).
  Proof.
    split; intro H.
    - destruct H.     
      split.
      +  now apply SubON_mono.
      + intros z Hz Hz';  destruct (SubON_onto z).
        * transitivity (f a); auto.       
          apply SubON_incl.
        * subst;  apply SubON_mono in Hz; apply SubON_mono in Hz'.
          eapply H0;eauto.
    - destruct H; split.
     +  now apply SubON_mono.
     + intros z Hz Hz';  specialize (H0 (f z)).
       apply H0; now apply SubON_mono.
  Qed.

  Lemma SubON_limit : forall a ,  Limit a  <-> Limit (f a).
  Proof.
    split; intro H.
    - destruct H ; split.
      + destruct H as [m Hm]; exists (f m); now apply SubON_mono.
      + intros y Hy; destruct (SubON_onto y) as [x Hx].
        * transitivity (f a); auto.       
          apply SubON_incl.
        * subst; apply SubON_mono in Hy.
          destruct (H0 _ Hy) as [z [Hz Hz']].
          exists (f z); split; apply SubON_mono; auto.
    - destruct H; split.
      +  destruct H as [w Hw]; destruct (SubON_onto w) as [x Hx].
         transitivity (f a); auto.
           * apply SubON_incl.
           * exists x; subst w; apply SubON_mono in Hw; auto.
      + intros y Hy; destruct (H0 (f y))  as [w [Hw Hw']].
        * apply SubON_mono; auto.
        * destruct (SubON_onto w) as [x Hx].
          transitivity (f a); auto; apply SubON_incl.
          subst w;   exists  x; split;apply SubON_mono; auto.
  Qed.     

  Lemma SubON_least : forall a ,  Least a  <-> Least (f a).
  Proof.
    split; intro H.
    - intros y; destruct (compare_correct (f a) y).
      + subst y; right.
      + now  left.
      + exfalso.
        { destruct (SubON_onto y).
          transitivity (f a); auto.
          apply SubON_incl.
          subst y;  apply SubON_mono in H0.
          destruct (H x).
          apply (StrictOrder_Irreflexive a).
          now transitivity y.
          apply (StrictOrder_Irreflexive a).
          auto.
        }
    - intro x; destruct (compare_correct a x).
      subst; right.
      + now left.
      + apply SubON_mono in H0; specialize (H (f x)).
      exfalso.
      { apply (StrictOrder_Irreflexive (f a)).
        destruct H.
        transitivity y; auto.
        auto.
      }
  Qed.
  
End SubON_properties.






(** * Partial functions *)

(** Pierre Casteran, Univ. Bordeaux and LaBRI  *)


(**  We study the relationship between  two representations of partial
   functions : relational presentation, and with the  [iota] description operator *)


From Coq Require Import ClassicalDescription Ensembles Image
  ProofIrrelevance.
Import ProofIrrelevanceFacts.
From ZornsLemma Require Import EnsemblesImplicit FunctionProperties ImageImplicit.
From hydras Require Import MoreEpsilonIota.

Set Implicit Arguments.

Section AB_given.
  Variables (A B : Type)
            (Ha : inhabited A)
            (Hb:inhabited B)
            (DA: Ensemble A)
            (DB : Ensemble B).

  (** ** Transformation of a functional relation into a function *)

Definition iota_fun (R:A->B-> Prop) : A -> B :=
  fun a =>  iota Hb (fun b':B => In DA a /\ R a b'  /\ In DB b').

Lemma iota_fun_e (R:A->B-> Prop):
  forall (a:A), In DA a ->
   (exists ! b, R a b /\ In DB b) ->
   unique (fun b => (R a b /\ In DB b)) (iota_fun   R a).
Proof.
 intros; unfold iota_fun; split.
 - apply iota_ind.
   destruct H0 as [y Hy]; exists y.
   destruct Hy;split.
   + tauto.
   + destruct 1;  auto.
   + destruct 1;  tauto.
 -  destruct 1.
    symmetry;apply iota_eq.
    + exists x';  split.
      * tauto.
      * destruct 1 as [H3 H4].
      destruct H0 as [x [H0 H5]].
      symmetry;auto.
      symmetry;auto.
      transitivity x.
      symmetry;apply H5;auto.
      apply H5;auto.
   + tauto.
Qed.

Lemma iota_fun_ind (P:A -> Prop)
      (Q R:A->B-> Prop):
  forall (a x:A), In DA a -> a = x ->
   (exists ! b, R a b /\ In DB b) ->
   P a ->
   (forall b,  unique (fun b => R a b /\  In DB b) b -> Q a b) ->
   Q x (iota_fun   R a).
Proof.
 intros a x H H0 H1 H2 H3;  subst x;  apply H3.
 generalize (iota_fun_e   R  H H1).
 intros H0; apply iota_fun_e; auto.
Qed.





Section f_given.

  Variable f : A -> B.

  (** relational representation *)

  Variable Rf : A -> B -> Prop.


  (** abstract properties of a function (relational representation ) *)

  Definition rel_domain := forall a, In DA a -> exists b, Rf a b .
  Definition rel_codomain := forall a b, In DA a -> Rf a b -> In DB b.
  Definition rel_functional := forall a b b', In DA a ->
                              Rf a b -> Rf a b' -> b = b'.
  Definition rel_onto := forall b, In DB b -> exists a, In DA a /\ Rf a b.
  Definition rel_inj := forall a a' b, In DA a ->
                                       In DA a' ->
                                       Rf a b ->
                                       Rf a' b ->
                                       a = a'.

  Inductive  rel_injection : Prop :=
   rel_inj_i : rel_domain ->  rel_codomain ->
        rel_functional ->
        rel_inj ->
        rel_injection.

  Inductive  rel_bijection : Prop :=
   rel_bij_i : rel_domain ->  rel_codomain ->
        rel_functional ->
        rel_onto ->
        rel_inj ->
        rel_bijection.



  (** Abstract properties of f: A->B (wrt. domain DA and codomain DB *)

  Definition fun_codomain := forall a, In DA a ->  In DB (f a).
  Definition fun_onto := forall b, In DB b -> exists a, In DA a /\ f a = b.
  Definition fun_inj := forall a a' , In DA a -> In DA a' -> f a = f a' ->
                 a = a'.

  Definition image := fun b => exists a, In DA a /\ f a = b.


  Inductive  fun_injection : Prop :=
   fun_inj_i :  fun_codomain ->
                            fun_inj -> fun_injection.

  Inductive  fun_bijection : Prop :=
   fun_bij_i :  fun_codomain -> fun_onto ->
                            fun_inj -> fun_bijection.

  Definition rel_inv := fun b a => In DA a /\ In DB b /\ Rf a b.


End f_given.




(** Conversion from a relational definition : A->B->Prop into a partial
    function of type A->B *)

 Section rel_to_fun.

 Variables
           (Rf : A -> B -> Prop).

 Definition r2i := iota_fun   Rf.

End rel_to_fun.
End AB_given.

Section inversion_of_bijection.
  Variables (A B : Type)
           (inhA :  inhabited A)
           (DA : Ensemble A)
           (DB : Ensemble B)
           (f : A -> B).

 Let inv_spec := fun y x => In DA x /\ In DB y /\ f x = y.


 Definition inv_fun := r2i   inhA DB DA inv_spec.

 Hypothesis f_b : fun_bijection DA DB f.


Lemma inv_compose :
  forall x, DA x -> inv_fun (f x) = x.
Proof.
  intros x H;  unfold inv_fun, r2i.
  pattern (f x), (iota_fun inhA DB DA inv_spec (f x)).
  eapply (iota_fun_ind inhA DB DA).
  -  destruct f_b;   now apply H0.
  -  reflexivity.
  - exists x; split.
   +  split.
    *   destruct f_b;   split;auto.
    *  auto.
   +   intros x' H0;   destruct f_b as [f0 f1 f2].
       apply f2;  auto.
      now destruct H0.
      now destruct H0 as [[H0 [_ H2]] H1].
  -   destruct f_b as [f0 f1 f2].
      apply f0;auto.
      - intros b H0;  destruct H0 as [H0 H1];   apply H1; auto.
        split;auto.
        split;auto.
        split;auto; now  apply f_b.
Qed.


Lemma inv_composeR :  forall b, DB b -> f (inv_fun b) = b.
Proof.
 intros b H; unfold inv_fun,r2i.
 pattern  b, (iota_fun inhA DB DA inv_spec b);eapply iota_fun_ind;eauto.
 destruct f_b as [H0 H1 H2].
 - case (H1 b H); intros x (H',H5); exists x;auto.
   repeat split; trivial.
   intros x' [H3 H4]; subst b ;  apply H2; auto.
   now   destruct H3 as [_ [H3 H5]].
 - destruct 1 as [[H0 _] _];  destruct H0; tauto.
Qed.

Lemma inv_fun_bij : fun_bijection DB DA inv_fun.
Proof.
  destruct f_b; split.
  -  intros b Hb;  unfold inv_fun, r2i.
     pattern  b, (iota_fun inhA DB DA inv_spec b);
       eapply iota_fun_ind;eauto.
     + destruct (H0 b Hb) as [x H2].
       exists x;split ;auto.
       unfold inv_spec;  repeat split; auto.
       1,2,3 :  tauto.
       destruct 1.
       apply H1; auto.
       tauto.
       destruct H3 as [H3 H5].
       destruct H2, H5; congruence.
     + destruct 1;  tauto.
  -   intros a Ha; exists (f a);split;auto.
       apply inv_compose;auto.
  - intros b b' Hb Hb' H2.
    rewrite <- (inv_composeR  Hb).
    rewrite <- (inv_composeR  Hb').
    now rewrite H2.
Qed.

End inversion_of_bijection.

Lemma image_as_Im {A B : Type} (U : Ensemble A) (f : A -> B) :
  image U f = Im U f.
Proof.
  apply Extensionality_Ensembles; split; intros y Hy.
  - destruct Hy as [x [Hx Hy]].
    subst. exists x; auto.
  - inversion Hy; subst; clear Hy.
    exists x; auto.
Qed.

(** convert a [fun_bijection] to a [bijection] in the sense of the
   [ZornsLemma] library. *)
Definition fun_restr {U V : Type} (f : U -> V)
  {A : Ensemble U} {B : Ensemble V}
  (Hf : fun_codomain A B f) :
  { x : U | In A x } -> { y : V | In B y } :=
  fun p : { x : U | In A x } =>
    exist (fun y : V => In B y)
      (f (proj1_sig p))
      (Hf (proj1_sig p) (proj2_sig p)).

Lemma fun_bijection_codomain
  {U V : Type} {A : Ensemble U} {B : Ensemble V}
  (g : U -> V) (g_bij : fun_bijection A B g) :
  fun_codomain A B g.
Proof.
  destruct g_bij; assumption.
Defined.

Lemma fun_bijection_is_ZL_bijection
  {U V : Type} {A : Ensemble U} {B : Ensemble V}
  (g : U -> V) (g_bij : fun_bijection A B g) :
  FunctionProperties.bijective
    (fun_restr (fun_bijection_codomain g_bij)).
Proof.
  destruct g_bij as [H0 H1 H2].
  split.
  - intros [x0 Hx0] [x1 Hx1] Hx.
    apply subset_eq_compat.
    inversion Hx; subst; clear Hx.
    apply H2; auto.
  - intros [y Hy].
    simpl.
    specialize (H1 y Hy) as [x [Hx0 Hx1]].
    subst. exists (exist _ x Hx0).
    apply subset_eq_compat.
    reflexivity.
Qed.

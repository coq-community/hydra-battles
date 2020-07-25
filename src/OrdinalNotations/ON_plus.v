
Require Import Arith Compare_dec Lia Simple_LexProd OrdinalNotations.Definitions
        Relation_Operators Disjoint_Union.

Import Relations.
Generalizable All Variables.
Coercion is_true: bool >-> Sortclass.


Section Defs.

  Context `(ltA: relation A)
          (compareA : A -> A -> comparison)
          (NA: ON ltA compareA).
  Context `(ltB: relation B)
          (compareB : B -> B -> comparison)
          (NB: ON ltB compareB).


Definition t := (A + B)%type.
Arguments inl  {A B} _.
Arguments inr  {A B} _.

Definition lt : relation t := le_AsB _ _ ltA ltB.

 Definition compare (alpha beta: t) : comparison :=
   match alpha, beta with
     inl _, inr _ => Lt
   | inl a, inl a' => compareA a a'
   | inr b, inr b' => compareB b b'
   | inr _, inl _ => Gt
  end.

Definition le := clos_refl _ lt.

Hint Unfold lt le : core.
Hint Constructors le_AsB: core.

Instance lt_strorder : StrictOrder lt.
Proof.
  split.
  -  intros x  H. inversion H. subst.
     Search Irreflexive.
     
     destruct (StrictOrder_Irreflexive _ H2).
    subst.
 destruct (StrictOrder_Irreflexive _ H2).
- intros x y z H H0.  inversion H; inversion H0; subst; try discriminate.
  + injection H5;constructor.  subst.
     now transitivity y0.    
    + constructor.
    + constructor.
    + constructor.
      injection H5; intro; subst.  now transitivity y0.
Qed.
    


Lemma lt_wf : well_founded lt.
Proof. destruct NA, NB.
       apply wf_disjoint_sum; [apply wf | apply wf0].
Qed.


Lemma compare_reflect alpha beta :
  match (compare alpha beta)
  with
    Lt => lt alpha  beta
  | Eq => alpha = beta
  | Gt => lt beta  alpha
  end.
  destruct alpha, beta; cbn; auto.
  destruct (compare_correct a a0); (now subst || constructor; auto).
  - destruct (compare_correct b b0); (now subst || constructor; auto).
Qed.


Lemma compare_correct alpha beta :
    CompareSpec (alpha = beta) (lt alpha beta) (lt beta alpha)
              (compare alpha beta).
Proof.
  generalize (compare_reflect alpha beta).
  destruct (compare alpha beta); now constructor. 
Qed.

Global Instance ON_plus : ON lt compare.
Proof.
  split.
  - apply lt_strorder.
  -  apply lt_wf.
  - apply compare_correct.
Qed.


Lemma lt_eq_lt_dec alpha beta :
  {lt alpha  beta} + {alpha = beta} + {lt beta  alpha}.
Proof.
 generalize (compare_reflect alpha beta).
 case_eq (compare alpha beta).
  - intros; left; now right.
  - intros; left; now left.
  - intros; now right.
Defined.


End Defs.

About ON_plus.

Arguments ON_plus {A ltA  compareA} _ {B ltB  compareB} _.

Require Import Omega_ON.

Check ON_plus Omega Omega.

Definition Omega_plus_Omega := ON_plus Omega Omega.

Existing Instance Omega_plus_Omega.

About lt_eq_lt_dec.

Arguments lt_eq_lt_dec {A ltA compareA} _ {B ltB compareB} _.


About compare.


About lt.
Check on_lt (inr 6) (inr 8).

Compute on_compare (inl 8) (inr 4).

Open Scope ON_scope.

Declare Scope oo_scope.
Delimit Scope oo_scope with oo.
Open Scope oo_scope.

Notation "'omega'" := (inr nat 0).

Goal inl 7 < inr 0.
constructor.
Qed.

Definition fin (i:nat) : on_t := inl i.
Coercion fin : nat >-> on_t.


Lemma omega_is_limit : Limit omega. 
Proof.
  split.
  + exists (inl 0); constructor.
  + inversion 1; subst.
    exists (inl (S x)); split; constructor;auto with arith.
    lia.
Qed.

Lemma is_limit_unique alpha : Limit alpha -> alpha = omega.
Proof.
destruct alpha.
- intro H; inversion H.
 destruct n.
 +  destruct H0 as [w Hw].
    inversion Hw.   lia.
    + specialize (H1 (inl n)).
    destruct H1.
    constructor; auto.
    destruct H1.
    inversion H2; subst; inversion H1; subst.
    lia.
 - destruct n.
   + trivial.
   + destruct 1.
    specialize (H0 (inr n)).
    destruct H0.
    constructor; auto.
    destruct H0 as [H0 H1]; inversion H1; inversion H0; subst.
     discriminate.    
      injection H7; intro; subst. lia.
Qed.


Lemma Successor_inv1 : forall i j, Successor  (inl j) (inl i) -> j = S i. 
Proof.
  destruct 1 as [H H0].
  inversion_clear H.
  assert (H2 : (j = S i \/ S i < j)%nat)  by lia.
  destruct H2; trivial.
  elimtype False.
  assert (inl i < inl (S i)) by (constructor; auto).
  assert (inl (S i) < inl j) by (constructor; auto).
  specialize (H0 (inl (S i)) H2 H3).
  destruct H0.
Qed.

Lemma Successor_inv2 : forall i j, Successor (inr j) (inr i) -> j = S i. 
Proof.
  destruct 1 as [H H0].
  inversion_clear H.
  
  assert (H2 : (j = S i \/ S i < j)%nat)  by lia.
  destruct H2; trivial.
   elimtype False.
   Print le_AsB.
   specialize (H0 (inr (S i))).
 assert (inr i < inr (S i)) by (constructor; auto).
  assert (inr (S i) < inr j) by (constructor; auto).
  specialize (H0 H2 H3); inversion H0.
Qed.

Lemma Successor_inv3 : forall i j, ~ Successor (inr j) (inl i).
Proof.
  destruct 1 as [H H0].

  specialize (H0 (inl (S i))).
  assert (inl i < inl (S i)) by (constructor;auto).
  assert (inl (S i) < inr j) by constructor.
  specialize (H0 H1 H2);  inversion H0.
Qed.

Lemma Successor_inv4 : forall i j, ~ Successor (inl j) (inr i).
Proof.
  destruct 1 as [H H0].
  inversion H.
Qed.


   
  Lemma ZLS (alpha : on_t) :{alpha = 0} +
                           {Limit alpha} +
                           {beta : on_t | Successor alpha beta}.
  destruct alpha.
  - destruct n.
    +   left; now left.
    + right; exists (inl n).
      split.
      * constructor. auto with arith.
      *       intros beta Hbeta Hbeta'; inversion Hbeta; subst;
                inversion Hbeta';subst; try lia.
  - destruct n.
    left;right.
    split.
    + exists (inl 0); constructor.
    + inversion 1; subst.
      exists (inl (S x)); split; constructor;auto with arith.
      lia.
    + right; exists (inr n).
      split.
      * constructor. auto with arith.
      *       intros beta Hbeta Hbeta'; inversion Hbeta; subst;
                inversion Hbeta';subst; try lia.
Defined.



Require Import Arith Compare_dec Lia Simple_LexProd OrdinalNotations.Definitions
        Relation_Operators Disjoint_Union.

Import Relations.
Generalizable All Variables.
Coercion is_true: bool >-> Sortclass.


Section Defs.

  Context `(ltA: relation A)
          (compareA : A -> A -> comparison)
          (NA: OrdinalNotation ltA compareA).
  Context `(ltB: relation B)
          (compareB : B -> B -> comparison)
          (NB: OrdinalNotation ltB compareB).


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

Global Instance ON_plus : OrdinalNotation lt compare.
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

Require Import Omega_ordinal.

Check ON_plus Omega Omega.

Definition Omega_plus_Omega := ON_plus Omega Omega.

Existing Instance Omega_plus_Omega.

About lt_eq_lt_dec.

Arguments lt_eq_lt_dec {A ltA compareA} _ {B ltB compareB} _.


About compare.



Compute comp (inl 8) (inr 4).

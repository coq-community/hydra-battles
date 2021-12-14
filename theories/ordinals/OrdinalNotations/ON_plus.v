
(** The sum of two ordinal  notations *)

(** Pierre Castéran, Univ. Bordeaux and LaBRI *)

 
From Coq Require Import Arith Compare_dec Lia 
     Relation_Operators RelationClasses Disjoint_Union.
From hydras Require Import  ON_Generic MoreOrders.

Import Relations.
Generalizable All Variables.

(* begin snippet Defs *)
Section Defs.

  Context `(ltA: relation A)
          (cmpA : Compare A)
          (NA: ON ltA cmpA).
  Context `(ltB: relation B)
          (cmpB : Compare B)
          (NB: ON ltB cmpB).

  Definition t := (A + B)%type.
  Arguments inl  {A B} _.
  Arguments inr  {A B} _.

  Definition lt : relation t := le_AsB _ _ ltA ltB.
(* end snippet Defs *)

(* begin snippet compareDef *)
#[global] Instance compare_t : Compare t :=
fun (alpha beta: t) =>
   match alpha, beta with
     inl _, inr _ => Lt
   | inl a, inl a' => compare a a'
   | inr b, inr b' => compare b b'
   | inr _, inl _ => Gt
  end.
(* end snippet compareDef *)

Definition le := clos_refl _ lt.

Local Hint Unfold lt le : core.
Local Hint Constructors le_AsB: core.

Instance lt_strorder : StrictOrder lt.
Proof.
  split.
  -  intros x  H. inversion H. subst.
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
    

Lemma compare_reflect alpha beta :
  match (compare alpha beta)
  with
    Lt => lt alpha  beta
  | Eq => alpha = beta
  | Gt => lt beta  alpha
  end.
  destruct alpha, beta; cbn; auto.
  destruct (comparable_comp_spec a a0); (now subst || constructor; auto).
   - destruct (comparable_comp_spec b b0); (now subst || constructor; auto).
Qed.

(* begin snippet compareCorrect:: no-out  *)

Lemma compare_correct alpha beta :
    CompSpec eq lt alpha beta (compare alpha beta). (* .no-out *)
(* end snippet compareCorrect *)

Proof.
  generalize (compare_reflect alpha beta).
  destruct (compare alpha beta); now constructor. 
Qed.
 

(* begin snippet plusComp:: no-out *)

#[global] Instance plus_comp : Comparable lt compare_t.
Proof.
  split.
  - apply lt_strorder.
  - apply compare_correct. 
Qed.
(* end snippet plusComp *)


(* begin snippet ltWf *)

(*|
.. coq:: no-out 
|*)


Lemma lt_wf : well_founded lt.
Proof.
  destruct NA, NB.
  apply wf_disjoint_sum; [apply ON_wf | apply ON_wf0].
Qed.

(*||*)

(* end snippet ltWf *)

(* begin snippet OnPlus *)

(*|
.. coq:: no-out 
|*)

#[global] Instance ON_plus : ON lt compare_t.
Proof.
  split.
  - apply plus_comp.
  - apply lt_wf.
Qed.

(*||*)

(* end snippet OnPlus *)


Lemma lt_eq_lt_dec alpha beta :
  {lt alpha  beta} + {alpha = beta} + {lt beta  alpha}.
Proof.
  generalize (compare_reflect  alpha beta).
  destruct (compare alpha beta).  
  - left;right; auto.
  - left;left; auto. 
  - right;  auto.
Defined.


End Defs.

Arguments lt_eq_lt_dec {A ltA cmpA} _ {B ltB  cmpB} _.
Arguments ON_plus {A ltA cmpA} _ {B ltB cmpB}.




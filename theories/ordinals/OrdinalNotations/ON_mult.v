
(** Product of ordinal  notations *)

(** Pierre Castéran, Univ. Bordeaux and LaBRI *)

 
From Coq Require Import Arith Compare_dec Lia 
     Relation_Operators RelationClasses.
From hydras Require Import Simple_LexProd ON_Generic.

Import Relations.
Generalizable All Variables.
Coercion is_true: bool >-> Sortclass.

(** * Definitions *)


(**  The product of two notation systems NA and NB is defined as the 
    lexicographic product of the order on NB by the order on NA 
    (in this order ! ) *)

Section Defs.

  Context `(ltA: relation A)
          (compareA : A -> A -> comparison)
          (NA: ON ltA compareA).
  Context `(ltB : relation B) 
          (compareB : B -> B -> comparison)
          (NB: ON ltB compareB).


Definition t := (B * A)%type.
Definition lt : relation t := lexico ltB ltA.


(** reflexive closure of lt *)

Definition le := clos_refl _ lt.


Definition compare (alpha beta: t) : comparison :=
  match compareB (fst alpha) (fst beta) with
  |  Eq => compareA (snd alpha) (snd beta)
  | c => c
  end.

Local Hint Constructors clos_refl lexico: core.

Local Hint Unfold  lt le : core.


(** * Properties *)

Instance lt_strorder : StrictOrder lt.
Proof.
  apply Strict_lex; [apply NB | apply NA].
Qed.
    

Lemma lt_wf : well_founded lt.
Proof. 
       apply wf_lexico; apply wf. 
Qed.


Lemma compare_reflect alpha beta :
  match (compare alpha beta)
  with
    Lt => lt alpha  beta
  | Eq => alpha = beta
  | Gt => lt beta  alpha
  end.
  destruct alpha, beta; cbn; auto. unfold compare. cbn.
  destruct (compare_correct b b0).
  - subst; destruct (compare_correct a a0).
    + now subst.
    + now constructor 2.
    + now constructor 2.
  - now constructor 1.
  - now constructor 1.
Qed.


Lemma compare_correct alpha beta :
    CompareSpec (alpha = beta) (lt alpha beta) (lt beta alpha)
                (compare alpha beta).
Proof.
  generalize (compare_reflect alpha beta).
  destruct (compare alpha beta); now constructor. 
Qed.

#[global] Instance mult_comp:  Comparable lt compare.
Proof.
  split.
  - apply lt_strorder.
  - apply compare_correct.
Qed. 

Global Instance ON_mult : ON lt compare.
Proof.
  split.
  - apply mult_comp.
  -  apply lt_wf.
Qed.


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

Arguments lt_eq_lt_dec {A ltA compareA} _ {B ltB compareB} _.
Arguments ON_mult {A ltA  compareA} _ {B ltB compareB}.
Arguments lt_strorder {A} {ltA} {compareA} _  {B} {ltB} {compareB} _.






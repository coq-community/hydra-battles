
(** Product of ordinal  notations *)

(** Pierre Castéran, Univ. Bordeaux and LaBRI *)

 
From Coq Require Import Arith Compare_dec Lia 
     Relation_Operators RelationClasses.
From hydras Require Import Comparable Simple_LexProd ON_Generic.

Import Relations.
Generalizable All Variables.

(** * Definitions *)


(**  The product of two notation systems NA and NB is defined as the 
    lexicographic product of the order on NB by the order on NA 
    (in this order ! ) *)


(* begin snippet Defs *)

Section Defs.

  Context `(ltA: relation A)
          (cmpA : Compare A)
          (NA: ON ltA cmpA)
          `(ltB : relation B) 
          (cmpB : Compare B)
          (NB: ON ltB cmpB).

  Definition t := (B * A)%type.
  Definition lt : relation t := Simple_LexProd.lexico ltB ltA.
  Definition le := clos_refl _ lt. 

  #[global] Instance compare_t : Compare t :=
    fun (alpha beta: t) =>
    match compare (fst alpha) (fst beta) with
    | Eq => compare (snd alpha) (snd beta)
    | c => c
    end.
   (*||*)
  (* end snippet Defs *)

  #[local] Hint Constructors clos_refl Simple_LexProd.lexico: core.
  #[local] Hint Unfold  lt le : core.

  (** * Properties *)

  Instance lt_strorder : StrictOrder lt.
  Proof.
    apply Strict_lex; [apply NB | apply NA].
  Qed.
  

  Lemma lt_wf : well_founded lt.
  Proof. apply wf_lexico; apply ON_wf. Qed.

  Lemma compare_reflect alpha beta :
    match (compare alpha beta)
    with
      Lt => lt alpha  beta
    | Eq => alpha = beta
    | Gt => lt beta  alpha
    end.
  Proof.
    destruct alpha, beta; cbn. unfold compare, compare_t; cbn.
    destruct (comparable_comp_spec b b0).
    - subst; destruct (comparable_comp_spec a a0).
      + now subst.
      + now constructor 2.
      + now constructor 2.
    - now constructor 1.
    - now constructor 1.
  Qed.


  Lemma compare_correct alpha beta :
    CompSpec eq lt alpha beta (compare alpha beta).
  Proof.
    generalize (compare_reflect alpha beta);
      destruct (compare alpha beta); now constructor. 
  Qed.

  (* begin snippet multComp:: no-out *)

  #[global] Instance mult_comp:  Comparable lt compare_t.
  (* end snippet multComp *)

  Proof.
    split.
    - apply lt_strorder.
    - apply compare_correct.
  Qed. 

  (* begin snippet ONMult:: no-out *)
  #[global] Instance ON_mult: ON lt compare_t.
  (* end snippet ONMult *)

  Proof.
    split.
    - apply mult_comp.
    - apply lt_wf.
  Qed.


  Lemma lt_eq_lt_dec alpha beta :
    {lt alpha  beta} + {alpha = beta} + {lt beta alpha}.
  Proof.
    generalize (compare_reflect  alpha beta).
    destruct (compare alpha beta).  
    - left;right; auto.
    - left;left; auto. 
    - right;  auto.
  Defined.


  (* begin snippet endDefs *)

End Defs.
(* end snippet endDefs *)


Arguments lt_eq_lt_dec {A ltA cmpA} _ {B ltB cmpB} _.
Arguments ON_mult {A ltA cmpA} _ {B ltB cmpB}.
Arguments lt_strorder {A} {ltA} {cmpA} _  {B} {ltB} {cmpB} _.






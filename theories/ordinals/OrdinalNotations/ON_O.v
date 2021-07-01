(** Ordinal Notation for a segment [O alpha] *)
(** Pierre Castéran, Unviv. Bordeaux and LaBRI *)



From Coq Require Import Arith Relations Lia Logic.Eqdep_dec Ensembles
        Wellfounded.Inverse_Image Wellfounded.Inclusion
        RelationClasses.
From hydras Require Import ON_Generic.


Coercion is_true: bool >-> Sortclass.
Generalizable Variables A Lt comp.

Section OA_given.
  
  Context {A:Type}
          {Lt Le: relation A}
          {compareA : A -> A -> comparison}
          `(OA : ON A Lt  compareA).

(** The type of ordinals less than [a] *)


Definition t (a:A) := {b:A | compareA b a = Datatypes.Lt}.

Definition lt {a:A} : relation (t a) :=
  fun alpha beta => ON_lt (proj1_sig alpha) (proj1_sig beta).

Definition le {a:A} : relation (t a) :=
  clos_refl (t a) lt.

Definition compare {a:A} (alpha beta : t a) :=
  compareA (proj1_sig alpha) (proj1_sig beta).

Lemma compare_correct {a} (alpha beta : t a) :
  CompareSpec (alpha = beta) (lt alpha beta) (lt beta alpha)
              (compare alpha beta).
Proof.
  - destruct alpha, beta; unfold compare; cbn.
    case_eq (compareA x x0); unfold lt; cbn.
    + constructor 1.
      destruct (compare_correct x x0); try discriminate.
       subst; f_equal; apply eq_proofs_unicity_on.
       decide equality.
    + constructor 2.
        destruct (compare_correct x x0); trivial; try discriminate.
    + constructor 3; destruct (compare_correct x x0); trivial; discriminate.
Qed.


Lemma compare_reflect {a:A} (alpha beta : t  a) :
  match (compare alpha beta)
  with
    Datatypes.Lt => lt alpha  beta
  | Eq => alpha = beta
  | Gt => lt beta  alpha
  end.
Proof.
 now destruct (compare_correct alpha beta).
Qed.


Lemma lt_wf (a:A) : well_founded (@lt a).
Proof.
  intro x;  unfold lt; apply Acc_inverse_image.
   destruct x; cbn; apply wf.
Qed.

Global Instance sto a : StrictOrder (@lt a).
Proof.
  destruct OA; split.
   - intro x; red;  unfold lt; destruct x; cbn.
     intro; destruct sto; apply (StrictOrder_Irreflexive x); auto. 
   -   red; intros; unfold lt in *; destruct x,y,z; cbn in *.
       specialize (StrictOrder_Transitive x x0 x1).
       intro; auto.
       apply H1.
       apply H. 
       apply H0.
Qed.

#[global] Instance ON_O_comp (a:A) : Comparable (@lt a)  compare .
Proof. 
  split.
  - apply sto.
  - apply compare_correct.
Qed. 

(** We have now an ordinal notation *)

Global Instance ON_O  (a:A) : ON (@lt a) compare .
Proof.
  split.
  - apply ON_O_comp. 
  - apply lt_wf.
Qed.

End OA_given.

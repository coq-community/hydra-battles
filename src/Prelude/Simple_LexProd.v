(** Non dependent lexicographic product *)

From Coq Require Import Relations Wellfounded.Lexicographic_Product
        Wellfounded.Inverse_Image Wellfounded.Inclusion Setoid.
From Coq Require Export RelationClasses.




Section Definitions.

  Variables (A B : Type)
            (ltA : relation A)
            (ltB : relation B).

  Hypothesis wfA : well_founded ltA.
  Hypothesis wfB : well_founded ltB.

  Inductive lexico : relation (A * B) :=
   lex_1 : forall a a' b b', ltA a a' -> lexico (a,b) (a',b')
|  lex_2 : forall a  b b', ltB b b' -> lexico (a,b) (a,b') .                                          

  Global Instance Trans_lex  {SA : StrictOrder ltA}
         {SB : StrictOrder ltB}  :Transitive lexico. 
  Proof.
    intros (x,y) (z,t) (u,v) H H'.
    inversion H; inversion H'.
    left; now transitivity z.
    left.
    subst u.   assumption.
    now left.
    right; now transitivity t.
  Qed.
  
  Global Instance Strict_lex {SA : StrictOrder ltA}
         {SB : StrictOrder ltB}  : StrictOrder lexico.                 
  Proof.
    split.
    intros (x,y) H.
    inversion_clear H.
    now destruct (StrictOrder_Irreflexive x). 
    now destruct (StrictOrder_Irreflexive y).
    apply Trans_lex.
  Qed.


  

  Let pair2sig (p: A * B) := existT (fun _ : A => B) (fst p) (snd p).

  Lemma wf_lexico : well_founded lexico.
  Proof.
    pose (R  :=
            fun p q : A * B =>
              lexprod A (fun _ : A => B) ltA
                      (fun _ : A => ltB)
                      (pair2sig p)
                      (pair2sig q)).
    apply wf_incl with R.
    - intros p q H; destruct p, q;  red.
      destruct H.
    + now left. 
    + now right.
    - unfold R;apply wf_inverse_image, wf_lexprod.
      + trivial.
      + intro; trivial.
  Defined.

End Definitions.

Arguments lexico {A B} _ _ _ _.
Arguments wf_lexico {A B ltA ltB} _ _ _.


Require Import Eqdep_dec.

#[global] Set Asymmetric Patterns.

Lemma inj_right_pair2 (A: Set):
  (forall x y : A, {x = y} + {x <> y}) ->
  forall (x : A) (P : A -> Set) (y y' : P x),
    existT P x y = existT P x y' -> y = y'.
Proof.
  intros H x P y y' H0.
  set (Proj :=
         fun (e : sigT P) (def : P x) =>
           match e with
           | existT x' dep =>
               match H x' x with
               | left eqdep => eq_rec x' P dep x eqdep
               | _ => def
               end
           end) in *.
  cut (Proj (existT P x y) y = Proj (existT P x y') y).
  - simpl; destruct  (H x x) as [e | n]. 
    + intro e0;
        set
          (B :=
             K_dec_set H
               (fun z : x = x =>
                  eq_rec x P y x z = eq_rec x P y' x z ->
                  eq_rec x P y x (refl_equal x) = 
                    eq_rec x P y' x (refl_equal x))
               (fun z : eq_rec x P y x (refl_equal x) = 
                          eq_rec x P y' x (refl_equal x) =>
                  z) e e0) in *; apply B.
    + now destruct n.
  - now rewrite H0.
Qed.

Set Apply With Renaming.

Require Import Eqdep_dec.

Global Set Asymmetric Patterns.

Lemma inj_right_pair2 :
 forall A : Set,
 (forall x y : A, {x = y} + {x <> y}) ->
 forall (x : A) (P : A -> Set) (y y' : P x),
 existT P x y = existT P x y' -> y = y'.
Proof.
intros.
set
 (Proj :=
  fun (e : sigT P) (def : P x) =>
  match e with
  | existT x' dep =>
      match H x' x with
      | left eqdep => eq_rec x' P dep x eqdep
      | _ => def
      end
  end) in *.
cut (Proj (existT P x y) y = Proj (existT P x y') y).
simpl in |- *.
induction (H x x).
intro e.
set
 (B :=
  K_dec_set H
    (fun z : x = x =>
     eq_rec x P y x z = eq_rec x P y' x z ->
     eq_rec x P y x (refl_equal x) = eq_rec x P y' x (refl_equal x))
    (fun z : eq_rec x P y x (refl_equal x) = eq_rec x P y' x (refl_equal x) =>
     z) a e) in *.
apply B.
elim b.
auto.
rewrite H0.
reflexivity.
Qed.

Require Import Relations.

Class Assoc {A} (R : relation A) (f : A -> A -> A) : Prop :=
  assoc x y z : R (f x (f y z)) (f (f x y) z).

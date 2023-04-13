From Coq Require Import Ensembles. 
Require Import folProp. 

Notation "'SetAddn' E0  x1 .. xn" := 
  (Ensembles.Add _ (.. (Ensembles.Add _ E0 x1) .. ) xn) 
    (at level 0, E0 at level 0, x1 at level 0, xn at level 0).


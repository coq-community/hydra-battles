From Coq Require Import Ensembles. 
From hydras.Ackermann Require Import folProp. 

Notation "'SetAdds' E0  x1 .. xn" := 
  (Ensembles.Add _ (.. (Ensembles.Add _ E0 x1) .. ) xn) 
    (at level 0, E0 at level 0, x1 at level 0, xn at level 0).

Notation "'SetEnum' x0  x1 .. xn" := 
  (Ensembles.Add _ (.. (Ensembles.Add _ (Singleton _ x0) x1) .. ) xn) 
    (at level 0, x0 at level 0, x1 at level 0, xn at level 0).

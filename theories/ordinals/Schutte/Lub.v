(* Pierre Casteran, LaBRI, Univ. Bordeaux *)

Set Implicit Arguments.

From Coq Require Import Relations Ensembles.

(* begin snippet isLubDef *)

Definition upper_bound (M:Type)
                       (D: Ensemble M)
                       (lt: relation M)
                       (X:Ensemble M)
                       (a:M) :=
  forall x, In _ D x ->  In _ X x -> x = a \/ lt  x a.


Definition is_lub (M:Type)
                  (D : Ensemble M)
                  (lt : relation M)
                  (X:Ensemble M)
                  (a:M) :=
   In _ D a  /\ upper_bound  D lt X a  /\
   (forall y, In _ D y ->
              upper_bound  D lt X y  ->
              y = a \/ lt a y).

(* end snippet isLubDef *)



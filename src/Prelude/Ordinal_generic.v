Require Import RelationClasses Relation_Operators.
Import Relation_Definitions.

(* Immediate predecessor *)

Definition ipred {A:Type}{lt : relation A}
           {sto : StrictOrder lt} (x y : A):=
  lt x y /\ (forall z,  lt z y -> clos_refl _ lt z x).

(* omega limit *)

Definition  Omega_limit
            {A:Type}{lt : relation A}
           {sto : StrictOrder lt} (s: nat -> A) (alpha:A)  :=
  (forall i: nat, lt (s i) alpha) /\
  (forall beta, lt beta  alpha -> exists i:nat, lt beta (s i)).


Definition  Omega_limit_s
              {A:Type}{lt : relation A}
              {sto : StrictOrder lt}
              (s: nat -> A) (alpha:A) : Type :=
  ((forall i: nat, lt (s i) alpha) *
  (forall beta, lt beta  alpha ->  {i:nat | lt beta ( s i)}))%type.

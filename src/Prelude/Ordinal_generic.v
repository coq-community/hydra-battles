Require Import RelationClasses Relation_Operators.
Import Relation_Definitions.

(* Immediate predecessor *)

Class OrdinalNotation {A:Type}{lt: relation A}(sto:StrictOrder lt)
      (compare : A -> A -> comparison) :=
  { compare_correct :
      forall alpha beta:A,
        CompareSpec (alpha=beta)(lt alpha beta) (lt beta alpha)
                    (compare alpha beta);
    wf : well_founded lt;}.

 
Definition Ipred {A:Type}{lt : relation A}
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
  (forall beta, lt beta  alpha ->  {i:nat | lt beta (s i)}))%type.

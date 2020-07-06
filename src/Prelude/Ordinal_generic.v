Require Import RelationClasses Relation_Operators.
Import Relation_Definitions.


Class OrdinalNotation {A:Type}{lt: relation A}(sto:StrictOrder lt)
      (compare : A -> A -> comparison) :=
  { compare_correct :
      forall alpha beta:A,
        CompareSpec (alpha=beta) (lt alpha beta) (lt beta alpha)
                    (compare alpha beta);
    wf : well_founded lt}.

 
Definition Ipred {A:Type}{lt : relation A}
           {sto : StrictOrder lt} (x y : A):=
  lt x y /\ (forall z,  lt z y -> clos_refl _ lt z x).



Class  SubNotation {A:Type}
       {ltA: relation A}{stoA:StrictOrder ltA}
       {compareA : A -> A -> comparison}
       (notA : OrdinalNotation stoA compareA)
       {B:Type}{ltB: relation B}{stoB:StrictOrder ltB}
       {compareB : B -> B -> comparison}
       (notB : OrdinalNotation stoB compareB)
       (bound :  B)
       (cast : A -> B):=
  {
  commutation :forall a a' : A,  compareB (cast a) (cast a') =
                                 compareA a a';
  incl : forall a, ltB (cast a) bound;
  surj : forall b, ltB b bound -> exists a:A, cast a = b}.


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

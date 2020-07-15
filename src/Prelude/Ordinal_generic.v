Require Import RelationClasses Relation_Operators Ensembles.
Import Relation_Definitions.

Require Export Limits_and_Successors.

Generalizable All Variables.

(**
  Ordinal notation system on type [A] :

*)

Class OrdinalNotation {A:Type}{lt: relation A}(sto:StrictOrder lt)
      (compare : A -> A -> comparison)  :=
  { compare_correct :

      forall alpha beta:A,
        CompareSpec (alpha=beta) (lt alpha beta) (lt beta alpha)
                    (compare alpha beta);
    wf : well_founded lt;
    ZeroLimitSucc_dec : forall x,  {Least x}+
                                   {Limit x} +
                                   {p: A | Successor x p}
  }. 





(** The segment (called [O alpha] in Schutte) *)

Definition bigO `{nA : @OrdinalNotation A ltA stoA compareA}
           (a: A) : Ensemble A :=
  fun x: A => ltA x a.



           
(** The segment associated with nA is isomorphic to
    the interval [0,b[ *)

Class  SubSegment 
       `(nA : @OrdinalNotation A ltA stoA compareA)
       `(nB : @OrdinalNotation B ltB stoB compareB)
       (b :  B)
       (iota : A -> B):=
  {
  subseg_compare :forall x y : A,  compareB (iota x) (iota y) =
                                 compareA x y;
  subseg_incl : forall x, ltB (iota x) b;
  subseg_onto : forall y, ltB y b  -> exists x:A, iota x = y}.



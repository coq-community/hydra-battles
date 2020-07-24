Require Import RelationClasses Relation_Operators Ensembles .
Import Relation_Definitions.

Require Schutte_basics.

Require Export MoreOrders.

Generalizable All Variables.
Declare Scope ON_scope.
Delimit Scope ON_scope with on.

(**
  Ordinal notation system on type [A] :

*)

Class ON {A:Type}(lt: relation A)
      (compare : A -> A -> comparison)  :=
  {
  sto :> StrictOrder lt;
  wf : well_founded lt;
  compare_correct :
    forall alpha beta:A,
      CompareSpec (alpha=beta) (lt alpha beta) (lt beta alpha)
                  (compare alpha beta);
  }.

(** Selectors *)

Definition on_t  {A:Type}{lt: relation A}
            {compare : A -> A -> comparison}
            {on : ON lt compare} := A.

Definition on_compare {A:Type}{lt: relation A}
            {compare : A -> A -> comparison}
            {on : ON lt compare} := compare.


Definition on_lt {A:Type}{lt: relation A}
           {compare : A -> A -> comparison}
           {on : ON lt compare} := lt.
Infix "<" := on_lt : ON_scope.

Definition on_le  {A:Type}{lt: relation A}
           {compare : A -> A -> comparison}
           {on : ON lt compare} :=
  clos_refl _ on_lt.

Infix "<=" := on_le : ON_scope.


Definition ZeroLimitSucc_dec {A:Type}{lt: relation A}
           {compare : A -> A -> comparison}
           {on : ON lt compare} :=
  forall alpha,
    {Least alpha}+
    {Limit alpha} +
    {beta: A | Successor alpha beta}.

 
(** The segment called [O alpha] in Schutte *)

Definition bigO `{nA : @ON A ltA compareA}
           (a: A) : Ensemble A :=
  fun x: A => ltA x a.


(** The segment associated with nA is isomorphic to
    the interval [0,b[ *)

Class  SubON 
       `(OA : @ON A ltA  compareA)
       `(OB : @ON B ltB  compareB)
       (alpha :  B)
       (iota : A -> B):=
  {
  subseg_compare :forall x y : A,  compareB (iota x) (iota y) =
                                 compareA x y;
  subseg_incl : forall x, ltB (iota x) alpha;
  subseg_onto : forall y, ltB y alpha  -> exists x:A, iota x = y}.


Class  ON_Isomorphic 
       `(OA : @ON A ltA compareA)
       `(OB : @ON B ltB  compareB)
       (f : A -> B)
       (g : B -> A):=
  {
  iso_compare_comm :forall x y : A,  compareB (f x) (f y) =
                                 compareA x y;
  iso_inv1 : forall a, g (f a)= a;
  iso_inv2 : forall b, f (g b) = b}.


(** OA is an ordinal notation for alpha *)

Class ON_for `(alpha : Schutte_basics.Ord)
     `(OA : @ON A ltA  compareA)
      (iota : A -> Schutte_basics.Ord) :=
  { conform_inj : forall a, Schutte_basics.lt (iota a) alpha;
    conform_surj : forall beta, Schutte_basics.lt beta alpha ->
                                exists b, iota b = beta;
    conform_compare : forall a b:A,
        match compareA a b with
          Datatypes.Lt => Schutte_basics.lt (iota a) (iota b)
        | Datatypes.Eq => iota a = iota b
        | Datatypes.Gt => Schutte_basics.lt (iota b) (iota a)
        end}.

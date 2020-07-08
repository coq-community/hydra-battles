Require Import RelationClasses Relation_Operators.
Import Relation_Definitions.
Generalizable All Variables.


(**
  Ordinal notation system on type [A] :

*)

Class OrdinalNotation {A:Type}{lt: relation A}(sto:StrictOrder lt)
      (compare : A -> A -> comparison) :=
  { compare_correct :
      forall alpha beta:A,
        CompareSpec (alpha=beta) (lt alpha beta) (lt beta alpha)
                    (compare alpha beta);
    wf : well_founded lt}.


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

(**
  [x] is an immediate predecessor of [y]
*)

Definition Ipred {A:Type}{lt : relation A}
           {sto : StrictOrder lt} (x y : A):=
  lt x y /\ (forall z,  lt z y -> clos_refl _ lt z x).


Definition Successor {A:Type}{lt : relation A}
           {sto : StrictOrder lt} (y x : A):= Ipred x y.
(* omega limit *)

Definition  Omega_limit
            {A:Type}{lt : relation A}
           {sto : StrictOrder lt} (s: nat -> A) (alpha:A)  :=
  (forall i: nat, lt (s i) alpha) /\
  (forall beta, lt beta  alpha -> exists i:nat, lt beta (s i)).

(* the same, with a [sig]-type *)

Definition  Omega_limit_s
              {A:Type}{lt : relation A}
              {sto : StrictOrder lt}
              (s: nat -> A) (alpha:A) : Type :=
  ((forall i: nat, lt (s i) alpha) *
  (forall beta, lt beta  alpha ->  {i:nat | lt beta (s i)}))%type.


Lemma Limit_not_Succ  {A:Type}{lt : relation A}
      {sto : StrictOrder lt} (s: nat -> A) (alpha:A) :
  Omega_limit s alpha ->
  forall beta,  ~ Successor alpha beta.
Proof.
  intros [Hlim Hlim0] beta [Hsucc Hsucc0].
  destruct (Hlim0 _ Hsucc) as [i Hi].
  absurd  (lt (s i) (s i)).
   +  apply sto.
   + destruct (Hsucc0 _ (Hlim i)).
     * now transitivity y.
     * assumption. 
Qed.


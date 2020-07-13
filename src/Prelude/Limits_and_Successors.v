Require Import RelationClasses Relation_Operators Ensembles.
Import Relation_Definitions.
Generalizable All Variables.



(**
  [x] is an immediate predecessor of [y]
*)

Definition Ipred {A:Type}{lt : relation A}
           {sto : StrictOrder lt} (x y : A):=
  lt x y /\ (forall z,  lt x z -> lt z y -> False).


Definition Successor {A:Type}{lt : relation A}
           {sto : StrictOrder lt} (y x : A):= Ipred x y.

(* omega limit *)

Definition  Omega_limit
            {A:Type}{lt : relation A}
           {sto : StrictOrder lt} (s: nat -> A) (x:A)  :=
  (forall i: nat, lt (s i) x) /\
  (forall y, lt y  x -> exists i:nat, lt y (s i)).


Definition Limit   {A:Type}{lt : relation A}
           {sto : StrictOrder lt}  (x:A)  :=
  exists s : nat -> A, Omega_limit s x.

(* the same, with a [sig]-type *)

Definition  Omega_limit_s
              {A:Type}{lt : relation A}
              {sto : StrictOrder lt}
              (s: nat -> A) (x:A) : Type :=
  ((forall i: nat, lt (s i) x) *
  (forall y, lt y  x ->  {i:nat | lt y (s i)}))%type.


Lemma Limit_not_Succ  {A:Type}{lt : relation A}
      {sto : StrictOrder lt} (s: nat -> A) (x:A) :
  Omega_limit s x ->
  forall y,  ~ Successor x y.
Proof.
  intros [Hlim Hlim0] y [Hsucc Hsucc0].
  destruct (Hlim0 _ Hsucc) as [i Hi].
  absurd  (lt (s i) (s i)).
   +  apply sto.
   + destruct (Hsucc0 _ Hi (Hlim i)).
Qed.


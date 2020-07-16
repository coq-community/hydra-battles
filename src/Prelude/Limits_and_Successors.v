Require Import RelationClasses Relation_Operators Ensembles.
Import Relation_Definitions.
Generalizable All Variables.



(**
  [x] is an immediate predecessor of [y]
*)
Definition Least `{lt : relation A}
           {sto : StrictOrder lt} (x : A):=
  forall y,  clos_refl A lt x y.


Definition Successor `{lt : relation A}
           {sto : StrictOrder lt} (y x : A):=
  lt x y /\ (forall z,  lt x z -> lt z y -> False).

(* omega limit *)



Definition Limit   `{lt : relation A}
           {sto : StrictOrder lt}  (x:A)  :=
  (exists w:A,  lt w x) /\
  (forall y:A, lt y x -> exists z:A, lt y z /\ lt z x).

Definition  Omega_limit
            `{lt : relation A}
           {sto : StrictOrder lt} (s: nat -> A) (x:A)  :=
  (forall i: nat, lt (s i) x) /\
  (forall y, lt y  x -> exists i:nat, lt y (s i)).

(* the same, with a [sig]-type *)

Definition  Omega_limit_s
             `{lt : relation A}
              {sto : StrictOrder lt}
              (s: nat -> A) (x:A) : Type :=
  ((forall i: nat, lt (s i) x) *
  (forall y, lt y  x ->  {i:nat | lt y (s i)}))%type.


Lemma Omega_limit_not_Succ  `{lt : relation A}
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

Lemma Omega_limit_Limit `{lt : relation A}
      {sto : StrictOrder lt} (s: nat -> A) (x:A) :
  Omega_limit s x -> Limit x.
Proof.
  destruct 1 as [H H0]; split.
  - exists (s 0); auto.
  - intros y Hlt; destruct (H0 _ Hlt) as [z Hz].
    exists (s z); split; auto.
Qed.



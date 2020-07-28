Require Import RelationClasses Relation_Operators Ensembles.
Import Relation_Definitions.
Set Implicit Arguments.

Section A_given.
  Variables (A : Type)
            (lt: relation A).
  
Local Infix "<" := lt.
Local Infix "<=" := (clos_refl _ lt).

(** x is the least element of A (w.r.t. [lt] *)

Definition Least {sto : StrictOrder lt} (x : A):=
  forall y,  x <= y.


Definition Successor {sto : StrictOrder lt} (y x : A):=
  x < y /\ (forall z,  x < z ->  z <  y -> False).

Definition Limit {sto : StrictOrder lt}  (x:A)  :=
  (exists w:A,  w < x) /\
  (forall y:A, y < x -> exists z:A, y < z /\ z < x).

Definition  Omega_limit
            {sto : StrictOrder lt} (s: nat -> A) (x:A)  :=
  (forall i: nat, s i < x) /\
  (forall y, y  < x -> exists i:nat, y < s i).

(* the same, with a [sig]-type *)

Definition  Omega_limit_s
             `{lt : relation A}
              {sto : StrictOrder lt}
              (s: nat -> A) (x:A) : Type :=
  ((forall i: nat, s i < x) *
  (forall y, y  < x ->  {i:nat | y  < s i}))%type.


Lemma Omega_limit_not_Succ  
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

Lemma Least_not_Succ  {sto : StrictOrder lt} (x:A) :
  Least x -> forall z, ~ Successor x z.
Proof.
  intros H z [H0 H1]; specialize (H z).
  inversion H; subst. 
  -  eapply H1; eauto.
     now transitivity z.   
  -  destruct sto; eauto.           
Qed.


Lemma Omega_limit_Limit 
      {sto : StrictOrder lt} (s: nat -> A) (x:A) :
  Omega_limit s x -> Limit x.
Proof.
  destruct 1 as [H H0]; split.
  - exists (s 0); auto.
  - intros y Hlt; destruct (H0 _ Hlt) as [z Hz].
    exists (s z); split; auto.
Qed.


Lemma strorder_irr {sto : StrictOrder lt} (x:A) : ~ lt x x.
Proof.
 destruct sto.
 intro H; destruct (StrictOrder_Irreflexive x H).
 Qed.

End A_given.




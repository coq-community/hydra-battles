(** extEqualNat:

     Original script by Russel O'Connor 
*)
     


Require Import Arith.

(* begin snippet naryFunc *)

Fixpoint naryFunc (n : nat) : Set :=
  match n with
  | O => nat
  | S n => nat -> naryFunc n
  end.

(* end snippet naryFunc *)

Fixpoint naryRel (n : nat) : Set :=
  match n with
  | O => bool
  | S n => nat -> naryRel n
  end.

(* begin snippet extEqualDef *)

Fixpoint  extEqual (n : nat) : forall  (a b : naryFunc n), Prop :=
  match n with
    0 => fun a b => a = b
  | S p => fun a b => forall c, extEqual p (a c) (b c)
  end.

(* end snippet extEqualDef *)


Fixpoint charFunction (n : nat) : naryRel n -> naryFunc n :=
  match n return (naryRel n -> naryFunc n) with
  | O => fun R : bool => match R with
                         | true => 1
                         | false => 0
                         end
  | S m => fun (R : naryRel (S m)) (a : nat) => charFunction m (R a)
  end.


Lemma extEqualRefl n a: extEqual n a a.
Proof.
  revert a; induction n as [| n Hrecn].
  - reflexivity.
  - intros a c; apply Hrecn.
Qed.

Lemma extEqualSym :
  forall (n : nat) (a b : naryFunc n), extEqual n a b -> extEqual n b a.
Proof.
  induction n as [| n Hrecn].
  - simpl in |- *; symmetry  in |- *; apply H.
  - simpl in |- *; intros; apply Hrecn; auto.
Qed.

Lemma extEqualTrans :
 forall (n : nat) (a b c : naryFunc n),
 extEqual n a b -> extEqual n b c -> extEqual n a c.
Proof.
induction n as [| n Hrecn].
- simpl in |- *; intros a b c H H0; transitivity b; auto.
- simpl in |- *; intros; eapply Hrecn.
  + simpl in H; apply (H c0).
  + apply (H0 c0).
Qed.


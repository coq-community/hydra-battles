Require Import Relations.

Class Assoc {A} (R : relation A) (f : A -> A -> A) : Prop :=
  assoc x y z : R (f x (f y z)) (f (f x y) z).


(** Decision typeclasses following Spitters and van der Weegen *)

Class Decision (P : Prop) := decide : {P} + {~P}.

#[export] Hint Mode Decision ! : typeclass_instances.
Arguments decide _ {_} : simpl never, assert.

Class RelDecision {A B} (R : A -> B -> Prop) :=
  decide_rel x y :> Decision (R x y).

#[export] Hint Mode RelDecision ! ! ! : typeclass_instances.
Arguments decide_rel {_ _} _ {_} _ _ : simpl never, assert.

Notation EqDecision A := (RelDecision (@eq A)).

Definition bool_decide (P : Prop) {dec : Decision P} : bool :=
  if dec then true else false.

Lemma bool_decide_eq_true (P : Prop) `{Decision P} : bool_decide P = true <-> P.
Proof.
  unfold bool_decide.
  destruct H; intuition discriminate.
Qed.

Lemma bool_decide_eq_false (P : Prop) `{Decision P} : bool_decide P = false <-> ~P.
Proof.
  unfold bool_decide.
  destruct H; intuition discriminate.
Qed.

(** Compatibility between primRec.iterate and Iterates.iterate *)

From hydras Require primRec Iterates.
From hydras.Ackermann Require Import extEqualNat.

(*

primRec.iterate = 
fun g : nat -> nat =>
nat_rec (fun _ : nat => nat -> nat) (fun x : nat => x)
  (fun (_ : nat) (rec : nat -> nat) (x : nat) => g (rec x))
     : (nat -> nat) -> forall n : nat, (fun _ : nat => nat -> nat) n

Iterates.iterate = 
fix iterate (A : Type) (f : A -> A) (n : nat) (x : A) {struct n} : A :=
  match n with
  | 0 => x
  | S p => f (iterate A f p x)
  end
     : forall A : Type, (A -> A) -> nat -> A -> A
 *)

Lemma iterate_compat (f: nat -> nat) n x :
  Iterates.iterate f n x = primRec.iterate f n x.
Proof.
  induction n; [reflexivity | cbn;  auto].
Qed.

Lemma iterate_extEqual (f: nat -> nat) n :
  extEqual 1 (Iterates.iterate f n) (primRec.iterate f n).
Proof.
  intro x; now rewrite iterate_compat.
Qed.


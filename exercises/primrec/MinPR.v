(** Prove that Stdlib's function [min] is primitive recursive *)
(** keywords: dependent-types primitive-recursive-functions *)


From hydras Require Import  primRec extEqualNat.
From Coq Require Import Min.

(** Define an n-ary if-then-else *)

Parameter naryIf :
  forall (n: nat), naryRel n -> naryFunc n -> naryFunc n -> naryFunc n.

(** Prove a few useful lemmas about [naryIf] *)

Section Proof_of_MinIsPR.

Let minPR : naryFunc 2 :=
  naryIf 2 leBool (fun x _ => x) (fun _ y => y).

(** Note : If you failed to define a useful [naryIf], 
   you may use arithmetic operations instead.

<<
Let minPR (a b: nat) : nat :=
  (charFunction 2 leBool a b) * a +
  (charFunction 2 ltBool b a) * b.
>>
*)

Lemma minPR_correct : extEqual 2 minPR min.
Admitted.


Lemma minPR_PR : isPR 2 minPR.
Admitted.

Lemma minIsPR : isPR 2 min.
Proof.
  destruct minPR_PR as [f Hf].
  exists f; eapply extEqualTrans with (1:= Hf). 
  apply minPR_correct.
Qed.


End Proof_of_MinIsPR.



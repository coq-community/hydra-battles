(** Prove that Stdlib's function [min] is primitive recursive *)
(** keywords: dependent-types primitive-recursive-functions *)


From hydras Require Import  primRec extEqualNat.
From Coq Require Import Min.


Section Proof_of_MinIsPR.

Let minPR (a b: nat) : nat :=
  (charFunction 2 leBool a b) * a +
  (charFunction 2 ltBool b a) * b.


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




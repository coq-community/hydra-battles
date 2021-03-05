(** Prove that Stdlib's function [min] is primitive recursive *)


From hydras Require Import  primRec extEqualNat.
From Coq Require Import Min Compare_dec Lia ArithRing.


Section Proof_of_MinIsPR.

  Let minPR (a b: nat) : nat :=
    (charFunction 2 leBool a b) * a +
    (charFunction 2 ltBool b a) * b.



  Lemma minPR_correct : extEqual 2 minPR min.
  Proof.
    intros x y. cbn. unfold leBool, ltBool.
    destruct (le_lt_dec x y).
    cbn.  
    rewrite (PeanoNat.Nat.min_l _ _ l); ring.
    destruct (min_spec y x).
    destruct H; ring_simplify.
    rewrite PeanoNat.Nat.min_comm. auto.
    destruct H; lia.
  Qed.



  Lemma minPR_PR : isPR 2 minPR.
    unfold minPR.
    apply   compose2_2IsPR.
    apply compose2_2IsPR.
    apply leIsPR.
    apply filter10IsPR.
    apply idIsPR.
    apply multIsPR.
    apply   compose2_2IsPR.
    apply compose2_2IsPR.
    apply filter01IsPR.
    apply idIsPR.
    apply filter10IsPR.
    apply idIsPR.
    apply ltIsPR.
    apply filter01IsPR.
    apply idIsPR.
    apply multIsPR.
    apply plusIsPR.
  Qed.

  Lemma minIsPR : isPR 2 min.
  Proof.
    destruct minPR_PR as [f Hf].
    exists f; eapply extEqualTrans with (1:= Hf). 
    apply minPR_correct.
  Qed.


End Proof_of_MinIsPR.




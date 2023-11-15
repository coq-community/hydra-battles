(** Prove that Stdlib's function [min] is primitive recursive *)

From hydras Require Import  primRec extEqualNat.
From Coq Require Import Compare_dec Lia ArithRing.
Import PeanoNat.Nat.

Section Proof_of_MinIsPR.

(* begin snippet minAltDef *)
  Let min_alt (a b: nat) : nat :=
    (charFunction 2 leBool a b) * a +
    (charFunction 2 ltBool b a) * b.
(* end snippet minAltDef *)

(* begin snippet minProof1:: no-out *)
  Lemma min_alt_correct : extEqual 2 min_alt Nat.min.
  Proof.
  (* ... *)
(* end snippet minProof1 *)
    intros x y. cbn. unfold leBool, ltBool.
    destruct (le_lt_dec x y).
    cbn.  
    rewrite (PeanoNat.Nat.min_l _ _ l); ring.
    destruct (min_spec y x).
    destruct H; ring_simplify.
    rewrite PeanoNat.Nat.min_comm. auto.
    destruct H; lia.
  Qed.

(* begin snippet minProof2:: no-out *)
  #[local] Instance minPR_PR : isPR 2 min_alt.
  Proof.
  (* ... *)
(* end snippet minProof2 *)
    unfold min_alt.
    apply compose2_2IsPR.
    apply compose2_2IsPR.
    apply leIsPR.
    apply filter10IsPR.
    apply idIsPR.
    apply multIsPR.
    apply compose2_2IsPR.
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

(* begin snippet minProof3:: no-out *)
  #[export] Instance minIsPR : isPR 2 Nat.min.
  Proof.
    destruct minPR_PR as [f Hf].
    exists f; eapply extEqualTrans with (1:= Hf). 
    apply min_alt_correct.
  Qed.
(* end snippet minProof3 *)

End Proof_of_MinIsPR.




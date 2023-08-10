(** prLogic.v

    Original script by Russel O'Connor

     Although this module doesn't depend on FOL, the following lemmas 
     are JUST  helpers to prove that the encoding of basic FOL connectives are PR *)


Require Import primRec code cPair.
From Coq Require Import Arith.

Lemma codeForallIsPR : isPR 2 (fun a b : nat => cPair 3 (cPair a b)).
Proof.
  apply compose2_2IsPR with (f := fun a b : nat => 3).
  - apply filter10IsPR with (g := fun _ : nat => 3).
    apply const1_NIsPR.
  - apply cPairIsPR.
  - apply cPairIsPR.
Qed.

Lemma codeNotIsPR : isPR 1 codeNot.
Proof.
  unfold codeNot; apply compose1_2IsPR with
    (f := fun a : nat => 2) (f' := fun a : nat => a).
  - apply const1_NIsPR.
  - apply idIsPR.
  - apply cPairIsPR.
Qed.

Lemma codeImpIsPR : isPR 2 codeImp.
Proof.
  unfold codeImp; apply compose2_2IsPR with (f := fun a b : nat => 1).
  - apply filter10IsPR with (g := fun _ : nat => 1).
    apply const1_NIsPR.
  - apply cPairIsPR.
  - apply cPairIsPR.
Qed.

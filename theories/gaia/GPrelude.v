From mathcomp Require Import all_ssreflect zify.
From hydras Require Import Canon Paths.
Require Import T1Bridge GCanon.

Lemma diffP {T:eqType}(i j:T): i <> j <-> i != j.
Proof.
  split => H.
  - case E: (eq_op i j) => //.
    have H1: i = j by apply /eqP => //.
    by move: (H H1). 
    move => E; subst; move: H; by rewrite eq_refl.  
Qed.


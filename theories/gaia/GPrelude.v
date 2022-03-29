From mathcomp Require Import all_ssreflect zify.
From hydras Require Import Canon Paths.
Require Import T1Bridge GCanon.

Lemma diffP {T:eqType}(i j:T): i <> j <-> i != j.
Proof.
  split => H.
  - case_eq (eq_op i j) => H0.
    have H1: i = j by apply /eqP. 
    contradiction. 
    by []. 
  move => H0; have H1: i == j by apply /eqP .
  subst;  clear H1; move: H; rewrite eq_refl => //. 
Qed.


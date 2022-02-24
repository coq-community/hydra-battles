(** Gaia-compatible large sequences 

(imported from [hydras.Epsilon0.Large_Sets] )
*)

From hydras Require Import T1.
From mathcomp Require Import all_ssreflect zify.
From hydras Require Import Canon Paths Large_Sets.
Require Import T1Bridge GCanon GPaths.

From gaia Require Import ssete9.
Import CantorOrdinal. 

Set Bullet Behavior "Strict Subproofs".

Notation hmlarge  := mlarge.
Notation hmlargeS  := mlargeS.
Definition mlarge alpha s := hmlarge (g2h alpha) s.
Definition mlargeS alpha s := hmlargeS (g2h alpha) s.


Notation hlarge := large. 
Notation hlargeS := largeS. 
Definition large alpha A := hlarge (g2h alpha) A.
Definition largeS alpha A := hlargeS (g2h alpha) A.

Notation hL_spec := L_spec.
Definition L_spec alpha f := L_spec (g2h alpha) f.

Lemma mlarge_unicity alpha k l l' : 
  mlarge alpha (index_iota k.+1 l.+1) ->
  mlarge alpha (index_iota k.+1 l'.+1) ->
  l = l'.
Proof.
  rewrite /mlarge -!interval_def => Hl Hl';
  by rewrite (mlarge_unicity _ _ _ _ Hl Hl').
Qed.

Lemma L_fin_ok i : L_spec (\F i) (L_fin i).
Proof.
  rewrite /L_spec (Finite_ref i) g2h_h2gK; apply L_fin_ok.
Qed.

Theorem Theorem_4_5 (alpha: T1)(Halpha : T1nf alpha)
        (A B : seq nat)
        (HA : Sorted.Sorted Peano.lt A)
        (HB : Sorted.Sorted Peano.lt B)
        (HAB : List.incl A B) :
  largeS alpha A -> largeS alpha B.
Proof.
  rewrite /largeS; apply Theorem_4_5 => //; by rewrite hnf_g2h.
Qed.




(* begin snippet T1BridgeUse:: no-out *)

From hydras Require Import T1. 
From mathcomp Require Import all_ssreflect zify.
Require Import T1Bridge . 
From gaia Require Import ssete9.
Import Epsilon0.T1.
(* end snippet T1BridgeUse *)

(* begin snippet LocateT1 *)

(* end snippet LocateT1 *)

(* begin snippet T1BridgeUseb:: no-out *)

Lemma hmultA : associative mult.
Proof. 
  move => a b c.
   by rewrite -(g2h_h2gK a) -(g2h_h2gK b) -(g2h_h2gK c) -!g2h_mult_rw mulA. 
Qed.

Example Ex1 (a: T1): omega * (a * omega) = omega * a * omega.
Proof. by rewrite hmultA. Qed.
(* end snippet T1BridgeUseb *)

(* begin snippet distributivity:: no-out *)
Lemma hmult_dist : right_distributive mult plus.
Proof.
  move => a b c; specialize (mul_distr (h2g a) (h2g b) (h2g c)) => H.
  rewrite -(g2h_h2gK a) -(g2h_h2gK b) -(g2h_h2gK c).
  rewrite -!g2h_plus_rw  -!g2h_mult_rw H.
  f_equal; by rewrite -g2h_plus_rw. 
Qed. 
(* end snippet distributivity:: no-out *)

Close Scope t1_scope.







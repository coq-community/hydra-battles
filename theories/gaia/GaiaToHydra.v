(* begin snippet T1BridgeUse:: no-out *)

From mathcomp Require Import all_ssreflect zify.
Require Import T1Bridge . 
From hydras Require Import T1. 

From gaia Require Import ssete9.
Import Epsilon0.T1.
(* end snippet T1BridgeUse *)

(* begin snippet LocateT1 *)
Locate T1.
(* end snippet LocateT1 *)

(* begin snippet T1BridgeUseb:: no-out *)

Lemma hmultA : associative T1mul.
Proof. 
  move => a b c.
  by rewrite -(g2h_h2gK a) -(g2h_h2gK b) -(g2h_h2gK c)
                                            -!g2h_multE mulA. 
Qed.

Example Ex1 (a: T1): T1omega * (a * T1omega) = T1omega * a * T1omega.
Proof. by rewrite hmultA. Qed.
(* end snippet T1BridgeUseb *)

(* begin snippet distributivity:: no-out *)
Lemma hmult_dist : right_distributive T1mul T1add.
Proof.
  move => a b c; move :(mul_distr (h2g a) (h2g b) (h2g c)) => H.
  rewrite -(g2h_h2gK a) -(g2h_h2gK b) -(g2h_h2gK c).
  by rewrite -!g2h_plusE  -!g2h_multE H -g2h_plusE. 
Qed. 
(* end snippet distributivity:: no-out *)

Close Scope t1_scope.







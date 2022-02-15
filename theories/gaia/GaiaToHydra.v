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


Example Ex1 (a: T1):  omega * (a * omega) = omega * a * omega.
Proof. by rewrite hmultA. Qed.

Close Scope t1_scope.
(* end snippet T1BridgeUseb *)






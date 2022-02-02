(* begin snippet T1BridgeUse:: no-out *)

From hydras Require Import T1. 
From mathcomp Require Import all_ssreflect zify.
Require Import T1Bridge . 
From gaia Require Import ssete9.
Import Epsilon0.T1.
(* end snippet T1BridgeUse *)

(* begin snippet LocateT1 *)
Locate T1.
(* end snippet LocateT1 *)

(* begin snippet T1BridgeUseb:: no-out *)
Example Ex1 (a: T1):  (omega * (a * omega) = omega * a * omega)%t1.
Proof. by rewrite hmultA. Qed.
(* end snippet T1BridgeUseb *)






(* begin snippet T1BridgeUse:: no-out *)
Require Import T1Bridge.

From hydras Require Import T1. 

Lemma L1 (a: T1):  omega * (a * omega) = omega * a * omega.
Proof.
   now rewrite multA.
Qed.
(* end snippet T1BridgeUse *)

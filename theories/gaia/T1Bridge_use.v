(* begin snippet T1BridgeUse:: no-out *)

From hydras Require Import T1.
From mathcomp Require Import all_ssreflect zify.
Require Import T1Bridge.
Import ssete9.CantorOrdinal. 

From gaia Require Import ssete9.
Import ssete9.CantorOrdinal. 
Set Bullet Behavior "Strict Subproofs".



Lemma L1 (a: hT1):  (homega * (a * homega) = homega * a * homega)%t1.
Proof. by rewrite hmultA. Qed.
(* end snippet T1BridgeUse *)





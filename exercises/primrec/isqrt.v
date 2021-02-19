(* @todo  add as an exercise *)

(** Returns smallest value of x less or equal than b such that (P b x). 
    Otherwise returns b  *)


From hydras Require Import  primRec extEqualNat.
From Coq Require Import Min ArithRing Lia Compare_dec Arith Lia.



(** Please consider the following specification of the integer square root *)

Definition isqrt_spec n r := r * r <= n < S r * S r.

(** Prove the following function [isqrt] is a primitive recursive 
    implementation of this specification *)

Section sqrtIsPR.
  
Let P (n r: nat) :=  Nat.ltb n (S r * S r).
Definition isqrt  := boundedSearch P . 

Lemma sqrt_correct (n: nat) : isqrt_spec n (isqrt n).
Admitted.

Lemma issqrtIsPR : isPR 1 isqrt.
Admitted.

End sqrtIsPR.


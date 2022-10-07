From Coq Require Import Arith Lists.List.
Require Import fol Languages.
Require Import primRec.

(* begin snippet arityTest *)
Compute arity LNT (inr Plus). 
Compute arity LNN (inr Succ). 
Compute arity LNN (inl LT). 
Fail Compute arity LNT (inl LT).
(* end snippet arityTest *)

Check var _ 1: Term LNT.
Check  apply LNT Zero (Tnil _) : Term LNT. 
About Tcons. 

(* begin snippet v1Plus0 *)
(** v1 + 0 *)
Check apply LNN Plus 
  (Tcons LNN 1 (var _ 1) 
     (Tcons _ 0 (apply LNN Zero (Tnil _))
        (Tnil _))).
(* end snippet v1Plus0 *)

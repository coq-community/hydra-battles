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

(* begin snippet v1Plus0 *)
(** v1 + 0 *)
Example t1_0: Term LNN :=
 apply LNN Plus 
   (Tcons LNN _ (var LNN  1)
     (Tcons LNN _ (apply LNN Zero (Tnil _)) (Tnil _))). 
(* end snippet v1Plus0 *)

(* begin snippet instantiations *)

Module InLNN.

Notation Tcons := (Tcons LNN _). 
Notation Tnil := (Tnil LNN). 
Notation var := (var LNN).
Notation apply := (apply LNN). 
Notation forallNN := (forallH LNN).
Notation atomicNN := (atomic LNN). 
Notation impNN := (impH LNN).
Notation notNN := (notH LNN).
Notation equal t1 t2 := (equal LNN t1 t2).

Notation orNN := (orH LNN).
Notation andNN := (andH LNN).
Notation iffNN := (iffH LNN).
Notation existNN := (existH LNN).


Notation plusNN t1 t2:= (apply Plus (Tcons t1 (Tcons t2 Tnil))).
Notation ltNN t1 t2 := (atomicNN LT (Tcons t1 (Tcons t2 Tnil))). 
Notation zeroNN := (apply Zero Tnil).
Notation succNN t := (apply Succ (Tcons t Tnil)).
Fixpoint termOfNat n :=
  match n with 
    0 => zeroNN
  | S p => succNN (termOfNat p)
  end.
(* end snippet instantiations *)

(* begin snippet v1Plus01 *)
Example t1: Term LNN := (plusNN (var 1) zeroNN). 
(* end snippet v1Plus01 *)


(** forall v0 v1, v0 < v1 -> v0 < v1 + v0 *)
(* begin snippet f1Example *)
Example f1 : Formula LNN :=
  forallNN 0 
    (forallNN 1 
       (impNN 
          (ltNN (var 0) (var  1))
          (ltNN (var 0) (plusNN (var 1) (var 0))))).  
(* end snippet f1Example *)

(* begin snippet f2Example *)
Example f2 : Formula LNN :=
  forallNN 0 (existNN 1 (ltNN (var 0) (var 1))).
(* end snippet f2Example *)

(** depth-order vs structural order *)
(* begin snippet ltDepth1:: no-out *)
Goal lt_depth _ 
  (existNN 1 (ltNN (plusNN (termOfNat 42) (var 3)) (var 1))) f2.
Proof. red; cbn; auto with arith. Qed. 
(* end snippet ltDepth1 *)
End InLNN.






From Coq Require Import Arith Lists.List.
Require Import fol folProp Languages.
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
Notation forallH := (forallH LNN).
Notation atomic := (atomic LNN). 
Notation inpH := (impH LNN).
Notation notH := (notH LNN).
Notation equal t1 t2 := (equal LNN t1 t2).

Notation orH := (orH LNN).
Notation andH := (andH LNN).
Notation iffH := (iffH LNN).
Notation existH := (existH LNN).


Notation plusH t1 t2:= (apply Plus (Tcons t1 (Tcons t2 Tnil))).
Notation timesH t1 t2:= (apply Times (Tcons t1 (Tcons t2 Tnil))).
Notation ltH t1 t2 := (atomic LT (Tcons t1 (Tcons t2 Tnil))). 
Notation zeroH := (apply Zero Tnil).
Notation succH t := (apply Succ (Tcons t Tnil)).
Fixpoint termOfNat n :=
  match n with 
    0 => zeroH
  | S p => succH (termOfNat p)
  end.
(* end snippet instantiations *)

Section Examples.

(* begin snippet v1Plus01 *)
Let t1: Term LNN := (plusH (var 1) zeroH). 
(* end snippet v1Plus01 *)


(** forall v0, v0 = 0 \/ exists v1,  v0 = S v1 *)
(* begin snippet f1Example *)
Let f1 : Formula LNN :=
  forallH 0 
    (orH (equal (var 0) zeroH)
          (existH 1 (equal (var 0) (succH (var 1))))).
(* end snippet f1Example *)

(* begin snippet f2Example *)
Let f2 : Formula LNN :=
   (existH 2 (andH (ltH zeroH (var 2))
                 (equal (termOfNat 4) (plusH (var 2) (var 2))))).

Let f3 := (orH (equal (var 0) zeroH)
             (existH 1 (equal (var 0) (succH (var 1))))).

Let f4 := (iffH (equal (var 0) (plusH (var 1) (var 1)))
                (equal (var 0) (timesH (var 1) (termOfNat 2)))).
(* end snippet f2Example *)

(* begin snippet depthCompute *)
Compute (depth _ f1, depth _ f2).
(* end snippet depthCompute *)

(* begin snippet FormulaRect *)
About Formula_rect.
(* end snippet FormulaRect *)

(** depth-order vs structural order *)
(* begin snippet ltDepth1:: no-out *)
Goal lt_depth _ f1  f2.
Proof. red; cbn; auto with arith. Qed. 
(* end snippet ltDepth1 *)

(* begin snippet freeVarExamples *)
Compute  freeVarFormula _ f3.

Compute ListExt.no_dup _ Nat.eq_dec (freeVarFormula _ f3).

Compute close _ f3.

Compute freeVarFormula _ f3.

Compute freeVarFormula _ (close _ f4).

Compute substituteFormula LNN f4 0 (termOfNat 0).
(* end snippet freeVarExamples *)

End Examples. 
End InLNN.

Section depth_rec_demo. 
Variable L: Language.
Variable P: Formula L -> Prop. 
Variable a: Formula L. 
Goal P a. 
  eapply  Formula_depth_rec_rec with (depth L a); [| apply le_n].
  (* begin snippet depthRecDemo:: unfold no-in *)
 clear a; intros a Ha.
  (* end snippet depthRecDemo *)
Abort.
Goal P a. 
 (* begin snippet depthRecDemo2:: unfold no-in *)
 apply Formula_depth_ind2.
 (* end snippet depthRecDemo2 *)
Abort. 




End depth_rec_demo. 




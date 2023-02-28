(** Experimental *)

From Coq Require Import Arith Lists.List.
Require Import fol folProp Languages LNN folProof.
Require Import FOL_notations. 
Import FolNotations. 

Section bare_syntax. 
(* begin snippet uglyF0 *)

Definition  f0 : Formula LNN :=
      forallH 0 
        (orH  
           (equal  (var  0) 
              (@apply LNN Languages.Zero (@Tnil LNN)))
           (existH 1 (equal (var 0)
                          (apply  
                             (Languages.Succ : Functions LNN)
                             (Tcons  (var 1) (@Tnil _)))))).
(* end snippet uglyF0 *)


(* begin snippet uglyF0a *)
Compute f0. 
(* end snippet uglyF0a *)
End bare_syntax.
 
Import  LNN_notations. 
(* begin snippet CNNF0 *)
Print  f0. 
Compute f0. 
(* end snippet CNNF0 *)

Locate zero.
Locate "_ + _".
 Example t1_0 : Term _ := LNN.Plus (var 1) Zero.  
Print t1_0. 


Print t1_0.
Unset Printing Notations.  

Compute t1_0. 
Set Printing Notations.  
Section Examples.

(* begin snippet v1Plus01 *)
Let t1: Term LNN := Plus (var 1) Zero. 
(* end snippet v1Plus01 *)

Compute t1. 



(** forall v0, v0 = 0 \/ exists v1,  v0 = S v1 *)
(* begin snippet f1Example *)
Let f1 : Formula LNN :=
  (forallH 0 
    (v_ 0 = zero \/
          exH 1 (v_ 0 = Succ (v_ 1))))%fol.
(* end snippet f1Example *)

Locate orH. 


Compute f0. 

Print Relations. 


(* begin snippet f2Example *)
Let f2 : Formula LNN :=
   (exH 2 (LT zero (v_ 2) /\ natToTerm 4 = Plus (v_ 2) (v_ 2)))%fol.

Let f2' : Formula LNN :=
   (exH 2 (zero < v_ 2 /\ natToTerm 4 = Plus (v_ 2) (v_ 2)))%fol.



Let f3 := (v_ 0 = zero \/ exH 1 (v_ 0 = Succ (v_ 1)))%fol.


Let f4 := (v_ 0 = v_ 1 + v_ 1 <-> v_ 0 = v_ 1 * (natToTerm 2))%fol.
(* end snippet f2Example *)

Compute f4. 
Print f4.

(* begin snippet depthCompute *)
Compute (depth _ f1, depth _ f2).
(* end snippet depthCompute *)
(* begin snippet freeVarExamples *)
Compute  freeVarFormula _ f3.

Compute ListExt.no_dup _ Nat.eq_dec (freeVarFormula _ f3).

Compute close _ f3.

Compute freeVarFormula _ f3.

Compute freeVarFormula _ (close _ f4).

Compute substituteFormula LNN f4 0 (natToTerm 0).
(* end snippet freeVarExamples *)

Locate LT.

End Examples.



Compute AxmEq4 LNN Languages.LT. 

Compute AxmEq5 LNN Languages.Plus. 

Compute AxmEq5 LNN Languages.Succ. 

Compute EQ3 LNN. 


Check GEN LNN nil (v_ 0 = v_ 0)%fol 1. 

Compute FA1 LNN  (v_ 0 = v_ 0)%fol 0 zero%fol. 


Compute FA1 LNN  (v_ 0 = v_ 0)%fol 0 zero%fol. 

Compute substituteFormula LNN (v_ 0 = v_ 0)%fol 0 zero.

Goal Prf LNN nil
         (forallH 0 (v_ 0 = v_ 0))%fol  -> 
       Prf LNN nil (zero = zero)%fol.
intros; specialize (FA1 LNN  (v_ 0 = v_ 0)%fol 0 zero%fol). 
intro H0.
unfold substituteFormula in H0. simpl in H0.    
generalize (MP LNN nil nil _ _ H0). 
intro H1; apply H1. auto. 
Qed.






(** Experimental *)

From Coq Require Import Arith Lists.List.
Require Import fol folProp Languages LNN folProof.
Import FolNotations.
Import NNnotations. 

Section bare_syntax. 
(* begin snippet uglyF0 *)

Definition  f0 : Formula LNN :=
      forallH 0 
        (orH  
           (equal  (var  0) Zero)
           (existH 1 (equal (var 0)
                          (apply  
                             (Languages.Succ_ : Functions LNN)
                             (Tcons  (var 1) (@Tnil _)))))).
(* end snippet uglyF0 *)

Import LNN.
Print f0.
Compute f0.
Check Zero. 
Compute Zero. 
Set Printing All. 
Compute Zero. 
Unset Printing All. 

(* begin snippet uglyF0a *)
Compute f0. 
Print f0.
(* end snippet uglyF0a *)
End bare_syntax.
 
(* begin snippet CNNF0 *)
Print  f0. 
Compute f0. 
Goal f0 = (allH 0, v#0 = Zero \/ exH 1, v#0 = Succ v#1)%fol.
reflexivity. 
Qed. 
(* end snippet CNNF0 *)

Locate Plus. 
Locate "_ + _".
 Example t1_0 : Term _ := Plus (S_ (var 1))%fol Zero.  
Print t1_0. 
Check S_ Zero. 
Compute t1_0. 

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
    (v#0 = Zero \/
          existH 1 (v#0 = Succ (v#1))))%fol.
(* end snippet f1Example *)
Compute f1. 
Print f1. 

(* To redefine (deleted by error) 
Goal f1 = f1. 
compute. 
rewrite  exHfold at 1. 
reflexivity. 
Qed. 
*)

Compute f0. 

Print Relations. 


(* begin snippet f2Example *)
Let f2 : Formula LNN :=
   (existH 2 (LT Zero (v#2) /\ natToTerm 4 = Plus (v#2) (v#2)))%fol.

Let f2' : Formula LNN :=
   (existH 2 (Zero < v#2 /\ natToTerm 4 = Plus (v#2) (v#2)))%fol.

Let f3 := (v#0 = Zero \/ existH 1 (v#0 = Succ (v#1)))%fol.


Let f4 := (v#0 = v#1 + v#1 <-> v#0 = v#1 * (natToTerm 2))%fol.
(* end snippet f2Example *)

Compute f4. 
Print f4.

Check (Plus Zero  Zero)%fol. 
Compute (Plus Zero  Zero)%fol. 
(* begin snippet depthCompute *)
Compute (depth _ f1, depth _ f2).
(* end snippet depthCompute *)
(* begin snippet freeVarExamples *)
Compute  freeVarF f3.

Compute List.nodup Nat.eq_dec (freeVarF f3).

Compute close _ f3.

Compute freeVarFormula  f3.

Compute freeVarFormula  (close _ f4).

Compute substF f4 0 (natToTerm 0).
(* end snippet freeVarExamples *)

Locate LT.

End Examples.



Compute AxmEq4 LNN Languages.LT_. 

Compute AxmEq5 LNN Languages.Plus_. 

Compute AxmEq5 LNN Languages.Succ_. 

Compute EQ3 LNN. 


Check GEN LNN nil (v#0 = v#0)%fol 1. 

Compute FA1 LNN  (v#0 = v#0)%fol 0 Zero%fol. 


Compute FA1 LNN  (v#0 = v#0)%fol 0 Zero%fol. 

Compute substF  (v#0 = v#0)%fol 0 Zero.

Goal Prf LNN nil
         (forallH 0 (v#0 = v#0))%fol  -> 
       Prf LNN nil (Zero = Zero)%fol.
intros; specialize (FA1 LNN  (v#0 = v#0)%fol 0 Zero%fol). 
intro H0.
unfold substF in H0. simpl in H0.    
generalize (MP LNN nil nil _ _ H0). 
intro H1; apply H1. auto. 
Qed.






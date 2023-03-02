(** Experimental *)

Require Import fol.

Module FolNotations.
Declare Scope fol_scope.
Delimit Scope fol_scope with fol.

Infix "=" := (equal _): fol_scope.
Infix "\/" := (orH): fol_scope.
Infix "/\" := (andH):fol_scope.
Infix "->" := (impH): fol_scope.
Notation "~ A" := (@notH _ A): fol_scope. 
Notation "A <-> B" := (@iffH _ A B): fol_scope.


Notation k_ t := (apply  (t:Functions _)  (Tnil)).

Notation app1 f arg := 
  (apply  (f: Functions _)  (Tcons arg (Tnil))).
About Tnil.
Notation app2 f arg1 arg2 := 
  (apply   (f: Functions _) 
     (Tcons  arg1 (Tcons  arg2 (Tnil)))).

Notation "t = u" := (@equal _ t u): fol_scope.


Reserved Notation "x '\/'' y" (at level 85, right associativity).
Reserved Notation "x '/\'' y" (at level 80, right associativity).
Reserved Notation "x '<->'' y" (at level 95, no associativity).
Reserved Notation "x '<->''' y" (at level 95, no associativity).

Notation "x \/' y" := (~ x -> y)%fol : fol_scope. 
Notation "x /\' y" := (~ (~ x \/'  ~ y))%fol : fol_scope.
Notation "x <->'' y" := ((x -> y) /\ (y -> x))%fol:  fol_scope.
Notation "x <->' y" := (~ (~ (x -> y) \/' ~(y -> x)))%fol : fol_scope.

Notation exH := (existH).
Notation v_ := var.
Notation exH' v A := (~ (forallH v (~ A)))%fol.

End FolNotations.

Export FolNotations. 


Section LExamples. 
Variable L: Language. 
Variables P Q : Formula L. 

Let ex1 : Formula L :=  (P /\ Q)%fol. 
About impH.
Let ex2 : Formula L := (~ (~~P -> ~Q))%fol. 
Print ex2. 
Let ex3 : Formula L:= (~(~P \/ ~Q))%fol. 
Print ex3. 
Compute ex3. 
Print ex1. 
Compute ex1. 

Check (forallH 5 (v_ 5 = v_ 5) -> forallH 0 (v_ 0 = v_ 0))%fol.

End LExamples.

(*


Notation "t = u" := (@equal _ t u): cfol_scope.

Notation app1 f arg := 
  (apply  (f: Functions _) 
     (Tcons  arg Tnil)).

Notation app2 f arg1 arg2 := 
  (apply   (f: Functions _) 
     (Tcons arg1 (Tcons arg2 Tnil))).

Notation v_ := (var).

 Section Consistance. 
  Goal forall L A B, @orH L A B = (A \/ B)%cfol. 
   reflexivity. Qed. 
  
  Goal forall L A B, andH (L:=L) A B = (A /\ B)%cfol. 
    reflexivity. Qed.  
  

 End Consistance. 

End CFOL_notations.
*)

Section Correctness. 
 Variable L: Language.
 Variables P Q R : Formula L. 

 Goal (P \/ Q)%fol = (P \/' Q)%fol.
 reflexivity. 
 Qed. 

Goal (P /\ Q)%fol = (P /\' Q)%fol.
Proof. reflexivity. Qed. 


End Correctness.

Section JustTry.
Variable L: Language.
Check (@var L 1 = var 2)%fol.
Check (v_ 1 = v_ 2)%fol: Formula L.
Check (exH 1 (v_ 1 = v_ 1))%fol : Formula L.
Compute (exH 1 (v_ 1 = v_ 1))%fol : Formula L.


Check (v_ 1 = v_ 1 \/ v_ 2 = v_ 2)%fol: Formula L. 
Compute (v_ 1 = v_ 1 \/ v_ 2 = v_ 2)%fol: Formula L.

Check (v_ 1 = v_ 1 \/ v_ 2 = v_ 2)%fol: Formula L. 
Compute (v_ 1 = v_ 1 \/ v_ 2 = v_ 2)%fol: Formula L.

Check (v_ 1 = v_ 1 \/ v_ 2 = v_ 2)%fol: Formula L. 
Compute (v_ 1 = v_ 1 \/ v_ 2 = v_ 2)%fol: Formula L.

Check (v_ 1 = v_ 1 \/ v_ 2 = v_ 2)%fol: Formula L. 
Compute (v_ 1 = v_ 1 \/ v_ 2 = v_ 2)%fol: Formula L.

Check (v_ 1 = v_ 1 <-> v_ 2 = v_ 2)%fol: Formula L. 
Compute (v_ 1 = v_ 1 <-> v_ 2 = v_ 2)%fol: Formula L.

End JustTry.

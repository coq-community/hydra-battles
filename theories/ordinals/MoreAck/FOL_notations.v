(** Experimental *)

Require Import fol.

#[local] Arguments notH _ _ : clear implicits.


Module FOL_notations.
Declare Scope fol_scope.
Delimit Scope fol_scope with fol.

Infix "=" := (equal _): fol_scope.
Infix "\/" := (orH): fol_scope.
Infix "/\" := (andH):fol_scope.
Infix "->" := (impH): fol_scope.
Notation "~ A" := (@notH _ A): fol_scope. 

Notation k_ t := (apply  (t:Functions _)  (Tnil)).

Notation app1 f arg := 
  (apply  (f: Functions _)  (Tcons arg (Tnil))).
About Tnil.
Notation app2 f arg1 arg2 := 
  (apply   (f: Functions _) 
     (Tcons  arg1 (Tcons  arg2 (Tnil)))).

Notation "t = u" := (@equal _ t u): fol_scope.

Notation allH v A := (forallH v A).
Notation exH := (existH).
Notation v_ := var.
End FOL_notations.



Declare Scope cfol_scope. 
Delimit Scope cfol_scope with cfol. 

Module CFOL_notations.

Notation "~ A" := (@notH _ A): cfol_scope.

Notation " A -> B" := (@impH _ A B) : cfol_scope.
Notation " A \/ B" := ((@notH _  A) -> B)%cfol : cfol_scope.
Notation " A /\ B" := 
     (@notH _ (@notH _  A \/ @notH _ B))%cfol 
 : cfol_scope.

Notation exH v A := 
  (@notH _ (@forallH _ v (@notH _ A))).

Notation allH v A:= (forallH v A).

Notation "A <-> B" := (( A -> B) /\ (B -> A))%cfol:  cfol_scope.

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


Import FOL_notations. 
Section JustTry.
Variable L: Language.
Check (@var L 1 = var 2)%fol.
Check (v_ 1 = v_ 2)%fol: Formula L.
Check (exH 1 (v_ 1 = v_ 1))%fol : Formula L.
Check (v_ 1 = v_ 1 \/ v_ 2 = v_ 2)%fol: Formula L. 
Compute (v_ 1 = v_ 1 \/ v_ 2 = v_ 2)%fol: Formula L.
 Import CFOL_notations. 
Check (v_ 1 = v_ 1 \/ v_ 2 = v_ 2)%fol: Formula L. 
Compute (v_ 1 = v_ 1 \/ v_ 2 = v_ 2)%fol: Formula L.
Import FOL_notations. 
Check (v_ 1 = v_ 1 \/ v_ 2 = v_ 2)%fol: Formula L. 
Compute (v_ 1 = v_ 1 \/ v_ 2 = v_ 2)%fol: Formula L.
Open Scope fol_scope.

Check (v_ 1 = v_ 1 \/ v_ 2 = v_ 2)%fol: Formula L. 
Compute (v_ 1 = v_ 1 \/ v_ 2 = v_ 2)%fol: Formula L.
Open Scope cfol_scope.

Check (v_ 1 = v_ 1 \/ v_ 2 = v_ 2)%fol: Formula L. 
Compute (v_ 1 = v_ 1 \/ v_ 2 = v_ 2)%fol: Formula L.

End JustTry.

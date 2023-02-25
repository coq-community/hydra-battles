(** Experimental *)

Require Import fol.


Module FOL_notations.
Declare Scope fol_scope.
Delimit Scope fol_scope with fol.

Infix "=" := (fol.equal _): fol_scope.
Infix "\/" := (fol.orH): fol_scope.
Infix "/\" := (fol.andH):fol_scope.
Infix "->" := (fol.impH): fol_scope.
Notation "~ A" := (@fol.notH _ A): fol_scope. 

Notation k_ t := (fol.apply  (t:Functions _)  (fol.Tnil)).

Notation app1 f arg := 
  (fol.apply  (f: Functions _)  (Tcons arg (fol.Tnil))).
About Tnil.
Notation app2 f arg1 arg2 := 
  (fol.apply   (f: Functions _) 
     (Tcons  arg1 (Tcons  arg2 (fol.Tnil)))).

Notation "t = u" := (@fol.equal _ t u): fol_scope.

Notation allH v A := (fol.forallH v A).
Notation exH := (fol.existH).
Notation v_ := var.
End FOL_notations.



Declare Scope cfol_scope. 
Delimit Scope cfol_scope with cfol. 

Module CFOL_notations.

Notation "~ A" := (@fol.notH _ A): cfol_scope.

Notation " A -> B" := (@fol.impH _ A B) : cfol_scope.
Notation " A \/ B" := ((@fol.notH _  A) -> B)%cfol : cfol_scope.
Notation " A /\ B" := 
     (@fol.notH _ (@fol.notH _  A \/ @fol.notH _ B))%cfol 
 : cfol_scope.

Notation exH v A := 
  (@fol.notH _ (@fol.forallH _ v (@fol.notH _ A))).

Notation allH v A:= (fol.forallH v A).

Notation "A <-> B" := (( A -> B) /\ (B -> A))%cfol:  cfol_scope.

Notation "t = u" := (@fol.equal _ t u): cfol_scope.

Notation app1 f arg := 
  (fol.apply  (f: Functions _) 
     (fol.Tcons  arg fol.Tnil)).

Notation app2 f arg1 arg2 := 
  (fol.apply   (f: Functions _) 
     (fol.Tcons arg1 (fol.Tcons arg2 fol.Tnil))).

Notation v_ := (fol.var).

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

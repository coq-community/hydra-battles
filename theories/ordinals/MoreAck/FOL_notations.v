Require Import fol.


Module FOL_notations.
Declare Scope fol_scope.
Delimit Scope fol_scope with fol.

Infix "=" := (fol.equal _): fol_scope.
Infix "\/" := (fol.orH _): fol_scope.
Infix "/\" := (fol.andH _):fol_scope.
Infix "->" := (fol.impH): fol_scope.
Notation "~ A" := (@fol.notH _ A): fol_scope. 
Notation atH := (fol.atomic _).
Notation k_ t := (fol.apply _ (t:Functions _)  (fol.Tnil _)).

Notation app1 f arg := 
  (fol.apply _ (f: Functions _)  (fol.Tcons _ _ arg (fol.Tnil _))).

Notation app2 f arg1 arg2 := 
  (fol.apply  _ (f: Functions _) 
     (fol.Tcons _ _ arg1 (fol.Tcons _ _ arg2 (fol.Tnil _)))).

Notation "t = u" := (@fol.equal _ t u): fol_scope.

Notation allH := (fol.forallH _).
Notation exH := (fol.existH _).
Notation v_ := (fol.var _).
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

Notation allH := (fol.forallH _).

Notation "A <-> B" := (( A -> B) /\ (B -> A))%cfol:  cfol_scope.

Notation "t = u" := (@fol.equal _ t u): cfol_scope.

Notation app1 f arg := 
  (fol.apply _ (f: Functions _) 
     (fol.Tcons _ _ arg (fol.Tnil _))).

Notation app2 f arg1 arg2 := 
  (fol.apply  _ (f: Functions _) 
     (fol.Tcons _ _ arg1 (fol.Tcons _ _ arg2 (fol.Tnil _)))).

Notation v_ := (fol.var _).

 Section Consistance. 
  Goal forall L A B, @orH L A B = (A \/ B)%cfol. 
   reflexivity. Qed. 
  
  Goal forall L A B, andH  L A B = (A /\ B)%cfol. 
    reflexivity. Qed.  
  

 End Consistance. 

End CFOL_notations.


Import FOL_notations. 
Section JustTry.
Variable L: Language.
Check (var L 1 = var _ 2)%fol.
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

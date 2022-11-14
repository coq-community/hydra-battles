Require Import fol.


Module FOL_notations.
Declare Scope fol_scope.
Delimit Scope fol_scope with fol.

Infix "=" := (fol.equal _): fol_scope.
Infix "\/" := (fol.orH _): fol_scope.
Infix "/\" := (fol.andH _):fol_scope.
Infix "->" := (fol.impH _): fol_scope.
Notation "~" := (fol.notH _): fol_scope. 
Notation atH := (fol.atomic _).
(*Notation "A \/ B" := (fol.impH _ (fol.notH _ A) B) (only printing) : fol_scope. *)

Notation k_ t := (fol.apply _ (t:Functions _)  (fol.Tnil _)).

Notation app1 f arg := 
  (fol.apply _ (f: Functions _)  (fol.Tcons _ _ arg (fol.Tnil _))).

Notation app2 f arg1 arg2 := 
  (fol.apply  _ (f: Functions _) 
     (fol.Tcons _ _ arg1 (fol.Tcons _ _ arg2 (fol.Tnil _)))).

Notation allH := (fol.forallH _).
Notation exH := (fol.existH _).
Notation v_ := (fol.var _).
End FOL_notations.

Import FOL_notations.

Declare Scope Cfol_scope. 
Delimit Scope Cfol_scope with cfol. 

Module CFOL_notations.
Notation " A -> B" := (@fol.impH _ A B) : Cfol_scope.
Notation " A \/ B" := ((@fol.notH _  A) -> B)%cfol : Cfol_scope.
Notation " A /\ B" := (@fol.notH _ (@fol.notH _  A \/ @fol.notH _ B))%cfol: Cfol_scope.
Notation "~ A" := (@fol.notH _ A): Cfol_scope.
Notation exH v A := (@fol.notH _ (@fol.forallH _ v (@fol.notH _ A))).
Notation "A <-> B" := (( A -> B) /\ (B -> A))%cfol: Cfol_scope.
Notation "t = u" := (@fol.equal _ t u): Cfol_scope.

Notation atH := (fol.atomic _).

Notation k_ t := (fol.apply _ (t:Functions _)  (fol.Tnil _)).

Notation app1 f arg := 
  (fol.apply _ (f: Functions _)  (fol.Tcons _ _ arg (fol.Tnil _))).

Notation app2 f arg1 arg2 := 
  (fol.apply  _ (f: Functions _) 
     (fol.Tcons _ _ arg1 (fol.Tcons _ _ arg2 (fol.Tnil _)))).

Goal forall L (A B: Formula L), (A \/ B)%cfol = (A \/ B)%fol.
reflexivity. 
Qed.

Goal forall L (A B: Formula L), (A /\ B)%cfol = (A /\ B)%fol.
reflexivity. 
Qed.


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
Open Scope Cfol_scope.

Check (v_ 1 = v_ 1 \/ v_ 2 = v_ 2)%fol: Formula L. 
Compute (v_ 1 = v_ 1 \/ v_ 2 = v_ 2)%fol: Formula L.

End JustTry.

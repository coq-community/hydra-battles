Require Import fol.


Module FOL_notations.
Declare Scope fol_scope.
Delimit Scope fol_scope with fol.

Infix "=" := (equal _): fol_scope.
Infix "\/" := (orH _): fol_scope.
Infix "/\" := (andH _):fol_scope.
Infix "->" := (impH _): fol_scope.
Notation "~" := (notH _): fol_scope. 
Notation atH := (atomic _).
Notation app1 f arg := (apply _ f (Tcons _ _ arg (Tnil _))).
Notation app2 f arg1 arg2 := 
  (apply _ f (Tcons _ _ arg2 (Tcons _ _ arg2 (Tnil _)))).
Notation allH := (forallH _).
Notation exH := (forallH _).
Notation v_ := (var _).
End FOL_notations.

Import FOL_notations. 
Section JustTry.
Variable L: Language.
Check (var L 1 = var _ 2)%fol.
Check (v_ 1 = v_ 2)%fol: Formula L.
Check (exH 1 (v_ 1 = v_ 1))%fol : Formula L.
End JustTry.

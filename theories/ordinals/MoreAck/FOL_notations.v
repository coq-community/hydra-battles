Require Import fol.


Module FOL_notations.
Declare Scope fol_scope.
Delimit Scope fol_scope with fol.

Infix "=" := (equal _): fol_scope.
Infix "\/" := (orH _): fol_scope.
Infix "/\" := (andH _):fol_scope.
Notation v_ := (var _).
End FOL_notations.

Import FOL_notations. 
Section JustTry.
Variable L: Language.
Check (var L 1 = var _ 2)%fol.
Check (v_ 1 = v_ 2)%fol: Formula L.

End JustTry.

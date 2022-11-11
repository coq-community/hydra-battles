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
Section JustTry.
Variable L: Language.
Check (var L 1 = var _ 2)%fol.
Check (v_ 1 = v_ 2)%fol: Formula L.
Check (exH 1 (v_ 1 = v_ 1))%fol : Formula L.
End JustTry.

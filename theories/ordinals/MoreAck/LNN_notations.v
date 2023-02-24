Require Import fol Languages PAtheory LNN.


(*** Expermimental ***)


Module LNN_notations.
Declare Scope lnn_scope.
Delimit Scope lnn_scope with lnn.
Infix "=" := (fol.equal LNN): lnn_scope.
Infix "\/" := (fol.orH LNN): lnn_scope.
Infix "/\" := (fol.andH LNN):lnn_scope.
Infix "->" := (@fol.impH LNN): lnn_scope.
Infix "<->" := (fol.iffH LNN): lnn_scope.
Notation "~" := (fol.notH LNN): lnn_scope. 

Set Printing Implicits. 
Check Zero. 
Locate Zero. 
Notation zero := (@fol.apply LNN (Languages.Zero: Functions LNN) (fol.Tnil)).
Check zero.

Notation app1 f arg := 
  (@fol.apply LNN (f: Functions _) 
     (fol.Tcons _ _ arg (fol.Tnil))).

Notation app2 f arg1 arg2 := 
  (@fol.apply  LNN (f: Functions _) 
     (fol.Tcons _ _ arg1 (fol.Tcons _ _ arg2 (fol.Tnil)))).

Notation allH := (fol.forallH LNN).
Notation exH := (fol.existH LNN).
Notation v_ := (@fol.var LNN).

Notation "t1 + t2" := 
  (fol.apply  LNN Languages.Plus 
     (fol.Tcons _ _ t1 (fol.Tcons _ _ t2 (fol.Tnil)))): 
    lnn_scope.

Notation "t1 * t2" := (fol.apply  LNN Languages.Times 
     (fol.Tcons _ _ t1 
        (fol.Tcons _ _ t2 (fol.Tnil)))): lnn_scope.

Notation S_ t  := (Succ t).
   

Notation "t1 < t2" := 
 (atomic  Languages.LT
    (fol.Tcons _ _ t1 
       (fol.Tcons _ _ t2 (fol.Tnil)))): lnn_scope.      
 
End LNN_notations.

(* A clone of lnn_scope for printing correctly disjunctions, conjunctions of fully computed formulas etc . *)

Declare Scope cnn_scope. 
Delimit Scope cnn_scope with cnn. 

Module CLNN_notations.

Notation "~ A" := (@fol.notH LNN A): cnn_scope.

Notation " A -> B" := (@fol.impH LNN A B) : cnn_scope.
Notation " A \/ B" := ((@fol.notH LNN  A) -> B)%cnn : cnn_scope.
Notation " A /\ B" := 
     (@fol.notH LNN (@fol.notH LNN  A \/ @fol.notH _ B))%cnn 
 : cnn_scope.

Notation allH := (@fol.forallH LNN).

Notation exH v A := 
  (@fol.notH _ (@fol.forallH _ v (@fol.notH _ A))).

Notation "A <-> B" := (( A -> B) /\ (B -> A))%cnn:  cnn_scope.

Notation "t = u" := (@fol.equal LNN t u): cnn_scope.

Notation v_ := (@fol.var LNN).

Notation app1 f arg := 
  (fol.apply LNN (f: Functions _) 
     (fol.Tcons _ _ arg (fol.Tnil))).

Notation app2 f arg1 arg2 := 
  (fol.apply  LNN (f: Functions _) 
     (fol.Tcons _ _ arg1 (fol.Tcons _ _ arg2 (fol.Tnil)))).

Notation "t1 + t2" := (@fol.apply  LNN Languages.Plus 
     (fol.Tcons _ _ t1 (fol.Tcons _ _ t2 (fol.Tnil)))): cnn_scope.

Notation "t1 * t2" := (@fol.apply  LNN Languages.Times 
     (fol.Tcons _ _ t1 (fol.Tcons _ _ t2 (fol.Tnil)))): cnn_scope.

Notation S_ t  := 
   (@fol.apply  LNN Languages.Succ 
     (fol.Tcons _ _ t (fol.Tnil))).

About fol.atomic. 
Notation "t1 < t2" := 
 (@fol.atomic LNN Languages.LT
    (fol.Tcons _ _ t1 
       (fol.Tcons _ _ t2 (fol.Tnil))))(*only printing*): cnn_scope.      

Print Zero.
Locate Zero. 
Definition  zero := (fol.apply (Languages.Zero: Functions LNN) Tnil).

 Section Consistance. 
  Goal forall A B, orH  A B = (A \/ B)%cnn. 
   reflexivity. Qed. 
  
  Goal forall A B, andH  A B = (A /\ B)%cnn. 
    reflexivity. Qed.  
  
 Goal forall t1 t2, LT t1 t2 = (t1 < t2)%cnn. 
    reflexivity. Qed.  
 End Consistance. 

End CLNN_notations.


(*

Import LNN_notations.

Compute ((v_ 0 = v_ 0 -> v_ 1 = v_ 1) /\ 
           (v_ 1 = v_ 1 -> v_ 0 = v_ 0))%lnn. 

Compute fol.atomic LNN Languages.LT 
 (fol.Tcons _ _ (fol.var _ 1) 
    (fol.Tcons _ _ (fol.var _ 2) (fol.Tnil _))).

Compute (v_ 0 < v_ 1)%lnn. 
Fail Compute (v_ 0 < v_ 1)%cnn. 

Import CLNN_notations. 

Compute (v_ 0 < v_ 1)%cnn. 

Compute ((v_ 0 = v_ 0 -> v_ 1 = v_ 1) /\ 
           (v_ 1 = v_ 1 -> v_ 0 = v_ 0))%lnn. 

Compute (exH 1 (v_ 0 = v_ 0 + v_ 0))%lnn.



Check (forallH 1 (v_ 0 = v_ 0))%lnn.

Check (forallH 1 (v_ 0 = v_ 0 + v_ 0))%lnn.

Check ((v_ 0 = v_ 0 -> v_ 1 = v_ 1) /\ (v_ 1 = v_ 1 -> v_ 0 = v_ 0))%cnn.

Compute ((v_ 0 = v_ 0 -> v_ 1 = v_ 1) /\ (v_ 1 = v_ 1 -> v_ 0 = v_ 0))%cnn.

Check ((v_ 0 = v_ 0 -> v_ 1 = v_ 1) /\ (v_ 1 = v_ 1 -> v_ 0 = v_ 3))%cnn.

Compute ((v_ 0 = v_ 0 -> v_ 1 = v_ 1) /\ (v_ 1 = v_ 1 -> v_ 0 = v_ 0))%cnn.

Compute ((v_ 0 = v_ 0 -> v_ 1 = v_ 1) /\ (v_ 1 = v_ 1 -> v_ 0 = v_ 0))%lnn. 



Check (forallH 1 (v_ 0 = v_ 0 + zero \/ v_ 1 = v_ 2))%lnn.

Check (forallH 1 (v_ 0 = v_ 0 + zero \/ v_ 1 = v_ 2))%lnn.



Goal zero = Zero. 
Set Printing All.
reflexivity. 
Qed.

Check (forallH  1 (v_ 0 = v_ 0 + zero))%lnn.

Unset Printing All. 
Check (forallH  1 (v_ 0 = v_ 0 + zero))%lnn.


*)

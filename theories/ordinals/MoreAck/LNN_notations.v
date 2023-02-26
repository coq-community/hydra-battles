Require Import fol Languages PAtheory LNN.


(*** Expermimental ***)


Module LNN_notations.
Declare Scope lnn_scope.
Delimit Scope lnn_scope with lnn.
Infix "=" := (equal LNN): lnn_scope.
Infix "\/" := (orH LNN): lnn_scope.
Infix "/\" := (andH LNN):lnn_scope.
Infix "->" := (impH LNN): lnn_scope.
Infix "<->" := (iffH LNN): lnn_scope.
Notation "~" := (notH LNN): lnn_scope. 

Set Printing Implicits. 
Check Zero. 
Locate Zero. 
Notation zero := (@apply LNN (Languages.Zero: Functions LNN) (fol.Tnil)).
Check zero.

Notation app1 f arg := 
  (@apply LNN (f: Functions _) 
     (Tcons arg (Tnil))).

Notation app2 f arg1 arg2 := 
  (@apply  LNN (f: Functions _) 
     (Tcons arg1 (Tcons arg2 (Tnil)))).

Notation allH := (forallH LNN).
Notation exH := (existH LNN).
Notation v_ := (@var LNN).

Notation "t1 + t2" := 
  (apply  LNN Languages.Plus 
     (Tcons t1 (Tcons t2 (Tnil)))): 
    lnn_scope.

Notation "t1 * t2" := (apply  LNN Languages.Times 
     (Tcons  t1 
        (Tcons  t2 (Tnil)))): lnn_scope.

Notation S_ t  := (Succ t).
   

Notation "t1 < t2" := 
 (atomic  Languages.LT
    (Tcons  t1 
       (Tcons t2 (Tnil)))): lnn_scope.      
 
End LNN_notations.

(* A clone of lnn_scope for printing correctly disjunctions, conjunctions of fully computed formulas etc . *)

Declare Scope cnn_scope. 
Delimit Scope cnn_scope with cnn. 

Module CLNN_notations.

Notation "~ A" := (@notH LNN A): cnn_scope.

Notation " A -> B" := (@impH LNN A B) : cnn_scope.
Notation " A \/ B" := ((@notH LNN  A) -> B)%cnn : cnn_scope.
Notation " A /\ B" := 
     (@notH LNN (@notH LNN  A \/ @notH _ B))%cnn 
 : cnn_scope.

Notation allH := (@forallH LNN).

Notation exH v A := 
  (@notH _ (@forallH _ v (@notH _ A))).

Notation "A <-> B" := (( A -> B) /\ (B -> A))%cnn:  cnn_scope.

Notation "t = u" := (@equal LNN t u): cnn_scope.

Notation v_ := (@var LNN).

Notation app1 f arg := 
  (apply LNN (f: Functions _) 
     (Tcons  arg (Tnil))).

Notation app2 f arg1 arg2 := 
  (apply  LNN (f: Functions _) 
     (Tcons  arg1 (Tcons arg2 (Tnil)))).

Notation "t1 + t2" := (@apply  LNN Languages.Plus 
     (Tcons t1 (Tcons  t2 (Tnil)))): cnn_scope.

Notation "t1 * t2" := (@apply  LNN Languages.Times 
     (Tcons  t1 (Tcons  t2 (Tnil)))): cnn_scope.

Notation S_ t  := 
   (@apply  LNN Languages.Succ 
     (Tcons  t (Tnil))).

About atomic. 
Notation "t1 < t2" := 
 (@atomic LNN Languages.LT
    (Tcons  t1 
       (Tcons  t2 (Tnil))))(*only printing*): cnn_scope.      

Print Zero.
Locate Zero. 
Definition  zero := (apply (Languages.Zero: Functions LNN) Tnil).

 Section Consistance. 
  Goal forall A B, orH  A B = (A \/ B)%cnn. 
   reflexivity. Qed. 
  
  Goal forall A B, andH  A B = (A /\ B)%cnn. 
    reflexivity. Qed.  
  
 Goal forall t1 t2, LT t1 t2 = (t1 < t2)%cnn. 
    reflexivity. Qed.  
 End Consistance. 

End CLNN_notations.




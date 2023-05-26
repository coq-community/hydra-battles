(** folProof.v

    Original script by Russel O'Connor

*)


From Coq Require Import Ensembles Lists.List Arith. 

Require Export fol.
Require Import folProp.
Import FolNotations.

Section ProofH.

Variable L : Language.

Let Formula := Formula L.
Let Formulas := Formulas L.
Let System := System L.
Let Term := Term L.
Let Terms := Terms L.

Fixpoint nVars (n: nat) : Terms n * Terms n:=
  match n with 
    0 => (Tnil, Tnil)
  | S n0 => 
      (let (a,b) := nVars n0 in
       (Tcons (var (n0 + n0)) a, 
         Tcons  (var (S (n0 + n0))) b))
  end.

Section Example.
Compute nVars 3. 
End Example. 

Definition AxmEq4 (R : Relations L) : Formula.
Proof. 
  assert (X: forall (f : Formula) (n : nat), Formula).
  { intros f n; induction n as [| n Hrecn].
    - exact f.
    - exact (v#(n + n) = v#(S (n + n)) -> Hrecn)%fol.
  } 
  apply X.
  - induction (nVars (arityR L R)).
    apply (atomic R a <->  atomic R b)%fol.
  - apply (arityR L R).
Defined.

(** TODO : An example in PA *)

Definition AxmEq5 (f : Functions L) : Formula.
Proof. 
  assert (X: forall (f : Formula) (n : nat), Formula).
  { intros f0 n; induction n as [| n Hrecn].
    - exact f0.
    - exact (impH (equal (var (n + n)) (var (S (n + n)))) Hrecn).
  } 
  apply X.
  induction (nVars (arityF L f)) as [a b].
  - apply (equal (apply f a) (apply f b)).
  - apply (arityF L f).
Defined.

Inductive Prf : Formulas -> Formula -> Set :=
| AXM : forall A : Formula, Prf (A :: nil) A
| MP :
  forall (Axm1 Axm2 : Formulas) (A B : Formula),
    Prf Axm1 (impH A B) -> Prf Axm2 A -> Prf (Axm1 ++ Axm2) B
| GEN :
  forall (Axm : Formulas) (A : Formula) (v : nat),
    ~ In v (freeVarListFormula L Axm) -> Prf Axm A ->
    Prf Axm  (forallH v A)
| IMP1 : forall A B : Formula, Prf nil (A -> B -> A)%fol
| IMP2 :
  forall A B C : Formula,
    Prf nil ((A -> B -> C) -> (A -> B) -> A -> C)%fol
| CP :
  forall A B : Formula,
    Prf nil ((~ A -> ~ B) -> B -> A)%fol
| FA1 :
  forall (A : Formula) (v : nat) (t : Term),
    Prf nil ((allH v, A) -> substF L A v t)%fol
| FA2 :
  forall (A : Formula) (v : nat),
    ~ In v (freeVarFormula L A) -> Prf nil (A -> allH v, A)%fol
| FA3 :
  forall (A B : Formula) (v : nat),
    Prf nil
      ((allH v, A -> B) -> (allH v, A) -> allH v, B)%fol
| EQ1 : Prf nil (v#0 = v#0)%fol
| EQ2 : Prf nil (v#0 = v#1 -> v#1 = v#0)%fol
| EQ3 :
  Prf nil
    (v#0 = v#1 -> v#1 = v#2 -> v#0 = v#2)%fol
| EQ4 : forall R : Relations L, Prf nil (AxmEq4 R)
| EQ5 : forall f : Functions L, Prf nil (AxmEq5 f).

Definition SysPrf (T : System) (f : Formula) :=
  exists Axm : Formulas,
    (exists prf : Prf Axm f,
       (forall g : Formula, In g Axm -> mem _ T g)).

Definition Inconsistent (T : System) := forall f : Formula, SysPrf T f.

Definition Consistent (T : System) := exists f : Formula, ~ SysPrf T f.

End ProofH.

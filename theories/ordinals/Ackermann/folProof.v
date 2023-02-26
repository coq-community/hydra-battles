
From Coq Require Import Ensembles Lists.List Arith. 

Require Export fol.
Require Import folProp.

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

Definition AxmEq4 (R : Relations L) : Formula.
Proof. 
  assert (X: forall (f : Formula) (n : nat), Formula).
  { intros f n; induction n as [| n Hrecn].
    - exact f.
    - exact (impH (equal (var (n + n)) (var (S (n + n)))) Hrecn).
  } 
  apply X.
  - induction (nVars (arity L (inl _ R))).
    apply (iffH (atomic R a) (atomic R b)).
  - apply (arity L (inl _ R)).
Defined.


Definition AxmEq5 (f : Functions L) : Formula.
Proof. 
  assert (X: forall (f : Formula) (n : nat), Formula).
  { intros f0 n; induction n as [| n Hrecn].
    - exact f0.
    - exact (impH (equal (var (n + n)) (var (S (n + n)))) Hrecn).
  } 
  apply X.
  induction (nVars (arity L (inr _ f))) as [a b].
  - apply (equal (apply f a) (apply f b)).
  - apply (arity L (inr _ f)).
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
| IMP1 : forall A B : Formula, Prf nil (impH A (impH B A))
| IMP2 :
  forall A B C : Formula,
    Prf nil (impH (impH A (impH B C)) (impH (impH A B) (impH A C)))
| CP :
  forall A B : Formula,
    Prf nil (impH (impH (notH A) (notH B)) (impH B A))
| FA1 :
  forall (A : Formula) (v : nat) (t : Term),
    Prf nil (impH (forallH v A) (substituteFormula L A v t))
| FA2 :
  forall (A : Formula) (v : nat),
    ~ In v (freeVarFormula L A) -> Prf nil (impH A (forallH v A))
| FA3 :
  forall (A B : Formula) (v : nat),
    Prf nil
      (impH (forallH v (impH A B)) (impH (forallH v A) (forallH v B)))
| EQ1 : Prf nil (equal (var 0) (var 0))
| EQ2 : Prf nil (impH (equal (var 0) (var 1)) (equal (var 1) (var 0)))
| EQ3 :
  Prf nil
    (impH (equal (var 0) (var 1))
       (impH (equal (var 1) (var 2)) (equal (var 0) (var 2))))
| EQ4 : forall R : Relations L, Prf nil (AxmEq4 R)
| EQ5 : forall f : Functions L, Prf nil (AxmEq5 f).

Definition SysPrf (T : System) (f : Formula) :=
  exists Axm : Formulas,
    (exists prf : Prf Axm f,
       (forall g : Formula, In g Axm -> mem _ T g)).

Definition Inconsistent (T : System) := forall f : Formula, SysPrf T f.

Definition Consistent (T : System) := exists f : Formula, ~ SysPrf T f.

End ProofH.

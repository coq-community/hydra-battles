Require Import folProof.
Require Import Arith.
Require Import folProp.
Require Import LNN.
Require Import Coq.Lists.List.
Import NNnotations. 

Definition wConsistent (T : System) :=
  forall (f : Formula) (v : nat),
  (forall x : nat, In x (freeVarF LNN f) -> v = x) ->
  SysPrf T (existH v (notH f)) ->
  exists n : nat, ~ SysPrf T (substF f v (natToTerm n)).

Lemma wCon2Con : forall T : System, wConsistent T -> Consistent LNN T.
Proof.
  intros T H; unfold wConsistent in H.
  unfold Consistent, Inconsistent; 
    assert (H0: SysPrf T (exH 0, ~ ~ v#0 = v#0)%nn) 
    by apply existSimp, nnI, eqRefl.
  assert
    (H1 : forall x : nat,
        In x (freeVarF LNN (v#0 <> v#0)%nn) -> 0 = x)
    by (intros x H1; simpl in H1; repeat induction H1; auto).
  destruct  (H _ _ H1 H0) as [x H2]; 
    now exists (substF (v#0 <> v#0)%nn 0
                  (natToTerm x)).
Qed.

Definition wInconsistent (T : System) :=
  exists f : Formula,
    (exists v : nat,
       (forall x : nat, In x (freeVarF LNN f) -> v = x) /\
       SysPrf T (existH v (notH f)) /\
       (forall n : nat, SysPrf T (substF f v (natToTerm n)))).

Lemma notCon2wNotCon :
 forall T : System, Inconsistent LNN T -> wInconsistent T.
Proof.
  intros T H; unfold wInconsistent; exists (equal Zero Zero).
  exists 0; split.
  - intros x H0; elim H0.
  - split.
    + apply H.
    + intros n; apply H.
Qed.

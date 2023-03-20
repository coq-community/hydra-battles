
Require Import Arith Lia.
Require Import Ensembles.
Require Import Coq.Lists.List.

Require Import folProp.
Require Import subAll.
Require Import folLogic3.
Require Export Languages.
Require Export LNN.
From hydras Require Import Compat815.

Section NN.

Definition NN1 := (forallH 0 (Succ v_ 0 <> Zero))%fol. 

Definition NN2 := 
(forallH 1 (forallH 0 (Succ v_ 0 = Succ v_ 1 -> v_ 0 = v_ 1)))%fol.

Definition NN3 := forallH 0 (equal (Plus (var 0) Zero) (var 0)).

Definition NN4 :=
forallH 1 (forallH 0 (v_ 0 + S_ (v_ 1) = S_ (v_ 0 + v_ 1))%fol).

Definition NN5 := (forallH 0 (v_ 0 * Zero = Zero))%fol.

Definition NN6 :=
  (forallH 1 (forallH 0 (v_ 0 * Succ v_ 1 = v_ 0 * v_ 1 + v_ 0)))%fol.

Definition NN7 := forallH 0 (~ v_ 0 < Zero)%fol.

Definition NN8 :=
  (forallH 1
    (forallH 0 (v_ 0 < Succ v_ 1 -> v_ 0 < v_ 1 \/ v_ 0 = v_ 1)))%fol.

Definition NN9 :=  (forallH 1 (forallH 0 (v_ 0 < v_ 1 \/ v_ 0 = v_ 1 \/ v_ 1 < v_ 0)))%fol.

Definition NNStar :=
(forallH 1 (forallH 0
              (v_ 0 < v_ 1 \/ v_ 0 = v_ 1 -> v_ 0 < S_ (v_ 1))))%fol.

Definition NN :=
  Ensembles.Add _
    (Ensembles.Add _
       (Ensembles.Add _
          (Ensembles.Add _
             (Ensembles.Add _ 
                (Ensembles.Add _ 
                   (Ensembles.Add _ 
                      (Ensembles.Add _ (Singleton _ NN1) NN2) NN3) NN4) NN5)
             NN6) NN7) NN8) NN9.

Lemma closedNN1 : ClosedSystem LNN NN.
Proof.
  intros v f H; repeat induction H; cbn; auto.
Qed.

Lemma closedNN : forall v : nat, ~ In_freeVarSys LNN v NN.
Proof.
  unfold not in |- *; intros v [x H].
  destruct closedNN1 with v x; tauto.
Qed.

Lemma nn1 (a : Term) : SysPrf NN (notH (equal (Succ a) Zero)).
Proof.
  replace (notH (equal (Succ a) Zero)) with
    (substituteFormula LNN (notH (equal (Succ (var 0)) Zero)) 0 a).
  - apply forallE, Axm; repeat (try right; constructor) || left.
  - reflexivity.
Qed.

Lemma nn2 (a b : Term):
  SysPrf NN (impH (equal (Succ a) (Succ b)) (equal a b)).
Proof.
  set (m := fun x : nat => match x with
                           | O => a
                           | S _ => b
                           end) in *.
  replace (impH (equal (Succ a) (Succ b)) (equal a b)) with
    (subAllFormula LNN
       (impH (equal (Succ (var 0)) (Succ (var 1))) (equal (var 0) (var 1)))
       (fun x : nat =>
          match le_lt_dec 2 x with
          | left _ => var x
          | right _ => m x
          end)).
  - apply (subAllCloseFrom LNN).
    cbn; apply Axm; repeat (try right; constructor) || left.
  - cbn; destruct (le_lt_dec 2 0) as [? | l].
    + lia. 
    + destruct (le_lt_dec 2 1).
      * lia. 
      * reflexivity. 
Qed.

Lemma nn3 (a : Term): SysPrf NN (equal (Plus a Zero) a).
Proof.
  replace (equal (Plus a Zero) a) with
    (substituteFormula LNN (equal (Plus (var 0) Zero) (var 0)) 0 a).
  - apply forallE; apply Axm; repeat (try right; constructor) || left.
  - reflexivity.
Qed.

Lemma nn4 (a b : Term) :
 SysPrf NN (a + S_ b = S_ (a + b))%fol.
Proof.
  set (m := fun x : nat => match x with
                           | O => a
                           | S _ => b
                           end).
  replace  (a + S_ b = S_ (a + b))%fol
    with (subAllFormula LNN
            (v_ 0 + S_ (v_ 1) = S_ (v_ 0 + v_ 1))%fol
            (fun x : nat =>
               match le_lt_dec 2 x with
               | left _ => var x
               | right _ => m x
               end)).
  - apply (subAllCloseFrom LNN).
    cbn; apply Axm; repeat (try right; constructor) || left.
  - destruct  (le_lt_dec 2 0).
    + lia.
    + destruct (le_lt_dec 2 1).
      * lia. 
      * reflexivity. 
Qed.

Lemma nn5 ( a : Term) : SysPrf NN (equal (Times a Zero) Zero).
Proof.
  replace (equal (Times a Zero) Zero) with
    (substituteFormula LNN (equal (Times (var 0) Zero) Zero) 0 a).
  - apply forallE, Axm; repeat (try right; constructor) || left.
  - reflexivity.
Qed.

Lemma nn6 (a b : Term):
  SysPrf NN (equal (Times a (Succ b)) (Plus (Times a b) a)).
Proof.
  set (m := fun x : nat => match x with
                           | O => a
                           | S _ => b
                           end) in *.
  replace (equal (Times a (Succ b)) (Plus (Times a b) a)) with
    (subAllFormula LNN
       (equal (Times (var 0) (Succ (var 1)))
          (Plus (Times (var 0) (var 1)) (var 0)))
       (fun x : nat =>
          match le_lt_dec 2 x with
          | left _ => var x
          | right _ => m x
          end)).
  - apply (subAllCloseFrom LNN).
    cbn; apply Axm; repeat (try right; constructor) || left.
  - cbn; destruct (le_lt_dec 2 0).
    + lia.
    + induction (le_lt_dec 2 1); [lia | reflexivity].
Qed.

Lemma nn7 (a : Term): SysPrf NN (notH (LT a Zero)).
Proof.
  replace (notH (LT a Zero)) with
    (substituteFormula LNN (notH (LT (var 0) Zero)) 0 a).
  - apply forallE, Axm; repeat (try right; constructor) || left.
  - reflexivity.
Qed.

Lemma nn8 (a b : Term) :
 SysPrf NN (impH (LT a (Succ b)) (orH (LT a b) (equal a b))).
Proof.
  set (m := fun x : nat => match x with
                           | O => a
                           | S _ => b
                           end) in *.
  replace (impH (LT a (Succ b)) (orH (LT a b) (equal a b))) with
    (subAllFormula LNN
       (impH (LT (var 0) (Succ (var 1)))
          (orH (LT (var 0) (var 1)) (equal (var 0) (var 1))))
       (fun x : nat =>
          match le_lt_dec 2 x with
          | left _ => var x
          | right _ => m x
          end)).
  - apply (subAllCloseFrom LNN).
    cbn; apply Axm; repeat (try right; constructor) || left.
  - cbn; destruct (le_lt_dec 2 0).
    + lia.
    + induction (le_lt_dec 2 1); [lia | reflexivity]. 
Qed.

Lemma nn9 (a b : Term):
  SysPrf NN (orH (LT a b) (orH (equal a b) (LT b a))).
Proof.
  set (m := fun x : nat => match x with
                           | O => a
                           | S _ => b
                           end) in *.
  replace (a < b \/ a = b \/ b < a)%fol 
    with 
    (subAllFormula LNN
       (v_ 0 < v_ 1 \/ v_ 0 = v_ 1 \/ v_ 1 < v_ 0)%fol
       (fun x : nat =>
          match le_lt_dec 2 x with
          | left _ => var x
          | right _ => m x
          end)).
  - apply (subAllCloseFrom LNN); cbn;
      apply Axm; repeat (try right; constructor) || left.
  - cbn; destruct (le_lt_dec 2 0).
    + lia.
    + induction (le_lt_dec 2 1); [lia | reflexivity].
Qed.

End NN.

Locate Plus. 
Locate "_ + _".



(**  NN.v : Natural Numbers: Axioms and basic properties


Original version by Russel O'Connor

*)

From Coq Require Import Arith Lia  Ensembles List.

From hydras.Ackermann Require Import folProp subAll  folLogic3 Languages.
From hydras.Ackermann Require Export LNN.
From hydras Require Import Compat815 NewNotations.
Import NNnotations. 
(** * Axioms of [NN] *)
Section NN.

Definition NN1 := (allH 0, S_ v#0 <> Zero)%fol. 

Definition NN2 := (allH 1 0,  S_ v#0 = S_ v#1 -> v#0 = v#1)%fol.

Definition NN3 := (allH 0, v#0 + Zero = v#0)%fol.

Definition NN4 := (allH 1 0, v#0 + S_ v#1 = S_ (v#0 + v#1))%fol.

Definition NN5 := (allH 0, v#0 * Zero = Zero)%fol.

Definition NN6 := (allH 1 0, v#0 * S_ v#1 = v#0 * v#1 + v#0)%fol.

Definition NN7 := (allH 0, ~ v#0 < Zero)%fol.

Definition NN8 := 
 (allH 1 0, v#0 < Succ(v#1) -> v#0 < v#1 \/ v#0 = v#1)%fol.

Definition NN9 := (allH 1 0, v#0 < v#1 \/ v#0 = v#1 \/ v#1 < v#0)%fol.

Definition NN := SetEnum NN1 NN2 NN3 NN4 NN5 NN6 NN7 NN8 NN9.
 
(** * Properties of the system [NN] *)

Lemma closedNN1 : ClosedSystem LNN NN.
Proof.
  intros v f H; repeat induction H; cbn; auto.
Qed.

Lemma closedNN : forall v : nat, ~ In_freeVarSys LNN v NN.
Proof.
  unfold not in |- *; intros v [x H].
  destruct closedNN1 with v x; tauto.
Qed.

(** ** Generic instantiation of axioms *)

Lemma nn1 (a : Term) : SysPrf NN (S_ a <> Zero)%fol.
Proof.
  change (S_ a <> Zero)%fol with
    (substF  (S_ v#0 <> Zero)%fol 0 a).
  - apply forallE, Axm; repeat (try right; constructor) || left.
Qed.

Lemma nn2 (a b : Term):  SysPrf NN (S_ a = S_ b -> a = b)%fol. 
Proof.
  set (m := fun x : nat => match x with
                           | O => a
                           | S _ => b
                           end) in *.
  change (S_ a = S_ b -> a = b)%fol with
    (subAllFormula LNN
       (S_ v#0 = S_ v#1 -> v#0 = v#1)%fol
       (fun x : nat =>
          match le_lt_dec 2 x with
          | left _ => var x
          | right _ => m x
          end)).
  - apply (subAllCloseFrom LNN).
    cbn; apply Axm; repeat (try right; constructor) || left.
Qed.

Lemma nn3 (a : Term): SysPrf NN (a + Zero = a)%fol.
Proof.
  change  (a + Zero = a)%fol with
    (substF (v#0 + Zero = v#0)%fol 0 a).
  - apply forallE; apply Axm; repeat (try right; constructor) || left.
Qed.

Lemma nn4 (a b : Term) : SysPrf NN (a + S_ b = S_ (a + b))%fol.
Proof.
  set (m := fun x : nat => match x with
                           | O => a
                           | S _ => b
                           end).
  change (a + S_ b = S_ (a + b))%fol
    with (subAllFormula LNN
            (v#0 + Succ(v#1) = Succ(v#0 + v#1))%fol
            (fun x : nat =>
               match le_lt_dec 2 x with
               | left _ => var x
               | right _ => m x
               end)).
  - apply (subAllCloseFrom LNN).
    cbn; apply Axm; repeat (try right; constructor) || left.
Qed.

Lemma nn5 ( a : Term) : SysPrf NN (a * Zero = Zero)%fol.
Proof.
  change (a * Zero = Zero)%fol with
    (substF (v#0 * Zero = Zero)%fol 0 a).
  - apply forallE, Axm; repeat (try right; constructor) || left.
Qed.

Lemma nn6 (a b : Term):
  SysPrf NN (a * Succ b = a * b + a)%fol.
Proof.
  set (m := fun x : nat => match x with
                           | O => a
                           | S _ => b
                           end) in *.
  change (a * Succ b = a * b + a)%fol with 
    (subAllFormula LNN
       (v#0 * Succ( v#1) = v#0 * v#1 + v#0)%fol
       (fun x : nat =>
          match le_lt_dec 2 x with
          | left _ => var x
          | right _ => m x
          end)).

  - apply (subAllCloseFrom LNN).
    cbn; apply Axm; repeat (try right; constructor) || left.
Qed.

Lemma nn7 (a : Term): SysPrf NN (~ (a <Zero))%fol.
Proof.
  change (~ (a <Zero))%fol with
    (substF (~ v#0 < Zero)%fol 0 a).
  - apply forallE, Axm; repeat (try right; constructor) || left.
Qed.

Lemma nn8 (a b : Term) : SysPrf NN (a < Succ b -> a < b \/ a = b)%fol.
Proof.
  set (m := fun x : nat => match x with
                           | O => a
                           | S _ => b
                           end) in *.
  change (a < Succ b -> a < b \/ a = b)%fol with 
    (subAllFormula LNN (v#0 < Succ v#1 -> v#0 < v#1 \/ v#0 = v#1)%fol 
              (fun x : nat =>
          match le_lt_dec 2 x with
          | left _ => var x
          | right _ => m x
          end)).
  - apply (subAllCloseFrom LNN).
    cbn; apply Axm; repeat (try right; constructor) || left.
Qed.

Lemma nn9 (a b : Term):  SysPrf NN (a < b \/ a = b \/ b < a)%fol.
Proof.
  set (m := fun x : nat => match x with
                           | O => a
                           | S _ => b
                           end) in *.
  change (a < b \/ a = b \/ b < a)%fol 
    with 
    (subAllFormula LNN
       (v#0 < v#1 \/ v#0 = v#1 \/ v#1 < v#0)%fol
       (fun x : nat =>
          match le_lt_dec 2 x with
          | left _ => var x
          | right _ => m x
          end)).
  - apply (subAllCloseFrom LNN); cbn;
      apply Axm; repeat (try right; constructor) || left.
Qed.

End NN.


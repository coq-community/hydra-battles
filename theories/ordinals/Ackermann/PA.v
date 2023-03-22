From Coq Require Import Arith Lia.
From Coq Require Import Ensembles.

Require Import folProp.
Require Import subAll.
Require Import folLogic3.
Require Export Languages.
Require Export LNT.
(*

Require Import FOL_notations.

Section PA.

Definition PA1 := (forallH 0 (~ Succ (v_ 0) = Zero))%fol. 

Definition PA2 := (forallH 1 (forallH 0 (Succ (v_ 0) = Succ (v_ 1) -> v_ 0 = v_ 1)))%fol.


*)

Section PA.

Definition PA1 := (forallH 0 (Succ v_ 0 <> Zero))%fol.

Definition PA2 := (forallH 1 (forallH 0 (Succ v_ 0 = Succ v_ 1 -> v_ 0 = v_ 1)))%fol.

Print Plus.

Definition PA3 := forallH 0 (v_ 0 + Zero = v_ 0)%fol. 

Definition PA4 := (forallH 1 (forallH 0 (v_ 0 + Succ v_ 1 = Succ (v_ 0 + v_ 1))))%fol.

Definition PA5 := forallH 0 (v_ 0 * Zero = Zero)%fol. 

Definition PA6 := 
  (forallH 1 (forallH 0 (v_ 0 * Succ v_ 1 = v_ 0 * v_ 1 + v_ 0)))%fol.

Definition PA7 (f : Formula) (v : nat) : Formula :=
close LNT (substituteFormula LNT f v Zero -> 
           forallH v (f -> substituteFormula LNT f v (Succ v_ v)) -> forallH v f)%fol.


Definition InductionSchema (f : Formula) : Prop :=
  exists g : Formula, (exists v : nat, f = PA7 g v).

Definition PA :=
  Ensembles.Add _
    (Ensembles.Add _ 
       (Ensembles.Add _ 
          (Ensembles.Add _ 
             (Ensembles.Add _ 
                (Ensembles.Add _ InductionSchema PA1) PA2) PA3) PA4)
       PA5) PA6.

Definition open :=
  Formula_rec LNT (fun _ => Formula) (fun t t0 : Term => equal t t0)
    (fun (r : Relations LNT) 
         (ts : Terms (arityR LNT r)) =>  atomic r ts) 
    (fun (f : Formula) _ (f0 : Formula) _ => impH f f0)
    (fun (f : Formula) _ => notH f)
    (fun (n : nat) _ (recf : Formula) => recf).

Lemma PAdec : forall x : Formula, In _ PA x \/ ~ In _ PA x.
Proof.
  intros x.
  unfold PA in |- *.
  induction (formula_dec LNT LNT_dec x PA6).
  - rewrite a; left; right; constructor.
  - induction (formula_dec LNT LNT_dec x PA5).
    + rewrite a; left; left; right; constructor.
    + induction (formula_dec LNT LNT_dec x PA4).
      * rewrite a; left; do 2 left; right; constructor.
      * induction (formula_dec LNT LNT_dec x PA3).
        -- rewrite a; left; do 3 left; right; constructor.
        -- induction (formula_dec LNT LNT_dec x PA2).
           ++ rewrite a; left; do 4 left; right; constructor.
           ++ induction (formula_dec LNT LNT_dec x PA1).
              ** rewrite a; left; do 5 left; right; constructor.
              ** cut (In Formula InductionSchema x \/ 
                        ~ In Formula InductionSchema x).
                 { intros  [H| H].
                   - left; do 6 left; assumption.
                   - right; intro H0. 
                     repeat tauto || induction H0.
                 } 
                 clear b b0 b1 b2 b3 b4.
                 assert
                   (forall y : Formula,
                       (exists f : Formula,
                           (exists v : nat,
                               impH (substituteFormula LNT f v Zero)
                                 (impH
                                    (forallH v
                                       (impH f 
                                          (substituteFormula LNT f v
                                             (Succ (var v)))))
                                    (forallH v f)) = y)) \/
                         ~
                           (exists f : Formula,
                               (exists v : nat,
                                   impH (substituteFormula LNT f v Zero)
                                     (impH
                                        (forallH v 
                                           (impH f 
                                              (substituteFormula LNT f v 
                                                 (Succ (var v)))))
                                        (forallH v f)) = y))).
                 intros y;
                   destruct y as [t t0| r t| f f0| f| n f];
                   try (right; unfold not in |- *; 
                        intros; decompose record H; discriminate H1).
                 destruct f0 as [t t0| r t| f0 f1| f0| n f0];
                   try (right; unfold not in |- *; intros; 
                        decompose record H; discriminate H1).
                 destruct f0 as [t t0| r t| f0 f2| f0| n f0];
                   try (right; unfold not in |- *; intros; 
                        decompose record H; discriminate H1).
                 destruct f1 as [t t0| r t| f1 f2| f1| n0 f1];
                   try (right; unfold not in |- *; intros; 
                        decompose record H; discriminate H1).
               (*   do 4 fold impH  in |- *. *)
                 induction (formula_dec LNT LNT_dec
                              (substituteFormula LNT f1 n0 Zero) f).
                 rewrite <- a.
                 clear a f.
                 destruct f0 as [t t0| r t| f f0| f| n1 f];
                   try (right; unfold not in |- *; intros; 
                        decompose record H; discriminate H1).
                 induction (formula_dec LNT LNT_dec f1 f).
                 rewrite <- a.
                 clear a f.
                 induction
                   (formula_dec LNT LNT_dec
                      (substituteFormula LNT f1 n0 (Succ (var n0))) f0).
                 rewrite <- a.
                 clear a f0.
                 induction (eq_nat_dec n n0).
                 rewrite a.
                 left.
                 exists f1.
                 exists n0.
                 reflexivity.
                 right; unfold not in |- *; intros; 
                   apply b; decompose record H.
                 inversion H1.
                 auto.
                 right; unfold not in |- *; intros; apply b; 
                   decompose record H.
                 inversion H1.
                 reflexivity.
                 right; unfold not in |- *; intros; apply b; 
                   decompose record H.
                 inversion H1.
                 auto.
                 right; unfold not in |- *; intros; apply b; 
                   decompose record H.
                 inversion H1.
                 auto.
                 induction (formula_dec LNT LNT_dec x (close LNT (open x))).
                 induction (H (open x)).
                 left.
                 unfold In, InductionSchema, PA7 in |- *.
                 decompose record H0.
                 exists x0.
                 exists x1.
                 rewrite H2.
                 assumption.
                 right.
                 unfold not in |- *; intros; apply H0.
                 unfold In, InductionSchema, PA7 in H1.
                 decompose record H1.
                 exists x0.
                 exists x1.
                 rewrite H3.
                 unfold close in |- *.
                 induction
                   (List.nodup eq_nat_dec
                      (freeVarFormula LNT
                         (impH (substituteFormula LNT x0 x1 Zero)
                            (impH
                               (forallH x1
                                  (impH x0 (substituteFormula LNT x0 x1
                                              (Succ (var x1)))))
                               (forallH x1 x0))))).
                 simpl in |- *.
                 reflexivity.
                 simpl in |- *.
                 assumption.
                 right.
                 intros H0; apply b.
                 unfold In, InductionSchema, PA7 in H0.
                 decompose record H0.
                 rewrite H2.
                 replace
                   (open
                      (close LNT
                         (impH (substituteFormula LNT x0 x1 Zero)
                            (impH
                               (forallH x1
                                  (impH x0 (substituteFormula LNT x0 x1
                                              (Succ (var x1)))))
                               (forallH x1 x0))))) 
                   with
                   (impH (substituteFormula LNT x0 x1 Zero)
                      (impH
                         (forallH x1 (impH x0
                                        (substituteFormula LNT x0 x1
                                           (Succ (var x1)))))
                         (forallH x1 x0))).
                 reflexivity.
                 unfold close in |- *.
                 induction
                   (List.nodup eq_nat_dec
                      (freeVarFormula LNT
                         (impH (substituteFormula LNT x0 x1 Zero)
                            (impH
                               (forallH x1
                                  (impH x0 (substituteFormula LNT x0 x1 
                                              (Succ (var x1)))))
                               (forallH x1 x0))))).
                 simpl in |- *.
                 reflexivity.
                 simpl in |- *.
                 auto.
Qed.

Lemma closedPA1 : ClosedSystem LNT PA.
Proof.
  unfold ClosedSystem, PA in |- *.
  intros v f H.
  induction H as [x H| x H].
  - induction H as [x H| x H].
    + induction H as [x H| x H].
      * induction H as [x H| x H].
      -- induction H as [x H| x H].
         ++  induction H as [x H| x H].
             ** induction H as (x0, H).
                induction H as (x1, H).
                unfold PA7 in H.
                rewrite H.
                apply freeVarClosed.
             ** induction H; auto.
         ++ induction H; auto.
      -- induction H; auto.
      * induction H; auto.
    + induction H; auto.
- induction H; auto.
Qed.

Lemma closedPA : forall v : nat, ~ In_freeVarSys LNT v PA.
Proof.
 intros v H; unfold In_freeVarSys in H.
 destruct H as [x H]; elim closedPA1 with v x; tauto.
Qed.

Lemma pa1 : forall a : Term, SysPrf PA (notH (equal (Succ a) Zero)).
Proof.
  intros a;
    replace (notH (equal (Succ a) Zero)) with
    (substituteFormula LNT (notH (equal (Succ (var 0)) Zero)) 0 a).
  - apply forallE.
    apply Axm; repeat (try right; constructor) || left.
  - reflexivity.
Qed.

Lemma pa2 (a b : Term):
  SysPrf PA (impH (equal (Succ a) (Succ b)) (equal a b)).
Proof.
  set (m := fun x : nat => match x with
                           | O => a
                           | S _ => b
                           end) in *.
  replace (impH (equal (Succ a) (Succ b)) (equal a b)) with
    (subAllFormula LNT
       (impH (equal (Succ (var 0)) (Succ (var 1))) (equal (var 0) (var 1)))
       (fun x : nat =>
          match le_lt_dec 2 x with
          | left _ => var x
          | right _ => m x
          end)).
  - apply (subAllCloseFrom LNT).
    simpl; apply Axm; repeat (try right; constructor) || left.
  - simpl; induction (le_lt_dec 2 0). 
    + lia. 
    + induction (le_lt_dec 2 1).
      * lia.
      * reflexivity.
Qed.

Lemma pa3 (a : Term): SysPrf PA (equal (Plus a Zero) a).
Proof.
replace (equal (Plus a Zero) a) with
 (substituteFormula LNT (equal (Plus (var 0) Zero) (var 0)) 0 a).
- apply forallE; apply Axm; repeat (try right; constructor) || left.
- reflexivity.
Qed.

Lemma pa4 ( a b : Term) :
  SysPrf PA (equal (Plus a (Succ b)) (Succ (Plus a b))).
Proof.
  set (m := fun x : nat => match x with
                           | O => a
                           | S _ => b
                           end) in *.
  replace (equal (Plus a (Succ b)) (Succ (Plus a b))) with
    (subAllFormula LNT
       (equal (Plus (var 0) (Succ (var 1))) (Succ (Plus (var 0) (var 1))))
       (fun x : nat =>
          match le_lt_dec 2 x with
          | left _ => var x
          | right _ => m x
          end)).
  - apply (subAllCloseFrom LNT).
    simpl in |- *.
    apply Axm; repeat (try right; constructor) || left.
  - simpl in |- *.
    induction (le_lt_dec 2 0).
    + lia.
    + induction (le_lt_dec 2 1).
      * lia.
      * reflexivity.
Qed.

Lemma pa5 (a : Term): SysPrf PA (equal (Times a Zero) Zero).
Proof.
  replace (equal (Times a Zero) Zero) with
    (substituteFormula LNT (equal (Times (var 0) Zero) Zero) 0 a).
  - apply forallE.
    apply Axm; repeat (try right; constructor) || left.
  - reflexivity.
Qed.

Lemma pa6 (a b : Term) :
 SysPrf PA (equal (Times a (Succ b)) (Plus (Times a b) a)).
Proof.
  set (m := fun x : nat => match x with
                           | O => a
                           | S _ => b
                           end) in *.
  replace (equal (Times a (Succ b)) (Plus (Times a b) a)) with
    (subAllFormula LNT
       (equal (Times (var 0) (Succ (var 1)))
          (Plus (Times (var 0) (var 1)) (var 0)))
       (fun x : nat =>
          match le_lt_dec 2 x with
          | left _ => var x
          | right _ => m x
          end)).
  - apply (subAllCloseFrom LNT).
    simpl in |- *.
    apply Axm; repeat (try right; constructor) || left.
  - simpl in |- *.
    induction (le_lt_dec 2 0).
    + lia.
    + induction (le_lt_dec 2 1).
      * lia.
      * reflexivity.
Qed.

Lemma induct (f : Formula) (v : nat):
 SysPrf PA (substituteFormula LNT f v Zero) ->
 SysPrf PA (forallH v (impH f (substituteFormula LNT f v (Succ (var v)))))
 ->
 SysPrf PA (forallH v f).
Proof.
  intros H H0; eapply impE.
  - eapply impE.
    + apply (openClosed LNT).
      apply Axm; repeat left.
      unfold InductionSchema in |- *.
      unfold In in |- *.
      unfold PA7 in |- *.
      exists f, v; reflexivity.
    + apply H.
- apply H0.
Qed.

End PA.

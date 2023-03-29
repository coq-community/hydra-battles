
Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Arith.

Require Import folProp.
Require Import folProof.
Require Import subProp.
Require Import folLogic3.
Require Import folReplace.
Require Import NN.
Require Import PAtheory.
Require Export LNN2LNT.
Require Import subAll.
Require Import ListExt.

Lemma NN2PA (f : fol.Formula LNN):
  folProof.SysPrf LNN NN f -> SysPrf PA (LNN2LNT_formula f). 
Proof.
  intro H; apply translateProof with NN.
  - apply closedPA1.
  - intros f0 H0; unfold NN in H0.
    destruct H0 as [x H0| x H0].
    + destruct  H0 as [x H0| x H0].
      * destruct H0 as [x H0| x H0].
        -- destruct H0 as [x H0| x H0].
           ++ destruct H0 as [x H0| x H0].
              ** destruct H0 as [x H0| x H0].
                 destruct H0 as [x H0| x H0].
                 destruct H0 as [x H0| x H0].
                 destruct H0.
                 apply Axm; repeat (try right; constructor) || left.
                 destruct H0.
                 apply Axm; repeat (try right; constructor) || left.
                 destruct H0.
                 apply Axm; repeat (try right; constructor) || left.
                 destruct H0.
                 apply Axm; repeat (try right; constructor) || left.
              ** destruct H0.
                 apply Axm; repeat (try right; constructor) || left.
           ++ destruct H0.
              apply Axm; repeat (try right; constructor) || left.
        -- destruct H0.
           apply NN72PA.
      * destruct H0.
        apply NN82PA.
    + destruct H0.
      apply NN92PA.
  - apply H.
Qed.

Lemma PAboundedLT :
  forall (m : nat) (F : Formula) (x : nat),
    (forall n : nat,
        n < m -> SysPrf PA (substituteFormula LNT F x (natToTerm n))) ->
    SysPrf PA (LNN2LNT_formula ((v_ x)%nt < LNN.natToTerm m)%nn -> F)%nt.
Proof.
simple induction m. 
- intros F x H; apply impI.
  apply contradiction with 
    (LNN2LNT_formula (LNN.LT (var x) (LNN.natToTerm 0))).
  apply Axm; right; constructor.
  apply sysWeaken.
  replace (notH (LNN2LNT_formula (LNN.LT (var x) (LNN.natToTerm 0)))) 
    with
    (LNN2LNT_formula (notH  (LNN.LT (var x) (LNN.natToTerm 0)))).
  + apply NN2PA.
    apply nn7.
  + reflexivity.
- intros n H a x H0; apply impI.
  eapply orE.
  + apply impE with 
      (LNN2LNT_formula (LNN.LT (var x) (LNN.natToTerm (S n)))).
    * apply sysWeaken.
      assert (H1: SysPrf PA (LNN2LNT_formula
                     ((v_ x < S_ (LNN.natToTerm n))%nn ->
                      (v_ x < LNN.natToTerm n)%nn \/ 
                        v_ x = LNN.natToTerm n)%nt)%nt)
      by (apply NN2PA, nn8). 
      simpl in H1; simpl. 
      unfold orH; apply H1.
    * apply Axm; right; constructor.
  + apply sysWeaken.
    simpl in H; apply H; auto. 
  + apply sysWeaken, impI.
    rewrite <- (subFormulaId LNT a x).
    rewrite LNN2LNT_natToTerm.
    apply impE with (substituteFormula LNT a x (natToTerm n)).
    * apply (subWithEquals LNT).
      apply eqSym.
      apply Axm; right; constructor.
    * apply sysWeaken.
      apply H0.
      apply Nat.lt_succ_diag_r .
Qed.

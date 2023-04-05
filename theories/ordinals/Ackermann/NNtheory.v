From Coq Require Import Arith Lia.

Require Import folLogic3.
Require Import folProp.
Require Import subProp.
Require Export NN.
From hydras Require Import Compat815.

Lemma natNE (a b : nat) :
  a <> b -> SysPrf NN (notH (equal (natToTerm a) (natToTerm b))).
Proof. 
  revert a b; 
    assert (* wlog ? *)
      (H: forall a b : nat,
          a < b -> SysPrf NN (notH (equal (natToTerm a) (natToTerm b)))).
  { induction a as [| a Hreca]; intros.
    - destruct b as [| n].
      + elim (Nat.nlt_0_r _ H).
      + cbn; apply impE with (notH (equal (Succ (natToTerm n)) Zero)).
        * apply cp2, impI, eqSym.
          apply Axm; right; constructor.
        * apply nn1.
    - destruct b as [| n].
      + elim (Nat.nlt_0_r _ H).
      + cbn; apply impE with (notH (equal (natToTerm a) (natToTerm n))).
        * apply cp2, nn2.
        * apply Hreca; lia. 
  }
 intros a b H0; 
   destruct (Nat.lt_gt_cases a b) as [H1 _]; specialize (H1 H0);
          destruct H1 as [H1 | H1]. 
  - now apply H.
  - apply impE with (notH (equal (natToTerm b) (natToTerm a))).
    + apply cp2, impI, eqSym.
      apply Axm; right; constructor.
    + now apply H.
Qed.
       
Lemma natLE (a b : nat):
 b <= a -> SysPrf NN (notH (LT (natToTerm a) (natToTerm b))).
Proof.
  intros H; induction b as [| b Hrecb].
  - apply nn7.
  - cbn; apply impE with
      (notH
         (orH (LT (natToTerm a) (natToTerm b))
            (equal (natToTerm a) (natToTerm b)))).
  + apply cp2, nn8.
  + apply nOr, andI.
    * apply Hrecb; lia. 
    * apply natNE.
      intro H0; lia.
Qed.

Lemma natLT (a b : nat):
  a < b -> SysPrf NN (natToTerm a < natToTerm b)%nn.
Proof.
  intros H; eapply orE.
  - apply nn9 with (a := natToTerm b) (b := natToTerm a).
  - apply impI; apply contradiction with (LT (natToTerm b) (natToTerm a)).
    + apply Axm; right; constructor.
    + now apply sysWeaken, natLE, Nat.lt_le_incl.
  - apply impI, orSys.
    + apply contradiction with (natToTerm b = natToTerm a)%nn.
      * apply Axm; right; constructor.
      * apply sysWeaken, natNE.
        unfold not in |- *; intros.
        subst; lia.
    + apply Axm; right; constructor.
Qed.

Lemma natPlus (a b : nat):
 SysPrf NN (equal (Plus (natToTerm a) (natToTerm b)) (natToTerm (a + b))).
Proof.
  induction b as [| b Hrecb].
  - rewrite Nat.add_comm; cbn; apply nn3. 
  - rewrite Nat.add_comm; cbn. 
    apply eqTrans with (Succ (Plus (natToTerm a) (natToTerm b))).
    + apply nn4.
    + apply eqSucc.
      rewrite Nat.add_comm; apply Hrecb.
Qed.

Lemma natTimes (a b : nat):
 SysPrf NN (equal (Times (natToTerm a) (natToTerm b)) (natToTerm (a * b))).
Proof.
  - induction b as [| b Hrecb].
    + rewrite Nat.mul_comm; cbn; apply nn5.
    + rewrite Nat.mul_comm; cbn; eapply eqTrans.
      * apply nn6.
      * rewrite Nat.add_comm;
          apply eqTrans with (Plus (natToTerm (b * a)) (natToTerm a)).
        -- apply eqPlus.
           ++ rewrite Nat.mul_comm; apply Hrecb.
           ++ apply eqRefl.
        -- apply natPlus.
Qed.

Lemma boundedLT  (m : nat) (a : Formula) (x : nat):
 (forall n : nat,
  n < m -> SysPrf NN (substituteFormula LNN a x (natToTerm n))) ->
 SysPrf NN (impH (LT (var x) (natToTerm m)) a).
Proof.
  revert m a x; simple induction m; intros.
  apply impI.
  apply contradiction with (LT (var x) (natToTerm 0)).
  - apply Axm; right; constructor.
  - apply sysWeaken, nn7.
  - apply impI; eapply orE.
    + apply impE with (LT (var x) (natToTerm (S n))).
      * apply sysWeaken; cbn; apply nn8.
      * apply Axm; right; constructor.
    + apply sysWeaken, H.
      intros n0 H1; apply H0.
      apply Nat.lt_lt_succ_r; auto.
    + apply sysWeaken, impI.
      rewrite <- (subFormulaId LNN a x).
      apply impE with (substituteFormula LNN a x (natToTerm n)).
      * apply (subWithEquals LNN).
        apply eqSym.
        apply Axm; right; constructor.
      * apply sysWeaken, H0.
        apply Nat.lt_succ_diag_r .
Qed.

Lemma nnPlusNotNeeded (n:nat) :
 SysPrf NN
   (impH (orH (LT (var 1) (natToTerm n)) (equal (var 1) (natToTerm n)))
      (LT (var 1) (Succ (natToTerm n)))).
Proof.
  induction n as [| n Hrecn].
  - cbn; apply impI, orSys. 
    + apply contradiction with (LT (var 1) Zero).
      * apply Axm; right; constructor.
      * apply sysWeaken, nn7. 
    + rewrite <- (subFormulaId LNN (LT (var 1) (Succ Zero)) 1).
      apply impE with 
        (substituteFormula LNN (LT (var 1) (Succ Zero)) 1 Zero).
      * apply (subWithEquals LNN).
        apply eqSym.
        apply Axm; right; constructor.
      * apply sysWeaken;
          replace (substituteFormula LNN (v_ 1 < Succ Zero)%nn 1 Zero) 
          with
          (natToTerm 0 < natToTerm 1)%nn.
      -- apply natLT; auto.
      -- unfold LT; now rewrite (subFormulaRelation LNN).
  - cbn; apply impI, orSys.
    + apply impE with 
        (orH (LT (var 1) (natToTerm n)) (equal (var 1) (natToTerm n))).
      * apply sysWeaken;
          apply impTrans with (LT (var 1) (natToTerm (S n))).
        -- apply Hrecn.
        -- apply boundedLT.
           intros n0 H. 
           replace
             (substituteFormula LNN (LT (var 1) 
                                       (Succ (Succ (natToTerm n)))) 
                1 (natToTerm n0)) 
             with (LT (natToTerm n0) (natToTerm (S (S n)))).
           { apply natLT; now apply Nat.lt_lt_succ_r. }
           unfold LT; rewrite (subFormulaRelation LNN).
           cbn; rewrite (subTermNil LNN).
           ++ reflexivity.
           ++ apply closedNatToTerm.
      * apply impE with (LT (var 1) (Succ (natToTerm n))).
        -- apply sysWeaken, nn8.
        -- apply Axm; right; constructor.
    + rewrite <- (subFormulaId LNN (LT (var 1) 
                                      (Succ (Succ (natToTerm n)))) 1).
      apply impE with
        (substituteFormula LNN (LT (var 1) (Succ (Succ (natToTerm n)))) 1
           (Succ (natToTerm n))).
      * apply (subWithEquals LNN), eqSym, Axm; right; constructor. 
      * apply sysWeaken.
        replace
          (substituteFormula LNN 
             (LT (var 1) (Succ (Succ (natToTerm n)))) 1
             (Succ (natToTerm n))) 
          with (LT (natToTerm (S n)) (natToTerm (S (S n)))).
        { apply natLT, Nat.lt_succ_diag_r. }
        unfold LT; rewrite (subFormulaRelation LNN); cbn. 
        rewrite (subTermNil LNN).
        -- reflexivity.
        -- apply closedNatToTerm.
Qed.

From Coq Require Import Arith Lia.

From hydras.Ackermann Require Import folLogic3 folProp subProp.
From hydras.Ackermann Require Import folLogic3 folProp subProp. 
From hydras.Ackermann Require Export NN.
From hydras Require Import Compat815.
Import NNnotations. 

Lemma natNE (a b : nat) :
  a <> b -> SysPrf NN (natToTerm a <> natToTerm b)%fol.
Proof. 
  revert a b; 
    assert (* wlog ? *)
      (H: forall a b : nat,
          a < b -> SysPrf NN (natToTerm a <> natToTerm b)%fol).
  { induction a as [| a Hreca]; intros.
    - destruct b as [| n].
      + elim (Nat.nlt_0_r _ H).
      + cbn; apply impE with (Succ (natToTerm n) <> Zero)%fol.
        * apply cp2, impI, eqSym.
          apply Axm; right; constructor.
        * apply nn1.
    - destruct b as [| n].
      + elim (Nat.nlt_0_r _ H).
      + cbn; apply impE with (natToTerm a <> natToTerm n)%fol.
        * apply cp2, nn2.
        * apply Hreca; lia. 
  }
 intros a b H0; 
   destruct (Nat.lt_gt_cases a b) as [H1 _]; specialize (H1 H0);
          destruct H1 as [H1 | H1]. 
  - now apply H.
  - apply impE with (natToTerm b <> natToTerm a)%fol.
    + apply cp2, impI, eqSym.
      apply Axm; right; constructor.
    + now apply H.
Qed.
       
Lemma natLE (a b : nat):
 b <= a -> SysPrf NN (~ (natToTerm a < natToTerm b))%fol.
Proof.
  intros H; induction b as [| b Hrecb].
  - apply nn7.
  - cbn; apply impE with
      (~ (natToTerm a < natToTerm b \/ natToTerm a = natToTerm b))%fol.
  + apply cp2, nn8.
  + apply nOr, andI.
    * apply Hrecb; lia. 
    * apply natNE.
      intro H0; lia.
Qed.

Lemma natLT (a b : nat):
  a < b -> SysPrf NN (natToTerm a < natToTerm b)%fol.
Proof.
  intros H; eapply orE.
  - apply nn9 with (a := natToTerm b) (b := natToTerm a).
  - apply impI; apply contradiction with (natToTerm b < natToTerm a)%fol.
    + apply Axm; right; constructor.
    + now apply sysWeaken, natLE, Nat.lt_le_incl.
  - apply impI, orSys.
    + apply contradiction with (natToTerm b = natToTerm a)%fol.
      * apply Axm; right; constructor.
      * apply sysWeaken, natNE.
        unfold not in |- *; intros.
        subst; lia.
    + apply Axm; right; constructor.
Qed.

Lemma natPlus (a b : nat):
 SysPrf NN (natToTerm a + natToTerm b = natToTerm (a + b)%nat)%fol.
Proof.
  induction b as [| b Hrecb].
  - rewrite Nat.add_comm; cbn; apply nn3. 
  - rewrite Nat.add_comm; cbn. 
    apply eqTrans with (Succ (natToTerm a + natToTerm b))%fol.
    + apply nn4.
    + apply eqSucc.
      rewrite Nat.add_comm; apply Hrecb.
Qed.

Lemma natTimes (a b : nat):
 SysPrf NN (natToTerm a *natToTerm b = natToTerm (a * b)%nat)%fol.
Proof.
  - induction b as [| b Hrecb].
    + rewrite Nat.mul_comm; cbn; apply nn5.
    + rewrite Nat.mul_comm; cbn; eapply eqTrans.
      * apply nn6.
      * rewrite Nat.add_comm;
          apply eqTrans with (natToTerm (b * a)%nat + natToTerm a)%fol.
        -- apply eqPlus.
           ++ rewrite Nat.mul_comm; apply Hrecb.
           ++ apply eqRefl.
        -- apply natPlus.
Qed.

Lemma boundedLT  (m : nat) (a : Formula) (x : nat):
  (forall n : nat,
      n < m -> SysPrf NN (substF a x (natToTerm n))) ->
  SysPrf NN (v#x < natToTerm m -> a)%fol.
Proof.
  revert m a x; simple induction m; intros.
  apply impI.
  apply contradiction with (v# x < natToTerm 0)%fol.
  - apply Axm; right; constructor.
  - apply sysWeaken, nn7.
  - apply impI; eapply orE.
    + apply impE with (v#x < natToTerm (S n))%fol.
      * apply sysWeaken; cbn; apply nn8.
      * apply Axm; right; constructor.
    + apply sysWeaken, H.
      intros n0 H1; apply H0.
      apply Nat.lt_lt_succ_r; auto.
    + apply sysWeaken, impI.
      rewrite <- (subFormulaId LNN a x).
      apply impE with (substF a x (natToTerm n)).
      * apply (subWithEquals LNN).
        apply eqSym.
        apply Axm; right; constructor.
      * apply sysWeaken, H0.
        apply Nat.lt_succ_diag_r .
Qed.

Lemma nnPlusNotNeeded (n:nat) :
 SysPrf NN
 (v#1 < natToTerm n \/ v#1 = natToTerm n ->
  v#1 < S_ (natToTerm n))%fol.
 Proof.
  induction n as [| n Hrecn].
  - cbn; apply impI, orSys. 
    + apply contradiction with (v#1 < Zero)%fol.
      * apply Axm; right; constructor.
      * apply sysWeaken, nn7. 
    + rewrite <- (subFormulaId LNN (v#1 < S_ Zero)%fol 1).
      apply impE with 
        (substF (v#1 < S_ Zero)%fol 1 Zero).
      * apply (subWithEquals LNN).
        apply eqSym.
        apply Axm; right; constructor.
      * apply sysWeaken;
          replace (substF (v#1 < S_ Zero)%fol 1 Zero) 
          with
          (natToTerm 0 < natToTerm 1)%fol.
      -- apply natLT; auto.
      -- unfold LT; now rewrite (subFormulaRelation LNN).
  - cbn; apply impI, orSys.
    + apply impE with 
        (v#1 < natToTerm n \/ v#1 = natToTerm n)%fol.
      * apply sysWeaken;
          apply impTrans with (v#1 < natToTerm (S n))%fol.
        -- apply Hrecn.
        -- apply boundedLT.
           intros n0 H. unfold Succ.
           replace
             (substF (v#1 < (S_ (S_ (natToTerm n))))%fol
                1 (natToTerm n0)) 
             with (natToTerm n0 < natToTerm (S (S n)))%fol.
           {  apply natLT. now apply Nat.lt_lt_succ_r. }
           unfold LT; rewrite (subFormulaRelation LNN).
           cbn; rewrite (subTermNil LNN).
           ++ reflexivity.
           ++ apply closedNatToTerm.
      * apply impE with (v#1 < S_ (natToTerm n))%fol.
        -- apply sysWeaken, nn8.
        -- apply Axm; right; constructor.
    + unfold Succ; rewrite <- 
        (subFormulaId LNN 
           (v#1 <  (S_ (S_ (natToTerm n))))%fol 1).
      apply impE with
        (substF (v#1 < S_ (S_ (natToTerm n)))%fol 1
           (S_ (natToTerm n))).
      * apply (subWithEquals LNN), eqSym, Axm; right; constructor. 
      * apply sysWeaken.
        replace
          (substF 
             (v# 1 < S_ (S_ (natToTerm n)))%fol 1
             (S_ (natToTerm n))) 
          with (natToTerm (S n) <  natToTerm (S (S n)))%fol.
        { apply natLT, Nat.lt_succ_diag_r. }
        unfold LT; rewrite (subFormulaRelation LNN); cbn. 
        rewrite (subTermNil LNN).
        -- reflexivity.
        -- apply closedNatToTerm.
Qed.

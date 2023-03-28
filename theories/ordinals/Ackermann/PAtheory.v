Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Arith Lia.

Require Import subAll.
Require Import folReplace.
Require Import folProp.
Require Import folLogic3.
Require Import NN.
Require Import LNN2LNT.
Require Export PA.
Require Import NewNotations.

#[local] Arguments apply _ _ _ : clear implicits.

Lemma paZeroOrSucc (t : Term):
 SysPrf PA
 (t = Zero \/
     exH (newVar (0 :: freeVarTerm LNT t)),
       (t = Succ (v_ (newVar (0 :: freeVarTerm LNT t)))))%nt.
  Proof.
    set (nv := newVar (0 :: freeVarTerm LNT t)) in *.
  apply impE with
    (substituteFormula LNT
       (v_ 0 = Zero \/ exH nv, v_ 0 = Succ v_ nv)%nt
       0 t).
  - rewrite (subFormulaOr LNT), (subFormulaEqual LNT); simpl.
    apply iffE1, (reduceOr LNT).
    + apply iffRefl.
    + rewrite (subFormulaExist LNT).
      destruct (eq_nat_dec nv 0) as [a | b].
      * elim (newVar1 (0 :: freeVarTerm LNT t)).
        fold nv in |- *.
        rewrite a; simpl; auto.
      * destruct (In_dec eq_nat_dec nv (freeVarTerm LNT t)) 
          as [a | b0].
        -- elim (newVar1 (0 :: freeVarTerm LNT t)).
           fold nv in |- *; simpl in |- *; auto.
        -- rewrite (subFormulaEqual LNT).
           Opaque eq_nat_dec.
           simpl in |- *.
           Transparent eq_nat_dec.
           destruct (eq_nat_dec 0 nv) as [e | n ].
           ++ elim b; auto.
           ++ apply iffRefl.
  - apply forallE, induct.
    + rewrite (subFormulaOr LNT); apply orI1.
      rewrite (subFormulaEqual LNT); simpl; apply eqRefl.
    + apply forallI.
      * apply closedPA.
      * apply impI; rewrite (subFormulaOr LNT); apply orI2.
        rewrite (subFormulaExist LNT).
        induction (eq_nat_dec nv 0).
  -- elim (newVar1 (0 :: freeVarTerm LNT t)).
     fold nv; simpl; auto.
  -- induction (In_dec eq_nat_dec nv (freeVarTerm LNT (Succ (v_ 0))%nt)) 
       as [a | b0].
     ++ elim (newVar1 (0 :: freeVarTerm LNT t)).
        fold nv in |- *.
        simpl in a.
        induction a as [H| H].
        ** simpl in |- *.
           auto.
        ** elim H.
       ++ rewrite (subFormulaEqual LNT).
          Opaque eq_nat_dec.
          simpl in |- *.
          Transparent eq_nat_dec.
          induction
            (nat_rec (fun n : nat => {0 = n} + {0 <> n})
               (left (0 <> 0) (refl_equal 0))
               (fun (m : nat) (_ : {0 = m} + {0 <> m}) => 
                  right (0 = S m) (O_S m)) nv) as [a | b1].
          ** elim b; auto.
          ** fold (Succ (var nv)).
             apply sysWeaken;  apply existI with (var 0).
             rewrite (subFormulaEqual LNT).
             simpl in |- *.
             destruct (eq_nat_dec nv 0) as [e | n].
             { elim b1; auto. }
             change match nv as n return ({0 = n} + {0 <> n}) with
                  | 0 => left (0 <> 0) (refl_equal 0)
                  | S m => right (0 = S m) (O_S m)
                  end
               with (eq_nat_dec 0 nv).
             destruct (eq_nat_dec 0 nv) as [e | n0].
             { now elim b1. }
             simpl; destruct (eq_nat_dec nv nv) as [? | n1].
             { apply eqRefl. }
             now destruct n1.
Qed.

Lemma paPlusSym : forall a b : Term, 
    SysPrf PA (a + b = b + a)%nt. 
Proof.
  assert
    (H: SysPrf PA (allH 1 0, v_ 0 + v_ 1 = v_ 1 + v_ 0)%nt).
  { apply induct.
    - rewrite (subFormulaForall LNT).
      induction (eq_nat_dec 0 1) as [a | b].
      + discriminate a.
      + induction (In_dec eq_nat_dec 0 (freeVarTerm LNT Zero)) as [a | b0].
        * elim a.
        * apply induct.
          -- repeat rewrite (subFormulaEqual LNT).
             simpl in |- *; apply eqRefl.
          -- apply forallI.
             ++ apply closedPA.
             ++ repeat rewrite (subFormulaEqual LNT).
                simpl; apply impI.
                apply eqTrans with (Succ (v_ 0))%nt.
                ** apply sysWeaken.
                   apply pa3 with (a := (Succ (var 0))%nt).
                ** apply eqTrans with (Succ (Zero + v_ 0))%nt.
                   { apply eqSucc.
                     apply eqTrans with (v_ 0 + Zero)%nt.
                     - apply sysWeaken.
                       apply eqSym.
                       apply pa3.
                     - apply Axm; right; constructor.
                   } 
                   apply eqSym.
                   apply sysWeaken.
                   apply pa4 with (a := Zero%nt) (b := (v_ 0)%nt).
    - apply forallI.
      + apply closedPA.
      + apply impI.
        rewrite (subFormulaForall LNT).
        induction (eq_nat_dec 0 1) as [a | b].
        * discriminate a.
        * induction (In_dec eq_nat_dec 0 (freeVarTerm LNT (Succ (v_ 1))%nt)).

          -- simpl in a.
             induction a as [H| H].
             ++ discriminate.
             ++ contradiction.
          -- rewrite (subFormulaEqual LNT).
             simpl; apply forallI.
             ++ intros [x [H H0]].
                destruct H0 as [x H0| x H0].
                ** elim closedPA with 0.
                   exists x; auto.
                ** induction H0; simpl in H.
                   decompose sum H.
                   discriminate H0.
                   discriminate H1.
             ++ apply eqTrans with (Succ (v_ 0 + v_ 1))%nt.
                ** apply sysWeaken.
                   apply pa4 with (a := var 0) (b := var 1).
                ** apply eqTrans with (Succ (v_ 1 + v_ 0))%nt.
                   { apply eqSucc.
                     apply forallSimp with 0.
                     apply Axm; right; constructor.
                   } 
                   apply sysWeaken.
                   apply forallSimp with 0.
                   apply induct.
                   rewrite (subFormulaEqual LNT).
                   simpl in |- *.
                   apply eqTrans with (Succ (v_ 1))%nt.
                   { 
                     fold
                       (Succ (v_ 1 + Zero))%nt.
                     apply eqSucc.
                     apply pa3 with (a := (v_ 1)%nt).
                   }
                   apply eqSym.
                   apply pa3 with (a := (Succ v_ 1)%nt).
                   apply forallI.
                   apply closedPA.
                   apply impI.
                   rewrite (subFormulaEqual LNT).
                   simpl in |- *.
                   apply eqTrans with  (Succ (Succ v_ 1 + v_ 0))%nt.
                   {
                     fold (Succ (v_ 1 + Succ v_ 0))%nt.
                     apply eqSucc.
                     apply eqTrans with (Succ (v_ 1 + v_ 0))%nt. 
                     apply sysWeaken.
                     apply pa4 with (a := (v_  1)%nt) (b := (v_ 0)%nt).
                     apply Axm; right; constructor.
                   } 
                   apply sysWeaken.
                   apply eqSym.
                   apply pa4 with (a := Succ (v_ 1)%nt) (b := (v_ 0)%nt).
  } 
  intros a b;
  set (m := fun x : nat => match x with
                         | O => a
                         | S _ => b
                         end) in *.
  replace (a + b = b + a)%nt with
    (subAllFormula LNT (v_ 0 + v_ 1 = v_ 1 + v_ 0)%nt
       (fun x : nat =>
          match le_lt_dec 2 x with
          | left _ => var x
          | right _ => m x
          end)).
  + apply (subAllCloseFrom LNT).
    simpl; apply H.
  + simpl; destruct (le_lt_dec 2 0).
    * lia. 
    * induction (le_lt_dec 2 1).
      -- lia. 
      -- reflexivity.
Qed.

Lemma NN72PA : SysPrf PA (LNN2LNT_formula NN7).
Proof.
  simpl; apply forallI.
  - apply closedPA.
  - rewrite translateLT1.
    set (nv := newVar (0 :: 2 :: 1 :: 0 :: nil)) in *.
     fold Zero%nt; fold (Succ (v_ nv))%nt; fold (v_ 0 +  (Succ v_ nv))%nt.
    apply nnI, forallI.
    + apply closedPA.
    + apply impE with (Succ (v_ 0 + v_ nv) <> Zero)%nt.
      * apply cp2, impI; apply eqTrans with (v_ 0 + Succ (v_ nv))%nt.
        -- apply sysWeaken, eqSym, pa4.
        -- apply Axm; right; constructor.
      * apply pa1.
Qed.

Lemma NN82PA : SysPrf PA (LNN2LNT_formula NN8).
Proof.
  replace (LNN2LNT_formula NN8) with
    (allH 1 0,
      translateLT (Tcons v_ 0 (Tcons (S_ v_ 1) Tnil)) ->
      translateLT (Tcons v_ 0 (Tcons v_ 1 Tnil)) \/ v_ 0 = v_ 1)%nt; simpl. 
  
  - repeat rewrite translateLT1; simpl.
    unfold newVar; simpl; fold (Succ (v_ 3))%nt.
    fold (Succ (v_ 1))%nt; fold (v_ 0 + Succ v_ 3)%nt.
    fold (exH 3, v_ 0 + Succ v_ 3 = Succ v_ 1)%nt.  
    fold (exH 3, v_ 0 + Succ  v_ 3 = v_ 1)%nt.
    apply forallI.
    + apply closedPA.
    + apply forallI.
     * apply closedPA.
     * apply impI.
       apply existSys.
       -- apply closedPA.
       -- simpl; intro H. 
          repeat (elim H; clear H; [ discriminate | intros ]); auto.
       -- eapply orE.
          ++ apply sysWeaken.
             apply paZeroOrSucc.
          ++ apply impI; apply orI2.
             apply impE with (Succ v_ 0 = Succ v_ 1)%nt.
             ** repeat simple apply sysWeaken.
                apply pa2.
             ** apply eqTrans with (v_ 0 + Succ v_ 3)%nt.
                apply eqTrans with (Succ (v_ 0 + v_ 3))%nt.
                apply eqSucc.
                apply eqTrans with (v_ 0 + Zero)%nt.
                apply eqSym.
                repeat simple apply sysWeaken.
                apply pa3.
                apply eqPlus.
                apply eqRefl.
                apply eqSym.
                apply Axm; right; constructor.
                apply eqSym.
                repeat simple apply sysWeaken.
                apply pa4.
                apply Axm; left; right; constructor.
          ++ unfold newVar in |- *; simpl; apply impI.
             apply existSys.
             intros (x, H); induction H as (H, H0).
             induction H0 as [x H0| x H0].
             elim closedPA with 4.
             exists x.
             auto.
             induction H0.
             simpl in H.
             repeat (elim H; clear H; [ discriminate | intros ]); auto.
             intros H; simpl in H.
             repeat (elim H; clear H; [ discriminate | intros ]); auto.
             apply orI1.
             apply existI with (var 4).
             rewrite (subFormulaEqual LNT).
             simpl; apply impE with 
               (Succ (v_ 0 + Succ v_ 4) = Succ v_ 1)%nt.
             repeat simple apply sysWeaken.
             apply pa2.
             apply eqTrans with (v_ 0 + Succ v_ 3)%nt.
             apply eqTrans with (v_ 0 + Succ (Succ  v_ 4))%nt.
             repeat simple apply sysWeaken.
             apply eqSym.
             apply pa4.
             apply eqPlus.
             apply eqRefl.
             apply eqSucc.
             apply eqSym.
             apply Axm; right; constructor.
             apply Axm; left; right; constructor.
  - reflexivity.
Qed.

Lemma NN92PA : SysPrf PA (LNN2LNT_formula NN9).
Proof.
  replace (LNN2LNT_formula NN9) with
(allH 1 0,
     LNN2LNT_formula ((v_ 0)%nt < (v_ 1)%nt)%nn \/
     v_ 0 = v_ 1 \/ LNN2LNT_formula (v_ 1 < v_ 0)%nn)%nt;
    [ idtac | reflexivity ].
  simpl in |- *.
  repeat rewrite translateLT1.
  simpl in |- *.
  unfold newVar in |- *.
  simpl in |- *.
  fold (Succ v_ 3)%nt in |- *.
  fold (v_ 0 + Succ v_ 3)%nt.
  fold (v_ 1 + Succ v_ 3)%nt.
  fold (exH 3, v_ 0 + Succ v_ 3 = v_ 1)%nt.
  fold (exH 3, v_ 1 + Succ v_ 3 = v_ 0)%nt.
    apply induct.
  - rewrite (subFormulaForall LNT).
    induction (eq_nat_dec 0 1).
    + discriminate a.
    + induction (In_dec eq_nat_dec 0 (freeVarTerm LNT Zero)).
      * simpl in a.
        elim a.
      * rewrite (subFormulaOr LNT).
        apply forallI.
        apply closedPA.
        apply orI2.
        rewrite (subFormulaOr LNT).
        rewrite (subFormulaEqual LNT).
        simpl in |- *.
        eapply orE.
        -- apply paZeroOrSucc with (t := (v_ 0)%nt).
        -- apply impI.
           apply orI1.
           apply Axm; right; constructor.
        -- apply impI.
           apply orI2.
           unfold newVar in |- *.
           simpl in |- *.
           rewrite (subFormulaExist LNT).
           induction (eq_nat_dec 3 1).
           ++ discriminate a.
           ++ induction (In_dec eq_nat_dec 3 (freeVarTerm LNT Zero)).
              ** elim a.
              ** apply impE with (exH 3, v_ 0 = Succ v_ 3)%nt.
                 { apply sysWeaken.
                   apply impI.
                   apply existSys.
                   - apply closedPA.
                   - unfold not in |- *; intros.
                     simpl in H.
                     induction H as [H| H].
                     + discriminate H.
                     + contradiction.
                   - apply existI with (v_ 3)%nt.
                     repeat rewrite (subFormulaEqual LNT).
                     simpl in |- *.
                     apply eqTrans with (Succ v_ 3)%nt.
                     + apply sysWeaken.
                       apply eqTrans with (Succ v_ 3 + Zero)%nt.
                       * apply paPlusSym with (a := Zero) (b := (Succ v_ 3)%nt).
                       * apply pa3.
                     + apply eqSym.
                       apply Axm; right; constructor.
                 } 
                 apply impE with (exH 1, v_ 0 = Succ v_ 1)%nt.
                 {
                   replace (v_ 0 = Succ v_ 3)%nt with
                     (substF LNT (v_ 0 = Succ v_ 1)%nt 1 (v_ 3)%nt).
                   - apply iffE1.
                     apply (rebindExist LNT).
                     simpl in |- *.
                     unfold not in |- *; intros.
                     induction H as [H| H].
                     + discriminate H.
                     + contradiction.
                   - rewrite (subFormulaEqual LNT).
                     reflexivity.
                 } 
                 apply Axm; right; constructor.
  - apply forallI.
    + apply closedPA.
    + apply impI.
      rewrite (subFormulaForall LNT).
      induction (eq_nat_dec 0 1).
      * discriminate a.
      * induction (In_dec eq_nat_dec 0 (freeVarTerm LNT (Succ v_ 1)%nt)).
        -- simpl in a.
           induction a as [H| H].
           ++ discriminate H.
           ++ contradiction.
        -- rewrite (subFormulaOr LNT).
           apply sysWeaken.
           apply induct.
           ++ rewrite (subFormulaOr LNT).
              apply orI1.
              rewrite (subFormulaExist LNT).
              induction (eq_nat_dec 3 1).
              ** discriminate a.
              ** induction (In_dec eq_nat_dec 3 
                              (freeVarTerm LNT (Succ v_ 1)%nt)).
                 { simpl in a.
                   induction a as [H| H].
                   - elim b1; auto.
                   - contradiction.
                 }
                 rewrite (subFormulaExist LNT).
                 induction (eq_nat_dec 3 0).
                 { discriminate a. }
                 induction (In_dec eq_nat_dec 3 (freeVarTerm LNT Zero)).
                 { simpl in a; contradiction. }
                 apply existI with (v_ 1)%nt.
                 repeat rewrite (subFormulaEqual LNT).
                 simpl in |- *.
                 apply eqTrans with (Succ v_ 1 + Zero)%nt.
                 { apply paPlusSym with (a := Zero) (b := (Succ v_ 1)%nt). }
                 apply pa3.
           ++ apply forallI.
              ** apply closedPA.
              ** apply impI; apply orSys.
                 { rewrite (subFormulaExist LNT).
                   induction (eq_nat_dec 3 1).
                   - discriminate a.
                   - induction (In_dec eq_nat_dec 3 
                                  (freeVarTerm LNT (Succ (v_ 1))%nt)).
                     + simpl in a.
                       induction a as [H| H].
                       * elim b1; auto.
                       * contradiction.
                     + repeat rewrite (subFormulaOr LNT).
                       rewrite (subFormulaExist LNT).
                       induction (eq_nat_dec 3 0).
                       * discriminate a.
                       * induction (In_dec eq_nat_dec 3
                                      (freeVarTerm LNT (Succ (v_ 0))%nt)).
                         -- simpl in a.
                            induction a as [H| H].
                            ++ elim b3; auto.
                            ++ contradiction.
                         -- rewrite (subFormulaExist LNT).
                            induction (eq_nat_dec 3 1).
                            ++ elim b1; auto.
                            ++ induction (In_dec eq_nat_dec 3 
                                            (freeVarTerm LNT (Succ (v_ 1))%nt)).
                               ** elim b2; auto.
                               ** rewrite (subFormulaExist LNT).
                                  induction (eq_nat_dec 3 0).
                                  { elim b3; auto. }
                                  induction (In_dec eq_nat_dec 
                                               3 
                                               (freeVarTerm LNT 
                                                  (Succ (v_ 0))%nt)).
                                  { elim b4; auto. }
                                  repeat rewrite (subFormulaEqual LNT); 
                                    simpl in |- *.
                                  apply existSys.
                                  { apply closedPA. }
                                  simpl in |- *.
                                  unfold not in |- *; intros.
                                  decompose sum H; auto.
                                  eapply orE.
                                  apply sysWeaken.
                                  apply paZeroOrSucc with (t := (v_ 3)%nt).
                                  apply impI.
                                  apply orI2.
                                  apply orI1.
                                  apply eqTrans with (v_ 0 + Succ v_ 3)%nt.
                                  apply eqTrans with (Succ (v_ 0 + v_ 3))%nt.
                                  apply eqSucc.
                                  apply eqTrans with (v_ 0 + Zero)%nt.
                                  apply eqSym.
                                  repeat simple apply sysWeaken.
                                  apply pa3.
                                  apply eqPlus.
                                  apply eqRefl.
                                  apply eqSym.
                                  apply Axm; right; constructor.
                                  apply eqSym.
                                  repeat simple apply sysWeaken.
                                  apply pa4.
                                  apply Axm; left; right; constructor.
                                  unfold newVar in |- *.
                                  simpl in |- *.
                                  apply impI.
                                  apply orI1.
                                  apply existSys.
                                  unfold not in |- *; intros.
                                  induction H as (x, H); induction H as (H, H0).
                                  induction H0 as [x H0| x H0].
                                  elim closedPA with 4.
                                  exists x.
                                  auto.
                                  induction H0.
                                  simpl in H.
                                  decompose sum H; 
                                    discriminate H0 || discriminate H1.
                                  simpl in |- *.
                                  unfold not in |- *; intros.
                                  decompose sum H; 
                                    discriminate H0 || discriminate H1.
                                  apply existI with (var 4).
                                  rewrite (subFormulaEqual LNT); simpl in |- *.
                                  apply eqTrans with (v_ 0 + Succ v_ 3)%nt.
                                  apply eqTrans with (v_ 0 + Succ (Succ v_ 4))%nt.
                                  apply eqTrans with (Succ (v_ 0 + Succ v_ 4))%nt.
                                  apply eqTrans with (Succ v_ 4 + Succ v_ 0)%nt.
                                  repeat simple apply sysWeaken.
                                  apply paPlusSym with 
                                    (a := (Succ v_ 0)%nt) (b := (Succ v_ 4)%nt).
                                  repeat simple apply sysWeaken.
                                  eapply eqTrans.
                                  apply pa4.
                                  apply eqSucc.
                                  apply paPlusSym.
                                  repeat simple apply sysWeaken.
                                  apply eqSym.
                                  apply pa4.
                                  apply eqPlus.
                                  apply eqRefl.
                                  apply eqSucc.
                                  apply eqSym.
                                  apply Axm; right; constructor.
                                  apply Axm; left; right; constructor.
                 }
                 repeat rewrite (subFormulaOr LNT).
                 apply orSys.
                 apply orI2.
                 apply orI2.
                 rewrite (subFormulaExist LNT).
                 induction (eq_nat_dec 3 1).
                 { discriminate a. }
                 induction (In_dec eq_nat_dec 3 
                              (freeVarTerm LNT (Succ v_ 1)%nt)).
                 induction a as [H| H].
                 { elim b1; auto. }
                 contradiction.
                 rewrite (subFormulaExist LNT).
                 induction (eq_nat_dec 3 0).
                 discriminate a.
                 induction (In_dec eq_nat_dec 3
                              (freeVarTerm LNT (Succ v_ 0)%nt)).
                 induction a as [H| H].
                 elim b3; auto.
                 contradiction.
                 apply existI with Zero.
                 repeat rewrite (subFormulaEqual LNT).
                 simpl in |- *.
                 apply eqTrans with  (Succ (Succ v_ 1 + Zero))%nt.
                 apply sysWeaken.
                 apply pa4 with (a := (Succ v_ 1)%nt) (b := Zero).
                 apply eqTrans with (Succ (Succ v_ 1))%nt.
                 apply eqSucc.
                 apply sysWeaken.
                 apply pa3.
                 fold (Succ (v_ 0))%nt.
                 apply eqSucc.
                 apply eqSym.
                 apply Axm; right; constructor.
                 do 2 rewrite (subFormulaExist LNT).
                 induction (eq_nat_dec 3 1).
                 discriminate a.
                 induction (In_dec eq_nat_dec 3 
                              (freeVarTerm LNT (Succ v_ 1)%nt)).
                 induction a as [H| H].
                 elim b1; auto.
                 contradiction.
                 do 2 rewrite (subFormulaExist LNT).
                 induction (eq_nat_dec 3 0).
                 discriminate a.
                 induction (In_dec eq_nat_dec 3 
                              (freeVarTerm LNT (Succ (v_ 0))%nt)).
                 induction a as [H| H].
                 elim b3; auto.
                 contradiction.
                 apply orI2.
                 apply orI2.
                 apply existSys.
                 apply closedPA.
                 simpl in |- *.
                 unfold not in |- *; intros.
                 decompose sum H; auto.
                 apply existI with (Succ v_ 3)%nt.
                 repeat rewrite (subFormulaEqual LNT).
                 simpl in |- *.
                 apply eqTrans with  (Succ (Succ v_ 1 + Succ v_ 3))%nt.
                 apply sysWeaken.
                 apply pa4 with (a := (Succ v_ 1)%nt) (b := (Succ v_ 3)%nt).
                 fold (Succ v_ 0)%nt in |- *.
                 apply eqSucc.
                 apply Axm; right; constructor.
Qed.

From hydras.Ackermann Require Import primRec.
From hydras.Ackermann Require Import cPair.
From Coq Require Import Arith Lia.
From hydras.Ackermann Require Import code.
From hydras.Ackermann Require Import codeSubFormula.
From hydras.Ackermann Require Import folProp.
From hydras.Ackermann Require Import folProof.
From hydras.Ackermann Require Import Languages.
From hydras.Ackermann Require Import subAll.
From hydras.Ackermann Require Import subProp.
From hydras.Ackermann Require Import folLogic3.
From hydras.Ackermann Require Import folReplace.
From hydras.Ackermann Require Import LNN.
From hydras.Ackermann Require Import codeNatToTerm.
From Goedel Require Import PRrepresentable.
From hydras.Ackermann Require Import ListExt.
From Coq Require Import List.
From hydras.Ackermann Require Import NN.
From hydras.Ackermann Require Import expressible.
From hydras Require Import Compat815.

Definition subStar (a v n : nat) : nat := codeSubFormula a v (codeNatToTerm n).

Lemma subStarIsPR : isPR 3 subStar.
Proof.
  unfold subStar; apply compose3_3IsPR  with
    (f1 := fun a v n : nat => a)
    (f2 := fun a v n : nat => v)
    (f3 := fun a v n : nat => codeNatToTerm n).
  - apply pi1_3IsPR.
  - apply pi2_3IsPR.
  - apply filter001IsPR, codeNatToTermIsPR.
  - apply codeSubFormulaIsPR.
Qed.

Section LNN_FixPoint.

Let codeFormula := codeFormula LNN codeLNTFunction codeLNNRelation.

Lemma FixPointLNN :
 forall (A : Formula) (v : nat),
 {B : Formula |
   SysPrf NN
     (B <-> substituteFormula LNN A v (natToTermLNN (codeFormula B)))%fol /\
   (forall x : nat,
    In x (freeVarFormula LNN B) <->
    In x (List.remove eq_nat_dec v (freeVarFormula LNN A)))}.
Proof.
  intros A v;
    set (subStarFormula := primRecFormula _ (proj1_sig subStarIsPR)).
  assert (represent : Representable NN 3 subStar subStarFormula).
  { unfold subStarFormula; apply primRecRepresentable. }
  set (nv := newVar (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNN A)).
  assert (H: 0 <> nv).
   { intros H; elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNN A)).
     unfold nv in H; rewrite <- H; simpl; right; auto.
   } 
   assert (H0: 1 <> nv).
   { intros H0; elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNN A)).
     unfold nv in H0; rewrite <- H0; simpl; auto.
   } 
   assert (H1: 2 <> nv).
   {  intros H1; elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNN A)).
      unfold nv in H1; rewrite <- H1; simpl; auto.
   } 
   assert (H2: 3 <> nv).
   { intro H2; elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNN A)).
     unfold nv in H2; rewrite <- H2; simpl; auto.
   } assert (H3: 3 < nv) by lia. 
   set
     (Theta :=
        existH v
          (andH
             (substituteFormula LNN
                (substituteFormula LNN
                   (substituteFormula LNN
                      (substituteFormula LNN subStarFormula 3 (var nv)) 2
                      (natToTerm nv)) 1 (var nv)) 0 (var v)) A)). 
   exists (substituteFormula LNN Theta nv (natToTerm (codeFormula Theta))). 
   split.
  - set (N :=
           natToTermLNN
             (codeFormula
                (substituteFormula LNN Theta nv (natToTerm (codeFormula Theta))))).
    unfold Theta at 1; rewrite (subFormulaExist LNN).
    induction (eq_nat_dec v nv) as [a | b].
    + elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNN A)).
      fold nv; simpl; auto.
    + induction
        (In_dec eq_nat_dec v (freeVarTerm LNN (natToTerm (codeFormula Theta)))) 
        as [a | b0].
      * elim (closedNatToTerm _ _ a).
      * clear b b0.
        rewrite (subFormulaAnd LNN).
        apply iffTrans with
          (existH v
             (andH
                (substituteFormula LNN
                   (substituteFormula LNN
                      (substituteFormula LNN
                         (substituteFormula LNN subStarFormula 3
                            (natToTerm (codeFormula Theta))) 2 
                         (natToTerm nv)) 1 (natToTerm (codeFormula Theta))) 0
                   (var v)) A)).
        -- apply (reduceExist LNN).
           ++ apply closedNN.
           ++ apply (reduceAnd LNN).
              ** eapply iffTrans.
                 --- apply (subFormulaExch LNN).
                     +++ assumption.
                     +++  intros [H4| H4].
                          *** elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: 
                                               freeVarFormula LNN A)).
                              fold nv; rewrite <- H4; simpl; auto.
                          *** apply H4.
                     +++ apply closedNatToTerm.
                 --- apply (reduceSub LNN).
                     +++ apply closedNN.
                     +++ eapply iffTrans.
                         *** apply (subSubFormula LNN).
                             assumption.
                             apply closedNatToTerm.
                         *** rewrite (subTermVar1 LNN).
                             apply (reduceSub LNN).
                             apply closedNN.
                             eapply iffTrans.
                             apply (subFormulaExch LNN).
                             assumption.
                             apply closedNatToTerm.
                             apply closedNatToTerm.
                             apply (reduceSub LNN).
                             apply closedNN.
                             apply (subFormulaTrans LNN).
                             intros H4;
                               assert (H5: In nv (freeVarFormula LNN subStarFormula)) 
                             by (eapply in_remove, H4).
                             induction represent as [H6 H7].
                             elim (Compat815.lt_not_le _ _ H3).
                             auto.
              ** apply (subFormulaNil LNN).
                 intros H4;
                 elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNN A)).
                 fold nv; simpl; repeat right; auto.
        -- apply iffI.
           ++ apply impI.
              apply existSys.
              ** apply closedNN.
              ** intros H4; induction (freeVarSubFormula3 _ _ _ _ _ H4) as [H5 | H5].
                 --- now elim (in_remove_neq _ _ _ _ _ H5).
                 --- elim (closedNatToTerm _ _ H5).
              ** apply impE with (substituteFormula LNN 
                                    (equal (var 0) N) 0 (var v)).
                 --- rewrite (subFormulaEqual LNN).
                     rewrite (subTermVar1 LNN).
                     rewrite (subTermNil LNN).
                     +++ apply impI.
                         apply impE with (substituteFormula LNN A v (var v)).
                         *** apply (subWithEquals LNN).
                             apply Axm; right; constructor.
                         *** rewrite (subFormulaId LNN).
                             eapply andE2.
                             apply Axm; left; right; constructor.
                     +++ unfold N; apply closedNatToTerm.
                 --- apply impE with
                       (substituteFormula LNN
                          (substituteFormula LNN
                             (substituteFormula LNN
                                (substituteFormula LNN subStarFormula 3
                                   (natToTerm (codeFormula Theta))) 2 
                                (natToTerm nv)) 1 (natToTerm (codeFormula Theta))) 0 
                          (var v)).
                     +++ apply iffE1.
                         apply sysWeaken.
                         apply (reduceSub LNN).
                         *** apply closedNN.
                         *** induction represent as (H4, H5); simpl in H5.
                             unfold N;
                               replace
                                 (codeFormula
                                    (substituteFormula LNN Theta nv 
                                       (natToTerm (codeFormula Theta)))) 
                               with
                               (subStar (codeFormula Theta) nv (codeFormula Theta)).
                             apply H5.
                             unfold subStar; rewrite codeNatToTermCorrectLNN.
                             unfold codeFormula at 1; rewrite codeSubFormulaCorrect.
                             reflexivity.
                     +++ eapply andE1; apply Axm; right; constructor.
           ++ apply impI; apply existI with N.
              rewrite (subFormulaAnd LNN).
              apply andI.
              ** apply sysWeaken.
                 eapply
                   impE
                   with
                   (substituteFormula LNN
                      (substituteFormula LNN (equal (var 0) N) 0 (var v)) v N).
                 --- apply iffE2.
                     apply (reduceSub LNN).
                     +++ apply closedNN.
                     +++ apply (reduceSub LNN).
                         *** apply closedNN.
                         *** induction represent as (H4, H5).
                             simpl in H5; unfold N;
                               replace
                                 (codeFormula
                                    (substituteFormula LNN Theta nv 
                                       (natToTerm (codeFormula Theta)))) 
                               with
                               (subStar (codeFormula Theta) nv (codeFormula Theta)).
                             apply H5.
                             unfold subStar; rewrite codeNatToTermCorrectLNN.
                             unfold codeFormula at 1; now rewrite codeSubFormulaCorrect.
                 --- repeat rewrite (subFormulaEqual LNN).
                     repeat rewrite (subTermVar1 LNN).
                     repeat rewrite (subTermNil LNN N).
                     +++ apply eqRefl.
                     +++ unfold N; apply closedNatToTerm.
                     +++ unfold N; apply closedNatToTerm.
              ** apply Axm; right; constructor.
  - intro x; split.
    + intro H4; unfold Theta at 1 in H4. (* ; unfold existH in H4.*)
      induction represent as (H5, H6).
      repeat
        match goal with
        | H1:(?X1 = ?X2),H2:(?X1 <> ?X2) |- _ =>
            elim H2; apply H1
        | H1:(?X1 = ?X2),H2:(?X2 <> ?X1) |- _ =>
            elim H2; symmetry  in |- *; apply H1
        | H:(In ?X3 (freeVarFormula LNN (existH ?X1 ?X2))) |- _ =>
            assert (In X3 (List.remove  eq_nat_dec X1 (freeVarFormula LNN X2)));
            [ apply H | clear H ]
        | H:(In ?X3 (freeVarFormula LNN (forallH LNN ?X1 ?X2))) |- _ =>
            assert (In X3 (List.remove  eq_nat_dec X1 (freeVarFormula LNN X2)));
            [ apply H | clear H ]
        | H:(In ?X3 (List.remove eq_nat_dec ?X1 (freeVarFormula LNN ?X2))) |- _
          =>
            assert (In X3 (freeVarFormula LNN X2));
            [ eapply in_remove; apply H
            | assert (X3 <> X1); [ eapply in_remove_neq; apply H | clear H ] ]
        | H:(In ?X3 (freeVarFormula LNN (andH ?X1 ?X2))) |- _ =>
            assert (In X3 (freeVarFormula LNN X1 ++ freeVarFormula LNN X2));
            [ apply H | clear H ]
        | H:(In ?X3 (freeVarFormula LNN (impH LNN ?X1 ?X2))) |- _ =>
            assert (In X3 (freeVarFormula LNN X1 ++ freeVarFormula LNN X2));
            [ apply H | clear H ]
        | H:(In ?X3 (freeVarFormula LNN (notH LNN ?X1))) |- _ =>
            assert (In X3 (freeVarFormula LNN X1)); [ apply H | clear H ]
        | H:(In _ (_ ++ _)) |- _ =>
            induction (in_app_or _ _ _ H); clear H
        | H:(In _ (freeVarFormula LNN (substituteFormula LNN ?X1 ?X2 ?X3))) |- _ =>
            induction (freeVarSubFormula3 _ _ _ _ _ H); clear H
        | H:(In _ (freeVarTerm LNN (natToTerm _))) |- _ =>
            elim (closedNatToTerm _ _ H)
        | H:(In _ (freeVarTerm LNN Zero)) |- _ =>
            elim H
        | H:(In _ (freeVarTerm LNN (Succ _))) |- _ =>
            rewrite freeVarSucc in H
        | H:(In _ (freeVarTerm LNN (var _))) |- _ =>
            simpl in H; decompose sum H; clear H
        | H:(In _ (freeVarTerm LNN (var LNN _))) |- _ =>
            simpl in H; decompose sum H; clear H
        end.
      elim (Compat815.le_not_lt _ _ (H5 _ H4)); lia. 
      apply in_in_remove; auto.
    + intro H4; assert (H5:  In x (freeVarFormula LNN A))
        by (eapply in_remove, H4).
      assert (H6: x <> v) by (  eapply in_remove_neq, H4 ). 
      clear H4; apply freeVarSubFormula1.
      * intro H4; rewrite <- H4 in H5.
        elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNN A)).
        fold nv; simpl; now repeat right.
      * unfold Theta;
          apply
            (@in_in_remove nat eq_nat_dec 
               (freeVarFormula LNN
                  (substituteFormula LNN
                     (substituteFormula LNN
                        (substituteFormula LNN
                           (substituteFormula LNN subStarFormula 3 (var nv)) 2
                           (natToTerm nv)) 1 (var nv)) 0 (var v)) ++
                  freeVarFormula LNN A) x v).
        -- assumption.
        -- apply in_or_app; now right.
Qed.

End LNN_FixPoint.

From hydras.Ackermann Require Import PA.
From hydras.Ackermann Require Import NN2PA.

Section LNT_FixPoint.

Let codeFormula := codeFormula LNT codeLNTFunction codeLNTRelation.

Lemma FixPointLNT  (A : Formula) (v : nat):
  {B : Formula |
    SysPrf PA
      (iffH B (substituteFormula LNT A v (natToTermLNT (codeFormula B)))) /\
      (forall x : nat,
          In x (freeVarFormula LNT B) <->
            In x (List.remove eq_nat_dec v (freeVarFormula LNT A)))}.
Proof.
  set (subStarFormula := primRecFormula _ (proj1_sig subStarIsPR)).
  assert (represent : Representable NN 3 subStar subStarFormula)
    by (unfold subStarFormula; apply primRecRepresentable).
  set (nv := newVar (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNT A)).
  assert (H: 0 <> nv).
  { intro H; 
      elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNT A)).
    unfold nv in H; rewrite <- H.
    simpl; right; auto.
  } 
  assert (H0: 1 <> nv).
  { intro H0;
      elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNT A)).
    unfold nv in H0; rewrite <- H0; simpl; auto.
  }
  assert (H1: 2 <> nv).
  { intro H1; 
      elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNT A));
      unfold nv in H1; rewrite <- H1; simpl; auto. 
  } 
  assert (H2: 3 <> nv).
  { intro H2;
      elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNT A)).
    unfold nv in H2; rewrite <- H2; simpl; auto. 
  } 
  assert (H3: 3 < nv) by lia.
  set  (Theta :=
          existH v
            (andH
               (substituteFormula LNT
                  (substituteFormula LNT
                     (substituteFormula LNT
                        (substituteFormula LNT (LNN2LNT_formula subStarFormula) 3
                           (var nv)) 2 (natToTerm nv)) 1 (var nv)) 0 
                  (var v)) A)).
  exists (substituteFormula LNT Theta nv (natToTerm (codeFormula Theta))).
  split.
  - set
      (N :=
         natToTermLNT
           (codeFormula
              (substituteFormula LNT Theta nv (natToTerm (codeFormula Theta))))).
    unfold Theta at 1; rewrite (subFormulaExist LNT).
    induction (eq_nat_dec v nv) as [a | b]. 
    + elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNT A)).
      fold nv; simpl; now left.   
    + induction
        (In_dec eq_nat_dec v (freeVarTerm LNT (natToTerm (codeFormula Theta)))) 
        as [a | ?].
      * elim (closedNatToTerm _ _ a).
      * clear b b0; rewrite (subFormulaAnd LNT).
        apply
          iffTrans
          with
          (existH v
             (andH
                (substituteFormula LNT
                   (substituteFormula LNT
                      (substituteFormula LNT
                         (substituteFormula LNT (LNN2LNT_formula subStarFormula) 3
                            (natToTerm (codeFormula Theta))) 2 
                         (natToTerm nv)) 1 (natToTerm (codeFormula Theta))) 0
                   (var v)) A)).
        -- apply (reduceExist LNT).
           ++ apply closedPA.
           ++ apply (reduceAnd LNT).
              ** eapply iffTrans.
                 --- apply (subFormulaExch LNT).
                    +++  assumption.
                    +++ intros [H4| H4].
                        *** elim
                            (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNT A)).
                            fold nv; rewrite <- H4; simpl; auto.
                        *** apply H4.
                    +++ apply closedNatToTerm.
                 --- apply (reduceSub LNT).
                     +++ apply closedPA.
                     +++ eapply iffTrans.
                         *** apply (subSubFormula LNT).
                             assumption.
                             apply closedNatToTerm.
                         *** rewrite (subTermVar1 LNT).
                             apply (reduceSub LNT).
                             apply closedPA.
                             eapply iffTrans.
                             apply (subFormulaExch LNT).
                             assumption.
                             apply closedNatToTerm.
                             apply closedNatToTerm.
                             apply (reduceSub LNT).
                             apply closedPA.
                             apply (subFormulaTrans LNT).
                             intros H4.
                             assert (H5: 
                                      In nv (freeVarFormula LNT 
                                               (LNN2LNT_formula subStarFormula)))
                             by  eapply in_remove,  H4.
                             destruct represent as (H6, H7).
                             elim (Compat815.lt_not_le _ _ H3).
                             apply H6.
                             apply LNN2LNT_freeVarFormula1; assumption.
              ** apply (subFormulaNil LNT).
                 intros H4;
                   elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNT A)).
                 fold nv; simpl; now repeat right.
        -- apply iffI.
           ++ apply impI, existSys.
              ** apply closedPA.
              **  intros H4; induction (freeVarSubFormula3 _ _ _ _ _ H4) as [H5 | H5].
                  --- now elim (in_remove_neq _ _ _ _ _ H5).
                  --- elim (closedNatToTerm _ _ H5).
              ** apply impE with (substituteFormula LNT (equal (var 0) N) 0 (var v)).
                 --- rewrite (subFormulaEqual LNT).
                     rewrite (subTermVar1 LNT).
                     rewrite (subTermNil LNT).
                     +++ apply impI.
                         apply impE with (substituteFormula LNT A v (var v)).
                         *** apply (subWithEquals LNT).
                             apply Axm; right; constructor.
                         *** rewrite (subFormulaId LNT).
                             eapply andE2.
                             apply Axm; left; right; constructor.
                     +++ unfold N; apply closedNatToTerm.
                 --- apply impE with
                       (substituteFormula LNT
                          (substituteFormula LNT
                             (substituteFormula LNT
                                (substituteFormula LNT 
                                   (LNN2LNT_formula subStarFormula) 3
                                   (natToTerm (codeFormula Theta))) 2 
                                (natToTerm nv)) 1 (natToTerm (codeFormula Theta))) 0 
                          (var v)).
                     +++ apply iffE1.
                         apply sysWeaken.
                         apply (reduceSub LNT).
                         *** apply closedPA.
                         *** induction represent as (H4, H5).
                             simpl in H5; unfold N.
                             replace
                               (codeFormula
                                  (substituteFormula LNT Theta nv 
                                     (natToTerm (codeFormula Theta)))) 
                               with
                               (subStar (codeFormula Theta) nv (codeFormula Theta)).
                             replace
                               (equal (var 0)
                                  (natToTermLNT (subStar (codeFormula Theta) nv 
                                                   (codeFormula Theta)))) 
                               with
                               (LNN2LNT_formula
                                  (equal (var 0)
                                     (LNN.natToTerm (subStar (codeFormula Theta) nv 
                                                       (codeFormula Theta))))).
                             apply iffTrans  with
                               (LNN2LNT_formula
                                  (substituteFormula LNN
                                     (substituteFormula LNN
                                        (substituteFormula LNN subStarFormula 3
                                           (LNN.natToTerm (codeFormula Theta))) 2 
                                        (LNN.natToTerm nv)) 1 
                                     (LNN.natToTerm (codeFormula Theta)))).
                             apply iffSym.
                             eapply iffTrans; [ apply LNN2LNT_subFormula | idtac ].
                             rewrite LNN2LNT_natToTerm; apply (reduceSub LNT);
                               [ apply closedPA | idtac ].
                             eapply iffTrans; [ apply LNN2LNT_subFormula | idtac ].
                             rewrite LNN2LNT_natToTerm; apply (reduceSub LNT);
                               [ apply closedPA | idtac ].
                             eapply iffTrans; [ apply LNN2LNT_subFormula | idtac ].
                             rewrite LNN2LNT_natToTerm; apply (reduceSub LNT);
                               [ apply closedPA | idtac ].
                             apply iffRefl.
                             rewrite <- LNN2LNT_iff.
                             apply NN2PA.
                             apply H5.
                             rewrite <- LNN2LNT_natToTerm.
                             reflexivity.
                             unfold subStar; rewrite codeNatToTermCorrectLNT.
                             unfold codeFormula at 1; rewrite codeSubFormulaCorrect.
                             reflexivity.
                     +++ eapply andE1.
                         apply Axm; right; constructor.
           ++ apply impI.
              apply existI with N.
              rewrite (subFormulaAnd LNT).
              apply andI.
              apply sysWeaken.
              ** eapply impE with
                   (substituteFormula LNT
                      (substituteFormula LNT (equal (var 0) N) 0 (var v)) v N).
                 --- apply iffE2.
                     apply (reduceSub LNT).
                     +++ apply closedPA.
                     +++ apply (reduceSub LNT).
                         *** apply closedPA.
                         *** induction represent as (H4, H5).
                             simpl in H5.
                             unfold N;
                               replace
                                 (codeFormula
                                    (substituteFormula LNT Theta nv 
                                       (natToTerm (codeFormula Theta)))) 
                               with
                               (subStar (codeFormula Theta) nv (codeFormula Theta)).
                             replace
                               (equal (var 0)
                                  (natToTermLNT (subStar (codeFormula Theta) nv 
                                                   (codeFormula Theta)))) 
                               with
                               (LNN2LNT_formula
                                  (equal (var 0)
                                     (LNN.natToTerm 
                                        (subStar (codeFormula Theta) nv 
                                           (codeFormula Theta))))).
                             apply
                               iffTrans
                               with
                               (LNN2LNT_formula
                                  (substituteFormula LNN
                                     (substituteFormula LNN
                                        (substituteFormula LNN subStarFormula 3
                                           (LNN.natToTerm (codeFormula Theta))) 2 
                                        (LNN.natToTerm nv)) 1
                                     (LNN.natToTerm
                                        (codeFormula Theta)))).
                             apply iffSym.
                             eapply iffTrans; [ apply LNN2LNT_subFormula | idtac ].
                             rewrite LNN2LNT_natToTerm; apply (reduceSub LNT);
                               [ apply closedPA | idtac ].
                             eapply iffTrans; [ apply LNN2LNT_subFormula | idtac ].
                             rewrite LNN2LNT_natToTerm; apply (reduceSub LNT);
                               [ apply closedPA | idtac ].
                             eapply iffTrans; [ apply LNN2LNT_subFormula | idtac ].
                             rewrite LNN2LNT_natToTerm; apply (reduceSub LNT);
                               [ apply closedPA | idtac ].
                             apply iffRefl.
                             rewrite <- LNN2LNT_iff.
                             apply NN2PA.
                             apply H5.
                             rewrite <- LNN2LNT_natToTerm.
                             reflexivity.
                             unfold subStar; rewrite codeNatToTermCorrectLNT.
                             unfold codeFormula at 1; rewrite codeSubFormulaCorrect.
                             reflexivity.
                 --- repeat rewrite (subFormulaEqual LNT).
                     repeat rewrite (subTermVar1 LNT).
                     repeat rewrite (subTermNil LNT N).
                     +++ apply eqRefl.
                     +++ unfold N; apply closedNatToTerm.
                     +++ unfold N; apply closedNatToTerm.
              ** apply Axm; right; constructor.
  - intro x; split.
    + intro H4; unfold Theta at 1 in H4.
      (* unfold existH in H4. *)
      induction represent as (H5, H6).
      repeat
        match goal with
        | H1:(?X1 = ?X2),H2:(?X1 <> ?X2) |- _ =>
            elim H2; apply H1
        | H1:(?X1 = ?X2),H2:(?X2 <> ?X1) |- _ =>
            elim H2; symmetry  in |- *; apply H1
        | H:(In ?X3 (freeVarFormula LNT (existH ?X1 ?X2))) |- _ =>
            assert (In X3 (List.remove eq_nat_dec X1 (freeVarFormula LNT X2)));
            [ apply H | clear H ]
        | H:(In ?X3 (freeVarFormula LNT (forallH LNT ?X1 ?X2))) |- _ =>
            assert (In X3 (List.remove  eq_nat_dec X1 (freeVarFormula LNT X2)));
            [ apply H | clear H ]
        | H:(In ?X3 (List.remove eq_nat_dec ?X1 (freeVarFormula LNT ?X2))) |- _
          =>
            assert (In X3 (freeVarFormula LNT X2));
            [ eapply in_remove; apply H
            | assert (X3 <> X1); [ eapply in_remove_neq; apply H | clear H ] ]
        | H:(In ?X3 (freeVarFormula LNT (andH  ?X1 ?X2))) |- _ =>
            assert (In X3 (freeVarFormula LNT X1 ++ freeVarFormula LNT X2));
            [ apply H | clear H ]
        | H:(In ?X3 (freeVarFormula LNT (impH LNT ?X1 ?X2))) |- _ =>
            assert (In X3 (freeVarFormula LNT X1 ++ freeVarFormula LNT X2));
            [ apply H | clear H ]
        | H:(In ?X3 (freeVarFormula LNT (notH LNT ?X1))) |- _ =>
            assert (In X3 (freeVarFormula LNT X1)); [ apply H | clear H ]
        | H:(In _ (_ ++ _)) |- _ =>
            induction (in_app_or _ _ _ H); clear H
        | H:(In _ (freeVarFormula LNT (substituteFormula LNT ?X1 ?X2 ?X3))) |- _ =>
            induction (freeVarSubFormula3 _ _ _ _ _ H); clear H
        | H:(In _ (freeVarTerm LNT (natToTerm _))) |- _ =>
            elim (closedNatToTerm _ _ H)
        | H:(In _ (freeVarTerm LNT Zero)) |- _ =>
            elim H
        | H:(In _ (freeVarTerm LNT (Succ _))) |- _ =>
            rewrite freeVarSucc in H
        | H:(In _ (freeVarTerm LNT (var _))) |- _ =>
            simpl in H; decompose sum H; clear H
        | H:(In _ (freeVarTerm LNT (var LNT _))) |- _ =>
            simpl in H; decompose sum H; clear H
        end.
      * elim (Compat815.le_not_lt x 3).
        -- apply H5.
          now  apply LNN2LNT_freeVarFormula1.
        --  lia. 
      * apply in_in_remove; auto.
    + intro H4; 
        assert (H5: In x (freeVarFormula LNT A)) 
        by (eapply in_remove, H4);
        assert (H6: x <> v) by (eapply in_remove_neq, H4);  clear H4.
      apply freeVarSubFormula1.
      * intros H4; rewrite <- H4 in H5.
        elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNT A)).
        fold nv; simpl; now repeat right.
      * unfold Theta;
          apply
            (@in_in_remove nat eq_nat_dec
               (freeVarFormula LNT
                  (substituteFormula LNT
                     (substituteFormula LNT
                        (substituteFormula LNT
                           (substituteFormula LNT 
                              (LNN2LNT_formula subStarFormula) 3
                              (var nv)) 2 (natToTerm nv)) 1 (var nv)) 0 
                     (var v)) ++ freeVarFormula LNT A) x v).
        -- assumption.
        -- apply in_or_app; now right. 
Qed.

End LNT_FixPoint.

From Coq Require Import Ensembles.
From Coq Require Import List.
From Coq Require Import Arith Lia.
From hydras.Ackermann Require Import folProp.
From hydras.Ackermann Require Import folProof.
From hydras.Ackermann Require Import folReplace.
From hydras.Ackermann Require Import folLogic3.
From hydras.Ackermann Require Import subProp.
From hydras.Ackermann Require Import ListExt.
From Goedel Require Import fixPoint.
From Goedel Require Import codeSysPrf.
From hydras.Ackermann Require Import NNtheory.
From hydras.Ackermann Require Import code.
From Goedel Require Import PRrepresentable.
From hydras.Ackermann Require Import expressible.
From hydras.Ackermann Require Import checkPrf.
From hydras.Ackermann Require Import codeNatToTerm.
From hydras Require Import Compat815.

Section Rosser's_Incompleteness.

Definition codeFormula := codeFormula LNN codeLNTFunction codeLNNRelation.

Variable T : System.

Hypothesis extendsNN : Included _ NN T.

Variable repT : Formula.
Variable v0 : nat.
Hypothesis
  freeVarRepT : forall v : nat, In v (freeVarFormula LNN repT) -> v = v0.
Hypothesis
  expressT1 :
    forall f : Formula,
    mem _ T f ->
    SysPrf T (substituteFormula LNN repT v0 (natToTerm (codeFormula f))).
Hypothesis
  expressT2 :
    forall f : Formula,
    ~ mem _ T f ->
    SysPrf T
      (notH (substituteFormula LNN repT v0 (natToTerm (codeFormula f)))).

Definition codeSysPrf :=
  codeSysPrf LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR
    codeArityLNTFIsPR codeArityLNNRIsPR repT v0.

Definition codeSysPrfCorrect1 :=
  codeSysPrfCorrect1 LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNNRIsPR
    codeArityLNNRIsCorrect1 T extendsNN T repT v0 freeVarRepT expressT1.

Definition codeSysPrfCorrect2 :=
  codeSysPrfCorrect2 LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNNRIsPR
    codeArityLNNRIsCorrect1 T extendsNN T repT v0 freeVarRepT expressT2.

Definition codeSysPrfCorrect3 :=
  codeSysPrfCorrect3 LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1
    codeArityLNTFIsCorrect2 codeArityLNNRIsPR codeArityLNNRIsCorrect1
    codeArityLNNRIsCorrect2 codeLNTFunctionInj codeLNNRelationInj T extendsNN.
  
Definition codePrf := codePrf LNN codeLNTFunction codeLNNRelation.

Definition codeSysPrfNot :=
  codeSysPrfNot LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNNRIsPR repT v0.

Definition freeVarCodeSysPrfN :=
  freeVarCodeSysPrfN LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNNRIsPR repT v0 freeVarRepT.

Definition codeSysPrfNCorrect1 :=
  codeSysPrfNCorrect1 LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNNRIsPR
    codeArityLNNRIsCorrect1 T extendsNN T repT v0 freeVarRepT expressT1.

Definition codeSysPrfNCorrect2 :=
  codeSysPrfNCorrect2 LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNNRIsPR
    codeArityLNNRIsCorrect1 T extendsNN T repT v0 freeVarRepT expressT2.

Definition codeSysPrfNCorrect3 :=
  codeSysPrfNCorrect3 LNN codeLNTFunction codeLNNRelation codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1
    codeArityLNTFIsCorrect2 codeArityLNNRIsPR codeArityLNNRIsCorrect1
    codeArityLNNRIsCorrect2 codeLNTFunctionInj codeLNNRelationInj T extendsNN
    repT v0 freeVarRepT.

Lemma decideAxioms :
  (forall x : Formula, mem _ T x \/ ~ mem _ T x) ->
  forall x : Formulas,
    (forall g : Formula, In g x -> mem _ T g) \/
      (exists g : Formula, In g x /\ ~ mem _ T g).
Proof.
  intros H x; induction x as [| a x Hrecx].
  - left.
    intros g H0; elim H0.
  - destruct Hrecx as [H0| H0].
    + induction (H a) as [H1 | H1].
      * left; intros g [H2 | H2]. 
        -- now subst. 
        -- auto.
      * right; exists a; split. 
        -- auto with datatypes.
        -- assumption.
    + right. destruct H0 as [x0 [H0 H1]].
      exists x0;  split. 
      * auto with datatypes. 
      * assumption. 
Qed.

Lemma searchProof :
  (forall x : Formula, mem _ T x \/ ~ mem _ T x) ->
  forall (a b : Formula) (A : Formulas) (p : Prf LNN A a),
    (exists B : Formulas,
        (exists q : Prf LNN B b,
            codePrf _ _ q < S (codePrf _ _ p) /\
              (forall x : Formula, In x B -> mem _ T x))) \/
      (forall (B : Formulas) (q : Prf LNN B b),
          codePrf _ _ q < S (codePrf _ _ p) ->
          exists g : Formula, In g B /\ ~ mem _ T g).
Proof.
  intros H a b A p.
  induction (S (codePrf A a p)).
  - right; intros B q H0; lia. 
  - induction IHn as [H0| H0].
    + left; decompose record H0; exists x, x0; auto.      
    + induction
        (eq_nat_dec
           (checkPrf LNN codeLNTFunction codeLNNRelation codeArityLNTF codeArityLNNR
              (codeFormula b) n) 0) as [a0 | b0].
      * right; intros B q H1; 
          induction (proj1 (Nat.lt_eq_cases _ _) (proj1 (Nat.lt_succ_r _ _) H1)).
        -- eauto.
        -- rewrite <- H2 in a0.
           rewrite
             (checkPrfCorrect1 LNN codeLNTFunction codeLNNRelation codeArityLNTF
                codeArityLNNR codeArityLNTFIsCorrect1 codeArityLNNRIsCorrect1)
             in a0.
           discriminate a0.
      * decompose record
          (checkPrfCorrect2 LNN codeLNTFunction codeLNNRelation codeArityLNTF
             codeArityLNNR codeArityLNTFIsCorrect1 codeArityLNTFIsCorrect2
             codeArityLNNRIsCorrect1 codeArityLNNRIsCorrect2 codeLNTFunctionInj
             codeLNNRelationInj _ _ b0).
        assert (H1:  x = b).
        { eapply codeFormulaInj.
          - apply codeLNTFunctionInj.
          - apply codeLNNRelationInj.
          - assumption.
        } 
        rewrite <- H1.
        induction (decideAxioms H x0) as [H4 | ?]. 
        -- left; exists x0, x1.
           unfold codePrf; rewrite H3;  auto. 
        -- right; intros B q H5.
           induction (proj1 (Nat.lt_eq_cases _ _) (proj1 (Nat.lt_succ_r _ _) H5))
             as [H6 | H6].
           ++ rewrite <- H1 in H0; eauto.
           ++ assert (H7: B = x0).
              { eapply (codePrfInjAxm LNN) with (p := q) (q := x1).
                - apply codeLNTFunctionInj.
                - apply codeLNNRelationInj.
                - transitivity n.
                  + unfold codePrf in H6; apply H6.
                  + symmetry; apply H3.
              }
              now rewrite H7.
Qed.

(** To prove the strong contructive result we need the decidability of T **)

Theorem Rosser'sIncompleteness :
 (forall x : Formula, mem _ T x \/ ~ mem _ T x) ->
 exists f : Formula,
   (forall v : nat, ~ In v (freeVarFormula LNN f)) /\
   (SysPrf T f \/ SysPrf T (notH f) -> Inconsistent LNN T).
Proof.
  intros decide.
  set
    (A :=
       forallH 1
         (impH codeSysPrf
            (existH 2
               (andH (LT (var 2) (var 1))
                  (substituteFormula LNN codeSysPrfNot 1 (var 2)))))). 
  destruct (FixPointLNN A 0) as [x [H0 H1]].
  exists x; split.
  -  intros v H; induction (H1 v) as [H2 H3]. 
     assert (H4: In v (list_remove nat eq_nat_dec 0 (freeVarFormula LNN A)))
     by apply H2, H.
     unfold A in H4; SimplFreeVar.
     + assert (H4: v <= 1).
       { apply
           (freeVarCodeSysPrf LNN codeLNTFunction codeLNNRelation codeArityLNTF
              codeArityLNNR codeArityLNTFIsPR codeArityLNNRIsPR repT v0 freeVarRepT).
         apply H5.
       } 
       lia.
     + assert (H4: v <= 1) by (apply freeVarCodeSysPrfN; assumption); lia. 
  - intros [H| H].
    + unfold Inconsistent in |- *.
      intro f; elim H; intros x0 [x1 H2]. 
      induction (searchProof decide _ (notH x) _ x1) as [H3 | H3].
      * decompose record H3.
        apply contradiction with x.
        -- assumption.
        -- now exists x2, x3.
      * apply
          contradiction
          with
          (existH 2
             (andH (LT (var 2) (natToTerm (codePrf _ _ x1)))
                (substituteFormula LNN
                   (substituteFormula LNN codeSysPrfNot 0
                      (natToTerm (codeFormula x))) 1 (var 2)))).
        -- apply impE with
             (existH 2
                (andH (LT (var 2) (natToTerm (codePrf x0 x x1)))
                   (substituteFormula LNN
                      (substituteFormula LNN
                         (substituteFormula LNN codeSysPrfNot 0
                            (natToTerm (codeFormula x))) 1 (var 2)) 1
                      (natToTerm (codePrf _ _ x1))))).
           ++ apply iffE1; apply sysExtend with NN.
              ** apply extendsNN.
              ** apply (reduceExist LNN).
                 --- apply closedNN.
                 --- apply (reduceAnd LNN).
                     +++ apply iffRefl.
                     +++ apply (subFormulaNil LNN).
                         intro H4; induction (freeVarSubFormula3 _ _ _ _ _ H4).
                         *** now apply (In_list_remove2 _ _ _ _ _ H5).
                         *** simpl in H5; decompose sum H5; discriminate H6.
           ++ replace (LT (var 2) (natToTerm (codePrf _ _ x1))) 
                with
                (substituteFormula LNN (LT (var 2) (var 1)) 1 
                   (natToTerm (codePrf _ _ x1))).
              ** rewrite <- (subFormulaAnd LNN).
                 apply impE with
                   (existH 2
                      (substituteFormula LNN
                         (fol.andH LNN (LT (var 2) (var 1))
                            (substituteFormula LNN
                               (substituteFormula LNN codeSysPrfNot 1 (var 2)) 0
                               (natToTerm (codeFormula x)))) 1 
                         (natToTerm (codePrf x0 x x1)))).
                 --- apply iffE1; apply sysExtend with NN.
                     +++ apply extendsNN.
                     +++ apply (reduceExist LNN).
                         *** apply closedNN.
                         *** apply (reduceSub LNN).
                             apply closedNN.
                             apply (reduceAnd LNN).
                             apply iffRefl.
                             apply (subFormulaExch LNN).
                             discriminate.
                             intros H4; simpl in H4.
                             decompose sum H4.
                             discriminate H5.
                             apply closedNatToTerm.
                 --- replace (LT (var 2) (var 1)) 
                       with
                       (substituteFormula LNN (LT (var 2) (var 1)) 0
                          (natToTerm (codeFormula x))).
                     rewrite <- (subFormulaAnd LNN).
                     +++ replace
                         (existH 2
                            (substituteFormula LNN
                               (substituteFormula LNN
                                  (fol.andH LNN (LT (var 2) (var 1))
                                     (substituteFormula LNN codeSysPrfNot 1 (var 2))) 0
                                  (natToTerm (codeFormula x))) 1 
                               (natToTerm (codePrf x0 x x1)))) 
                         with
                         (substituteFormula LNN
                            (existH 2
                               (substituteFormula LNN
                                  (fol.andH LNN (LT (var 2) (var 1))
                                     (substituteFormula LNN codeSysPrfNot 1 (var 2))) 0
                                  (natToTerm (codeFormula x)))) 1 
                            (natToTerm (codePrf x0 x x1))).
                         *** replace
                             (existH 2
                                (substituteFormula LNN
                                   (fol.andH LNN (LT (var 2) (var 1))
                                      (substituteFormula LNN codeSysPrfNot 1 (var 2))) 0
                                   (natToTerm (codeFormula x)))) with
                             (substituteFormula LNN
                                (existH 2
                                   (fol.andH LNN (LT (var 2) (var 1))
                                      (substituteFormula LNN codeSysPrfNot 1 (var 2)))) 0
                                (natToTerm (codeFormula x))).
                             apply impE with
                               (substituteFormula LNN
                                  (substituteFormula LNN codeSysPrf 0 
                                     (natToTerm (codeFormula x))) 1
                                  (natToTerm (codePrf _ _ x1))).
                             repeat rewrite <- (subFormulaImp LNN).
                             apply forallE.
                             replace
                               (forallH 1
                                  (substituteFormula LNN
                                     (impH codeSysPrf
                                        (existH 2
                                           (fol.andH LNN (LT (var 2) (var 1))
                                              (substituteFormula LNN codeSysPrfNot 1 
                                                 (var 2))))) 0
                                     (natToTerm (codeFormula x)))) 
                               with
                               (substituteFormula LNN
                                  (forallH 1
                                     (impH codeSysPrf
                                        (existH 2
                                           (fol.andH LNN (LT (var 2) (var 1))
                                              (substituteFormula LNN codeSysPrfNot 1 
                                                 (var 2)))))) 0
                                  (natToTerm (codeFormula x))).
                             apply impE with x.
                             apply iffE1.
                             apply sysExtend with NN.
                             apply extendsNN.
                             apply H0.
                             assumption.
                             rewrite (subFormulaForall LNN).
                             induction (eq_nat_dec 1 0) as [a | b].
                             ---- discriminate a.
                             ---- induction 
                                 (In_dec eq_nat_dec 1 (freeVarTerm LNN 
                                                         (natToTerm (codeFormula x))))
                                   as [a | b0].
                                  ++++ elim (closedNatToTerm _ _ a).
                                  ++++ reflexivity.
                             ---- now apply codeSysPrfCorrect1.
                             ---- rewrite (subFormulaExist LNN).
                                  induction (eq_nat_dec 2 0) as [a | b].
                                  discriminate a.
                                  induction (In_dec eq_nat_dec 2 
                                               (freeVarTerm LNN 
                                                  (natToTerm (codeFormula x)))).
                                  elim (closedNatToTerm _ _ a).
                                  reflexivity.
                         *** rewrite (subFormulaExist LNN).
                             induction (eq_nat_dec 2 1) as [a | b]. 
                             discriminate a.
                             induction
                               (In_dec eq_nat_dec 2 (freeVarTerm LNN 
                                                       (natToTerm (codePrf x0 x x1))))
                               as [a | b0]. 
                             elim (closedNatToTerm _ _ a).
                             reflexivity.
                     +++ unfold LT; rewrite (subFormulaRelation LNN); now simpl.
              ** unfold LT; rewrite (subFormulaRelation LNN); now simpl.
        -- apply nExist.
           set
             (E :=
                nat_rec (fun _ => Formula) (equal Zero Zero)
                  (fun (n : nat) (rec : Formula) =>
                     andH
                       (notH
                          (substituteFormula LNN
                             (substituteFormula LNN codeSysPrfNot 0
                                (natToTerm (codeFormula x))) 1 (natToTerm n))) rec)
                  (codePrf x0 x x1)).
           assert (H4: forall x : nat, ~ In x (freeVarFormula LNN E)).
           { unfold E; clear H3 E; induction (codePrf x0 x x1) as [ | n IHn].
            - simpl; auto.
            - intros x2; unfold nat_rec, nat_rect; intro H3. 
              set
                (Q :=
                   (fix F (n : nat) : (fun _ : nat => Formula) n :=
                      match n with
                      | O => equal Zero Zero
                      | S n0 =>
                          (fun (n1 : nat) (rec : Formula) =>
                             andH
                               (notH
                                  (substituteFormula LNN
                                     (substituteFormula LNN codeSysPrfNot 0
                                        (natToTerm (codeFormula x))) 1 
                                     (natToTerm n1))) rec) n0 (F n0)
                      end) n).
              SimplFreeVar.
              + apply (Nat.le_ngt x2 1).
                apply freeVarCodeSysPrfN.
                * assumption.
                * lia.
              +  apply (IHn x2 H3).
           } 
           apply impE with E.
           ++ apply sysExtend with NN.
              apply extendsNN.  
              apply impI.
              apply forallI.
              **  intros [x2 [H5 H6]].
                  induction H6 as [x2 H6| x2 H6].
                  --- apply (closedNN 2); exists x2; auto.
                  --- induction H6; now apply (H4 2).
              ** apply nAnd; unfold orH, fol.orH;
                   apply impTrans with (LT (var 2) (natToTerm (codePrf x0 x x1))).
                 --- apply impI, nnE.
                     apply Axm; right; constructor.
                 --- apply impI; apply impE with E.
                     +++ apply impE with (LT (var 2) (natToTerm (codePrf x0 x x1))).
                         do 2 apply sysWeaken.
                         *** apply boundedLT.
                             intros n H5; rewrite (subFormulaImp LNN).
                             rewrite (subFormulaNot LNN).
                             apply impE with
                               (impH E
                                  (notH
                                     (substituteFormula LNN
                                        (substituteFormula LNN codeSysPrfNot 0
                                           (natToTerm (codeFormula x))) 1 
                                        (natToTerm n)))).
                             apply iffE2.
                             apply (reduceImp LNN).
                             apply (subFormulaNil LNN).
                             apply H4.
                             apply (reduceNot LNN).
                             apply (subFormulaTrans LNN).
                             intros H6; SimplFreeVar.
                             apply (Nat.le_ngt 2 1).
                             apply freeVarCodeSysPrfN.
                             assumption.
                             apply Nat.lt_succ_diag_r.
                             unfold E in |- *.
                             clear E H4 H3.
                             apply impI.
                             induction (codePrf x0 x x1).
                             elim (Nat.nlt_0_r _ H5).
                             unfold nat_rec, nat_rect;
                               set
                                 (Q :=
                                    (fix F (n1 : nat) : (fun _ : nat => Formula) n1 :=
                                       match n1 with
                                       | O => equal Zero Zero
                                       | S n2 =>
                                           (fun (n3 : nat) (rec : Formula) =>
                                              andH
                                                (notH
                                                   (substituteFormula LNN
                                                      (substituteFormula LNN 
                                                         codeSysPrfNot 0
                                                         (natToTerm (codeFormula x))) 1 
                                                      (natToTerm n3))) rec) n2 (F n2)
                                       end) n0).
                             induction (Compat815.le_lt_or_eq _ _ 
                                          (Compat815.lt_n_Sm_le _ _ H5)).
                             apply impE with Q.
                             apply sysWeaken.
                             apply impI.
                             apply (IHn0 H3).
                             eapply andE2.
                             apply Axm; right; constructor.
                             rewrite H3.
                             eapply andE1.
                             apply Axm; right; constructor.
                         *** apply Axm; right; constructor.
                     +++ apply Axm; left; right; constructor.
           ++ unfold E in |- *; clear H4 E.
              induction (codePrf x0 x x1) as [ | n IHn].
              ** simpl; apply eqRefl.
              ** simpl; apply andI.
                 induction
                   (eq_nat_dec
                      (checkPrf LNN codeLNTFunction codeLNNRelation 
                         codeArityLNTF codeArityLNNR
                         (codeFormula (notH x)) n) 0) as [a | b].
                 --- unfold codeSysPrfNot.
                     apply codeSysPrfNCorrect3.
                     intros A0 p H4; rewrite H4 in a.
                     rewrite
                       (checkPrfCorrect1 LNN codeLNTFunction codeLNNRelation 
                          codeArityLNTF
                          codeArityLNNR codeArityLNTFIsCorrect1 
                          codeArityLNNRIsCorrect1)
                       in a; discriminate a.
                 --- decompose record
                       (checkPrfCorrect2 LNN codeLNTFunction codeLNNRelation 
                          codeArityLNTF
                          codeArityLNNR codeArityLNTFIsCorrect1 
                          codeArityLNTFIsCorrect2
                          codeArityLNNRIsCorrect1 
                          codeArityLNNRIsCorrect2 codeLNTFunctionInj
                          codeLNNRelationInj _ _ b).
                     rewrite <- H6.
                     assert (H4: x2 = notH x).
                     { eapply codeFormulaInj.
                       - apply codeLNTFunctionInj.
                       - apply codeLNNRelationInj.
                       - assumption.
                     } 
                     cut (code.codePrf LNN codeLNTFunction codeLNNRelation x3 x2 x4 = n).
                     +++ generalize x4; clear H6 x4; rewrite H4.
                         intros x4 H6; apply codeSysPrfNCorrect2.
                         eapply H3.
                         apply Nat.lt_lt_succ_r.
                         rewrite <- H6.
                         apply Nat.lt_succ_diag_r.
                     +++ assumption.
                 --- apply IHn; intros B q H4.
                     eapply H3.
                     apply Nat.lt_lt_succ_r.
                     apply H4.
    + unfold Inconsistent; intros f.
      elim H; intros x0 [x1 H2].
      induction (searchProof decide _ x _ x1) as [H3 | H3].
      * decompose record H3.
        apply contradiction with x.
        -- exists x2, x3; assumption.
        -- assumption.
      * apply
          contradiction
          with
          (substituteFormula LNN A 0
             (natToTermLNN (code.codeFormula LNN codeLNTFunction codeLNNRelation x))).
        -- unfold A; rewrite (subFormulaForall LNN).
           induction (eq_nat_dec 1 0) as [a | b].
           ++ discriminate a.
           ++ induction
               (In_dec eq_nat_dec 1
                  (freeVarTerm LNN
                     (natToTermLNN (code.codeFormula LNN codeLNTFunction 
                                      codeLNNRelation x)))) as [a | b0].
              ** elim (closedNatToTerm _ _ a).
              ** clear b0 b.
                 set
                   (E :=
                      nat_rec (fun _ => Formula) (equal Zero Zero)
                        (fun (n : nat) (rec : Formula) =>
                           andH
                             (notH
                                (substituteFormula LNN
                                   (substituteFormula LNN codeSysPrf 0 
                                      (natToTerm (codeFormula x)))
                                   1 (natToTerm n))) rec) (S (codePrf _ _ x1))). 
                 assert (H4: forall x : nat, ~ In x (freeVarFormula LNN E)).
                 { unfold E; clear H3 E.
                   induction (S (codePrf x0 (notH x) x1)).
                   - simpl; auto.
                   - intros x2; unfold nat_rec, nat_rect; intros H3.
                     SimplFreeVar.
                     + apply (Compat815.le_not_lt x2 1).
                       * apply
                           (freeVarCodeSysPrf LNN codeLNTFunction
                              codeLNNRelation codeArityLNTF
                              codeArityLNNR codeArityLNTFIsPR 
                              codeArityLNNRIsPR repT v0 freeVarRepT).
                         apply H4.
                       * destruct x2 as [| n0].
                         -- elim H6; reflexivity.
                         -- destruct n0.  
                            ++ elim H5; reflexivity.
                            ++ apply Compat815.lt_n_S.
                               apply Nat.lt_0_succ.
                     + apply (IHn _ H3).
                 } 
                 apply impE with E.
                 --- set
                     (G :=
                        substituteFormula LNN
                          (substituteFormula LNN codeSysPrfNot 0 
                             (natToTerm (codeFormula x))) 1
                          (natToTerm (codePrf x0 (notH x) x1))).
                     apply impE with G.
                     +++ apply sysExtend with NN.
                         *** assumption.
                         *** repeat apply impI; apply forallI.
                             unfold not in |- *; intros [x2 [H5 H6]].
                             induction H6 as [x2 H6| x2 H6].
                             induction H6 as [x2 H6| x2 H6].
                             apply (closedNN 1).
                             exists x2.
                             auto.
                             induction H6.
                             unfold G in H5.
                             SimplFreeVar.
                             induction H6.
                             apply (H4 _ H5).
                             rewrite (subFormulaImp LNN).
                             rewrite (subFormulaExist LNN).
                             induction (eq_nat_dec 2 0) as [a | b].
                             discriminate a.
                             induction
                               (In_dec eq_nat_dec 2
                                  (freeVarTerm LNN
                                     (natToTermLNN 
                                        (code.codeFormula LNN 
                                           codeLNTFunction codeLNNRelation x)))).
                             elim (closedNatToTerm _ _ a).
                             clear b0 b.
                             rewrite (subFormulaAnd LNN).
                             replace
                               (substituteFormula LNN (LT (var 2) (var 1)) 0
                                  (natToTermLNN 
                                     (code.codeFormula LNN 
                                        codeLNTFunction codeLNNRelation x)))
                               with
                               (LT (var 2) (var 1)).
                             apply orE with
                               (orH (LT (var 1) (natToTerm (codePrf x0 (notH x) x1)))
                                  (equal (var 1) (natToTerm (codePrf x0 (notH x) x1))))
                               (LT (natToTerm (codePrf x0 (notH x) x1)) (var 1)).
                             repeat simple apply sysWeaken.
                             apply impE with
                               (orH (LT (var 1) (natToTerm (codePrf x0 (notH x) x1)))
                                  (orH (equal (var 1) 
                                          (natToTerm (codePrf x0 (notH x) x1)))
                                     (LT (natToTerm (codePrf x0 (notH x) x1))
                                        (var 1)))).
                             apply impI.
                             apply orSys.
                             apply orI1.
                             apply orI1.
                             apply Axm; right; constructor.
                             apply orSys.
                             apply orI1.
                             apply orI2.
                             apply Axm; right; constructor.
                             apply orI2.
                             apply Axm; right; constructor.
                             apply nn9.
                             apply impI.
                             apply impE with G.
                             apply impE with E.
                             apply impE with (LT (var 1) 
                                                (natToTerm
                                                   (S (codePrf x0 (notH x) x1)))).
                             repeat simple apply sysWeaken.
                             apply boundedLT.
                             intros n H5; repeat apply impE.
                             repeat rewrite (subFormulaImp LNN).
                             repeat apply impI.
                             fold codeFormula.
                             apply
                               contradiction
                               with
                               (substituteFormula LNN
                                  (substituteFormula LNN codeSysPrf 0 
                                     (natToTermLNN (codeFormula x))) 1
                                  (natToTerm n)).
                             apply Axm; right; constructor.
                             apply sysWeaken.
                             apply impE with E.
                             repeat simple apply sysWeaken.
                             apply impI.
                             clear H3 H4. 
                             induction (S (codePrf x0 (notH x) x1)).
                             elim (Nat.nlt_0_r _ H5).
                             induction (Compat815.le_lt_or_eq _ _ 
                                          (Compat815.lt_n_Sm_le _ _ H5)).
                             unfold E; 
                               apply impE with
                               (nat_rec (fun _ : nat => Formula) (equal Zero Zero)
                                  (fun (n : nat) (rec : Formula) =>
                                     andH
                                       (notH
                                          (substituteFormula LNN
                                             (substituteFormula LNN codeSysPrf 0
                                                (natToTerm (codeFormula x))) 1 
                                             (natToTerm n))) rec) n0).
                             apply sysWeaken.
                             repeat apply impI.
                             apply IHn0.
                             assumption.
                             simpl; eapply andE2.
                             apply Axm; right; constructor.
                             unfold E; simpl; rewrite H3.
                             eapply andE1.
                             apply Axm; right; constructor.
                             apply impE with (substituteFormula LNN E 1 (natToTerm n)).
                             apply iffE1.
                             apply (subFormulaNil LNN).
                             apply H4.
                             apply Axm; left; right; constructor.
                             apply impE with
                               (orH (LT (var 1) (natToTerm (codePrf x0 (notH x) x1)))
                                  (equal (var 1) (natToTerm (codePrf x0 (notH x) x1)))).
                             repeat simple apply sysWeaken.
                             simpl; apply nnPlusNotNeeded.
                             apply Axm; right; constructor.
                             apply Axm; left; right; constructor.
                             apply Axm; do 2 left; right; constructor.
                             repeat apply impI.
                             apply sysWeaken.
                             apply existI with (natToTerm (codePrf x0 (notH x) x1)).
                             rewrite (subFormulaAnd LNN).
                             apply andI.
                             unfold LT in |- *.
                             rewrite (subFormulaRelation LNN).
                             simpl in |- *.
                             apply Axm; right; constructor.
                             apply sysWeaken.
                             apply sysWeaken.
                             apply impE with
                               (substituteFormula LNN
                                  (substituteFormula LNN codeSysPrfNot 0 
                                     (natToTerm (codeFormula x))) 1
                                  (natToTerm (codePrf x0 (notH x) x1))).
                             apply sysWeaken.
                             apply iffE2.
                             fold codeFormula; 
                               apply iffTrans with
                               (substituteFormula LNN
                                  (substituteFormula LNN
                                     (substituteFormula LNN codeSysPrfNot 0
                                        (natToTermLNN (codeFormula x))) 1 (var 2)) 2
                                  (natToTerm (codePrf x0 (notH x) x1))).
                             repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
                             apply (subFormulaExch LNN).
                             discriminate.
                             unfold not in |- *; intros; SimplFreeVar.
                             discriminate H6.
                             apply closedNatToTerm.
                             apply (subFormulaTrans LNN).
                             intros H5; SimplFreeVar.
                             apply (Compat815.le_not_lt 2 1).
                             apply freeVarCodeSysPrfN.
                             assumption.
                             apply Nat.lt_succ_diag_r.
                             apply Axm; right; constructor.
                             unfold LT; rewrite (subFormulaRelation LNN).
                             reflexivity.
                     +++ unfold G; now apply codeSysPrfNCorrect1.
                 --- clear H4; unfold E; clear E.
                     induction (S (codePrf x0 (notH x) x1)) as [| n IHn].
                     +++ simpl; apply eqRefl.
                     +++ simpl; apply andI.
                         induction
                           (eq_nat_dec
                              (checkPrf LNN codeLNTFunction 
                                 codeLNNRelation codeArityLNTF codeArityLNNR
                                 (codeFormula x) n) 0) as [a | b]. 
                         *** unfold codeSysPrf, codeFormula; apply codeSysPrfCorrect3.
                             intros A0 p H4; rewrite H4 in a.
                             rewrite
                               (checkPrfCorrect1 LNN codeLNTFunction 
                                  codeLNNRelation codeArityLNTF
                                  codeArityLNNR codeArityLNTFIsCorrect1 
                                  codeArityLNNRIsCorrect1)
                               in a.
                             discriminate a.
                         *** decompose record
                               (checkPrfCorrect2 LNN codeLNTFunction 
                                  codeLNNRelation codeArityLNTF
                                  codeArityLNNR codeArityLNTFIsCorrect1 
                                  codeArityLNTFIsCorrect2
                                  codeArityLNNRIsCorrect1 codeArityLNNRIsCorrect2 
                                  codeLNTFunctionInj
                                  codeLNNRelationInj _ _ b).
                             rewrite <- H6.
                             assert (H4: x2 = x).
                             { eapply (codeFormulaInj LNN).
                               apply codeLNTFunctionInj.
                               apply codeLNNRelationInj.
                               assumption.
                             } 
                             rewrite <- H4.
                             apply codeSysPrfCorrect2.
                             rewrite <- H4 in H3.
                             apply H3 with x4.
                             rewrite <- H6.
                             apply Nat.lt_succ_diag_r.
                         *** apply IHn.
                             intros B q H4; eapply H3.
                             apply Nat.lt_lt_succ_r.
                             apply H4.
        -- apply impE with (notH x).
           +++ apply cp2.
               apply iffE2.
               apply sysExtend with NN.
               *** apply extendsNN.
               *** assumption.
           +++ assumption.
Qed.

End Rosser's_Incompleteness.

Definition RepresentsInSelf (T:System) := 
  exists rep:Formula, exists v:nat,
    (forall x : nat, In x (freeVarFormula LNN rep) -> x = v)  /\
      (forall f : Formula,
          mem Formula T f ->
          SysPrf T (substituteFormula LNN rep v (natToTerm (codeFormula f)))) /\
      (forall f : Formula,
          ~ mem Formula T f ->
          SysPrf T
            (notH (substituteFormula LNN rep v (natToTerm (codeFormula f))))).

Definition DecidableSet (A:_)(s:Ensemble A) :=
  (forall x : A,
      mem A s x \/
        ~ mem A s x).

Theorem Incompleteness :
  forall T : System,
    Included Formula NN T ->
    RepresentsInSelf T ->
    DecidableSet Formula T ->
    exists f : Formula,
      (Sentence f) /\
        (SysPrf T f \/ SysPrf T (notH f) -> Inconsistent LNN T).
Proof.
  intros T H H0 H1; repeat induction H0.
  apply Rosser'sIncompleteness with x x0; auto; tauto.
Qed.

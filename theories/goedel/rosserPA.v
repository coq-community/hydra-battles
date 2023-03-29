From Coq Require Import Ensembles.
From Coq Require Import List.
From Coq Require Import Arith Lia.
From hydras.Ackermann Require Import folProp.
From hydras.Ackermann Require Import folProof.
From hydras.Ackermann Require Import folReplace.
From hydras.Ackermann Require Import folLogic3.
From hydras.Ackermann Require Import subProp.
From hydras.Ackermann Require Import ListExt.
From hydras.Ackermann Require Import NNtheory.
From hydras.Ackermann Require Import NN2PA.
From Goedel Require Import fixPoint.
From Goedel Require Import codeSysPrf.
From hydras.Ackermann Require Import PAtheory.
From hydras.Ackermann Require Import code.
From Goedel Require Import PRrepresentable.
From hydras.Ackermann Require Import expressible.
From hydras.Ackermann Require Import checkPrf.
From hydras.Ackermann Require Import codeNatToTerm.
From hydras Require Import Compat815.

Section Rosser's_Incompleteness.

  Definition codeFormula := codeFormula LNT codeLNTFunction codeLNTRelation.

  Variable T : System.
  Definition T' : fol.System LNN :=
    Union _ NN
      (fun x : fol.Formula LNN => mem _ T (LNN2LNT_formula x)).

Lemma extendsNN : Included _ NN T'.
Proof. intros x H; now left. Qed.

Hypothesis extendsPA : Included _ PA T.

Variable repT : Formula.
Variable v0 : nat.
Hypothesis
  freeVarRepT : forall v : nat, In v (freeVarFormula LNT repT) -> v = v0.
Hypothesis
  expressT1 :
    forall f : Formula,
    mem _ T f ->
    SysPrf T (substituteFormula LNT repT v0 (natToTerm (codeFormula f))).
Hypothesis
  expressT2 :
    forall f : Formula,
    ~ mem _ T f ->
    SysPrf T
      (notH (substituteFormula LNT repT v0 (natToTerm (codeFormula f)))).

Lemma freeVarRepT' :
 forall v : nat, In v (freeVarFormula LNN (LNT2LNN_formula repT)) -> v = v0.
Proof.
  intros v H; apply freeVarRepT.
  rewrite <- (LNT2LNT_formula repT); now apply LNN2LNT_freeVarFormula2.
Qed.

Lemma Tprf2T'prf :
  forall f : Formula, SysPrf T f -> folProof.SysPrf LNN T' (LNT2LNN_formula f).
Proof.
  intros f H; unfold T'.
  apply
    (folLogic.sysExtend LNN)
    with
    (fun x : fol.Formula LNN =>
       mem (fol.Formula LNT) T (LNN2LNT_formula x)).
  - intros x H0; right; assumption.
  - induction H as [x [x0 H]]; exists (map LNT2LNN_formula x).
    induction x0
      as
      [A|
        Axm1 Axm2 A B x0_1 Hrecx0_1 x0_0 Hrecx0_0|
        Axm A v n x0 Hrecx0|
        A B|
        A B C|
        A B|
        A v t|
        A v n|
        A B v|
      |
      |
      |
        R|
        f]; simpl.
    + exists (AXM LNN (LNT2LNN_formula A)).
      intros g H0; unfold mem, Ensembles.In.
      induction H0 as [H0| H0].
      * rewrite <- H0; rewrite LNT2LNT_formula;  apply H; auto with datatypes.
      * induction H0.
    + assert
        (H0: forall g : fol.Formula LNT, In g Axm1 -> mem (fol.Formula LNT) T g)
        by auto with datatypes. 
      assert
        (H1: forall g : fol.Formula LNT, In g Axm2 -> mem (fol.Formula LNT) T g) by
        auto with datatypes.
      induction (Hrecx0_0 H1) as [x H2].
      induction (Hrecx0_1 H0) as [x0 H3].
      clear Hrecx0_0 Hrecx0_1 H0 H1.
      assert
        (H0: map LNT2LNN_formula (Axm1 ++ Axm2) =
               map LNT2LNN_formula Axm1 ++ map LNT2LNN_formula Axm2).
      { generalize Axm1 Axm2; intros.
        induction Axm0 as [| a Axm0 HrecAxm0]; simpl in |- *.
        reflexivity.
        rewrite HrecAxm0.
        reflexivity.
      } 
      rewrite H0.
      exists
        (MP LNN (map LNT2LNN_formula Axm1) (map LNT2LNN_formula Axm2)
           (LNT2LNN_formula A) (LNT2LNN_formula B) x0 x).
      intros g H1; induction (in_app_or _ _ _ H1); auto.
    + induction (Hrecx0 H) as [x H0].
      assert (H1: ~ In v (freeVarListFormula LNN (map LNT2LNN_formula Axm))).
      { clear x0 H Hrecx0 x H0.
        intros H;  apply n; clear n.
        induction Axm as [| a Axm HrecAxm].
        - auto.
        - simpl in H |- *; apply in_or_app.
          induction (in_app_or _ _ _ H).
        + left; rewrite <- (LNT2LNT_formula a).
          now apply LNN2LNT_freeVarFormula2.
        + auto.
      } 
      exists (GEN LNN (map LNT2LNN_formula Axm) (LNT2LNN_formula A) v H1 x); auto.
    + exists (IMP1 LNN (LNT2LNN_formula A) (LNT2LNN_formula B)).
      tauto.
    + exists (IMP2 LNN (LNT2LNN_formula A) (LNT2LNN_formula B) (LNT2LNN_formula C)).
      tauto.
    + exists (CP LNN (LNT2LNN_formula A) (LNT2LNN_formula B)).
      tauto.
    + rewrite LNT2LNN_subFormula.
      exists (FA1 LNN (LNT2LNN_formula A) v (LNT2LNN_term t)).
      tauto.
    + rewrite <- LNT2LNN_freeVarFormula in n.
      exists (FA2 LNN (LNT2LNN_formula A) v n).
      tauto.
    + exists (FA3 LNN (LNT2LNN_formula A) (LNT2LNN_formula B) v).
      tauto.
    + exists (EQ1 LNN).
      tauto.
    + exists (EQ2 LNN).
      tauto.
    + exists (EQ3 LNN).
      tauto.
    + induction R.
    + induction f; simpl. 
      * exists (EQ5 LNN Languages.Plus_).
        tauto.
      * exists (EQ5 LNN Languages.Times_).
        tauto.
      * exists (EQ5 LNN Languages.Succ_).
        tauto.
      * exists (EQ5 LNN Languages.Zero_).
        tauto.
Qed.

Lemma expressT'1 :
 forall f : Formula,
 mem _ T f ->
 folProof.SysPrf LNN T'
   (substituteFormula LNN (LNT2LNN_formula repT) v0
      (natToTermLNN (codeFormula f))).
Proof.
  intros f H; rewrite <- (LNT2LNN_natToTerm (codeFormula f)), <- LNT2LNN_subFormula;
    now apply Tprf2T'prf, expressT1.
Qed.

Lemma expressT'2 :
  forall f : Formula,
    ~ mem _ T f ->
    folProof.SysPrf LNN T'
      (notH
         (substituteFormula LNN (LNT2LNN_formula repT) v0
            (natToTermLNN (codeFormula f)))).
Proof.
  intros f H; rewrite <- (LNT2LNN_natToTerm (codeFormula f)).
  rewrite <- LNT2LNN_subFormula.
  replace
    (notH 
       (LNT2LNN_formula
          (substituteFormula LNT repT v0 (natToTerm (codeFormula f))))) 
    with
    (LNT2LNN_formula
       (notH (substituteFormula LNT repT v0 (natToTerm (codeFormula f))))).
  - now apply Tprf2T'prf, expressT2.
  - reflexivity.
Qed.

Definition codeSysPrf :=
  codeSysPrf LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR
    codeArityLNTFIsPR codeArityLNTRIsPR (LNT2LNN_formula repT) v0.

Definition codeSysPrfCorrect1 :=
  codeSysPrfCorrect1 LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNTRIsPR
    codeArityLNTRIsCorrect1 T' extendsNN T (LNT2LNN_formula repT) v0
    freeVarRepT' expressT'1.

Definition codeSysPrfCorrect2 :=
  codeSysPrfCorrect2 LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNTRIsPR
    codeArityLNTRIsCorrect1 T' extendsNN T (LNT2LNN_formula repT) v0
    freeVarRepT' expressT'2.

Definition codeSysPrfCorrect3 :=
  codeSysPrfCorrect3 LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1
    codeArityLNTFIsCorrect2 codeArityLNTRIsPR codeArityLNTRIsCorrect1
    codeArityLNTRIsCorrect2 codeLNTFunctionInj codeLNTRelationInj T'
    extendsNN.
  
Definition codePrf := codePrf LNT codeLNTFunction codeLNTRelation.

Definition codeSysPrfNot :=
  codeSysPrfNot LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsPR codeArityLNTRIsPR 
    (LNT2LNN_formula repT) v0.

Definition freeVarCodeSysPrfN :=
  freeVarCodeSysPrfN LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsPR codeArityLNTRIsPR 
    (LNT2LNN_formula repT) v0 freeVarRepT'.

Definition codeSysPrfNCorrect1 :=
  codeSysPrfNCorrect1 LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNTRIsPR
    codeArityLNTRIsCorrect1 T' extendsNN T (LNT2LNN_formula repT) v0
    freeVarRepT' expressT'1.

Definition codeSysPrfNCorrect2 :=
  codeSysPrfNCorrect2 LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNTRIsPR
    codeArityLNTRIsCorrect1 T' extendsNN T (LNT2LNN_formula repT) v0
    freeVarRepT' expressT'2.

Definition codeSysPrfNCorrect3 :=
  codeSysPrfNCorrect3 LNT codeLNTFunction codeLNTRelation codeArityLNTF
    codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1
    codeArityLNTFIsCorrect2 codeArityLNTRIsPR codeArityLNTRIsCorrect1
    codeArityLNTRIsCorrect2 codeLNTFunctionInj codeLNTRelationInj T'
    extendsNN (LNT2LNN_formula repT) v0 freeVarRepT'.

Lemma decideAxioms :
  (forall x : Formula, mem _ T x \/ ~ mem _ T x) ->
  forall x : Formulas,
    (forall g : Formula, In g x -> mem _ T g) \/
      (exists g : Formula, In g x /\ ~ mem _ T g).
Proof.
  intros H x; induction x as [| a x Hrecx].
  - left; intros g H0; elim H0.
  - induction Hrecx as [H0| H0].
    + induction (H a).
      * left; intros g [H2| H2].
        -- now rewrite <- H2.
        -- auto.
      * right; exists a; split.
        -- auto with datatypes.
        -- assumption.
    + right.
      induction H0 as [x0 H0].
      exists x0.
      induction H0 as [H0 H1].
      auto with datatypes.
Qed.

Lemma searchProof :
  (forall x : Formula, mem _ T x \/ ~ mem _ T x) ->
  forall (a b : Formula) (A : Formulas) (p : Prf LNT A a),
    (exists B : Formulas,
        (exists q : Prf LNT B b,
            codePrf _ _ q < S (codePrf _ _ p) /\
              (forall x : Formula, In x B -> mem _ T x))) \/
      (forall (B : Formulas) (q : Prf LNT B b),
          codePrf _ _ q < S (codePrf _ _ p) ->
          exists g : Formula, In g B /\ ~ mem _ T g).
Proof.
  intros H a b A p.
  induction (S (codePrf A a p)).
  - right.
    intros B q H0; elim (Nat.nlt_0_r _ H0).
  - induction IHn as [H0| H0].
    + left.
      decompose record H0.
      exists x, x0; auto.
    + induction
        (eq_nat_dec
           (checkPrf LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR
              (codeFormula b) n) 0) as [a0 | b0].
      * right; intros B q H1.
        induction (Compat815.le_lt_or_eq _ _ (Compat815.lt_n_Sm_le _ _ H1)) as [H2 | H2].
        -- eauto.
        -- rewrite <- H2 in a0.
           rewrite
             (checkPrfCorrect1 LNT codeLNTFunction codeLNTRelation codeArityLNTF
                codeArityLNTR codeArityLNTFIsCorrect1 codeArityLNTRIsCorrect1)
             in a0.
           discriminate a0.
      * decompose record
          (checkPrfCorrect2 LNT codeLNTFunction codeLNTRelation codeArityLNTF
             codeArityLNTR codeArityLNTFIsCorrect1 codeArityLNTFIsCorrect2
             codeArityLNTRIsCorrect1 codeArityLNTRIsCorrect2 codeLNTFunctionInj
             codeLNTRelationInj _ _ b0).
        assert (H1: x = b).
        { eapply codeFormulaInj.
          - apply codeLNTFunctionInj.
          - apply codeLNTRelationInj.
          - assumption.
        } 
        rewrite <- H1.
        induction (decideAxioms H x0) as [H4 | H4].
        -- left; exists x0, x1.
           unfold codePrf; rewrite H3; auto.
        -- right; intros B q H5. 
           induction (Compat815.le_lt_or_eq _ _ (Compat815.lt_n_Sm_le _ _ H5)) 
             as [H6 | H6].
           ++ rewrite <- H1 in H0; eauto.
           ++ assert (H7: B = x0).
              { eapply (codePrfInjAxm LNT) with (p := q) (q := x1).
                - apply codeLNTFunctionInj.
                - apply codeLNTRelationInj.
                - transitivity n.
                  + unfold codePrf in H6.
                    apply H6.
                  + symmetry; apply H3.
              } 
              now rewrite H7.
Qed.

Lemma T'prf2Tprf :
  forall f : fol.Formula LNN,
    folProof.SysPrf LNN T' f -> SysPrf T (LNN2LNT_formula f).
Proof.
  assert
    (freeVarPA :
      forall x : Formulas,
        (forall g : fol.Formula LNT, In g x -> mem (fol.Formula LNT) PA g) ->
        forall v : nat, In v (freeVarListFormula LNT x) -> False).
  { intros x H v H0; induction x as [| a x Hrecx].
    - apply H0.
    - simpl in H0; induction (in_app_or _ _ _ H0) as [H1 | H1].
      + apply (closedPA v); exists a; auto with datatypes.
      + auto with datatypes.
  } 
  intros f [x [x0 H]]; unfold SysPrf, folProof.SysPrf.
  assert
    (H0: exists Axm : fol.Formulas LNT,
        (forall v : nat,
            In v (freeVarListFormula _ Axm) -> In v (freeVarListFormula _ x)) /\
          ex
            (fun _ : Prf LNT Axm (LNN2LNT_formula f) =>
               forall g : fol.Formula LNT,
                 In g Axm -> mem (fol.Formula LNT) T g)).
  { induction x0
      as
      [A|
        Axm1 Axm2 A B x0_1 Hrecx0_1 x0_0 Hrecx0_0|
        Axm A v n x0 Hrecx0|
        A B|
        A B C|
        A B|
        A v t|
        A v n|
        A B v|
      |
      |
      |
        R|
        f]; simpl.
    - assert (H0: mem (fol.Formula LNN) T' A) by auto with datatypes.
      repeat induction H0.
      + exists (PA1 :: nil); split.
        * auto.
        * exists (AXM _ PA1); intros g H0.
          apply extendsPA.
          induction H0 as [H0| H0].
          -- rewrite <- H0.
             repeat (right; constructor) || left.
          -- elim H0.
      + exists (PA2 :: nil); split.
        * auto.
        * exists (AXM _ PA2); intros g H0; apply extendsPA.
          induction H0 as [H0| H0].
          -- rewrite <- H0.
             repeat (right; constructor) || left.
          -- elim H0.
      + exists (PA3 :: nil); split.
        * auto.
        * exists (AXM _ PA3); intros g H0; apply extendsPA.
          induction H0 as [H0| H0].
          -- rewrite <- H0; repeat (right; constructor) || left.
          -- elim H0.
      + exists (PA4 :: nil); split.
        * auto.
        * exists (AXM _ PA4); intros g H0; apply extendsPA.
          induction H0 as [H0| H0].
          -- rewrite <- H0.
             repeat (right; constructor) || left.
          -- elim H0.
      + exists (PA5 :: nil); split.
        * auto.
        * exists (AXM _ PA5); intros g H0; apply extendsPA.
          induction H0 as [H0| H0].
          -- rewrite <- H0.
             repeat (right; constructor) || left.
          -- elim H0.
      + exists (PA6 :: nil); split.
        * auto.
        * exists (AXM _ PA6); intros g H0; apply extendsPA.
          induction H0 as [H0| H0].
          -- rewrite <- H0; repeat (right; constructor) || left.
          -- elim H0.
      + assert (H0: SysPrf PA (LNN2LNT_formula NN7)) by apply NN72PA.
        induction H0 as [x [x0 H0]]; exists x; split.
        * intros v H1; apply (freeVarPA x H0 v H1).
        * exists x0; intros g H1.
          apply extendsPA.
          fold mem; auto.
      + assert (H0: SysPrf PA (LNN2LNT_formula NN8)) by apply NN82PA.
        induction H0 as [x [x0 H0]]; exists x; split.
        intros v H1; apply (freeVarPA x H0 v H1).
        exists x0; intros g H1.
        apply extendsPA.
        fold mem; auto.
      + assert (H0:SysPrf PA (LNN2LNT_formula NN9)) by apply NN92PA.
        induction H0 as [x [x0 H0]]; exists x; split.
        intros v H1; apply (freeVarPA x H0 v H1).
        exists x0; intros g H1; apply extendsPA.
        fold mem; auto.
      + exists (LNN2LNT_formula x :: nil); split.
        * simpl; repeat rewrite <- app_nil_end.
          apply (LNN2LNT_freeVarFormula1 x).
        * exists (AXM _ (LNN2LNT_formula x)).
          intros g H1; induction H1 as [H1| H1].
          -- unfold mem, Ensembles.In in H0.
             rewrite H1 in H0.
             apply H0.
          -- elim H1.
    - assert
        (H0: forall g : fol.Formula LNN,
            In g Axm1 -> mem (fol.Formula LNN) T' g) by auto with datatypes.
      assert
        (H1: forall g : fol.Formula LNN,
            In g Axm2 -> mem (fol.Formula LNN) T' g) by auto with datatypes.
      induction (Hrecx0_1 H0) as [x H2].
      induction (Hrecx0_0 H1) as [x0 H3].
      induction H2 as [H2 H4].
      induction H3 as [H3 H5].
      induction H4 as [x1 H4].
      induction H5 as [x2 H5].
      clear Hrecx0_1 H0 Hrecx0_0 H1.
      exists (x ++ x0); split.
      + repeat rewrite freeVarListFormulaApp.
        intros v H0; induction (in_app_or _ _ _ H0); auto with datatypes.
      + simpl in x1; exists (MP _ _ _ _ _ x1 x2).
        intros g H0; induction (in_app_or _ _ _ H0); auto.
    - assert
        (H0: forall g : fol.Formula LNN, In g Axm -> mem (fol.Formula LNN) T' g) by auto. 
      induction (Hrecx0 H0) as [x H1].
      clear Hrecx0 H0.
      induction H1 as [H0 H1].
      induction H1 as [x1 H1].
      exists x; split.
      + assumption.
      + assert (H2: ~ In v (freeVarListFormula LNT x)) by auto.
        exists (GEN _ _ _ _ H2 x1); assumption.
    - exists (nil (A:=Formula)); split.
      + auto.
      + exists (IMP1 _ (LNN2LNT_formula A) (LNN2LNT_formula B)).
        simpl; tauto.
    - exists (nil (A:=Formula)); split.
      + auto.
      + exists (IMP2 _ (LNN2LNT_formula A) (LNN2LNT_formula B) (LNN2LNT_formula C)).
        simpl; tauto.
    - exists (nil (A:=Formula)); split.
      + auto.
      + exists (CP _ (LNN2LNT_formula A) (LNN2LNT_formula B)).
        simpl; tauto.
    - exists (nil (A:=Formula)); split.
      + auto.
      + assert
          (H0: SysPrf (Empty_set _)
                 (impH (forallH v (LNN2LNT_formula A))
                    (LNN2LNT_formula (substituteFormula LNN A v t)))).
        { apply
            impTrans with (substituteFormula LNT (LNN2LNT_formula A) v (LNN2LNT_term t)).
          apply impI.
          apply forallE.
          apply Axm; right; constructor.
          apply iffE2.
          apply LNN2LNT_subFormula.
        } 
        induction H0 as [x [x0 H0]].
        induction x as [| a x Hrecx].
        * exists x0; simpl; tauto.
        * assert (H1: mem (fol.Formula LNT) (Empty_set (fol.Formula LNT)) a) by
            auto with datatypes.
          induction H1.
    - exists (nil (A:=Formula)); split.
      + auto.
      + assert (H0: ~ In v (freeVarFormula LNT (LNN2LNT_formula A))).
        { intros H0; apply n.
          apply LNN2LNT_freeVarFormula1.
          assumption.
        } 
        exists (FA2 _ (LNN2LNT_formula A) v H0); simpl; tauto.
    - exists (nil (A:=Formula)); split.
      + auto.
      + exists (FA3 _ (LNN2LNT_formula A) (LNN2LNT_formula B) v).
        simpl; tauto.
    - exists (nil (A:=Formula)); split.
      + auto.
      + exists (EQ1 LNT); simpl; tauto.
    - exists (nil (A:=Formula)); split.
      + auto.
      + exists (EQ2 LNT); simpl; tauto.
    - exists (nil (A:=Formula)); split.
      + auto.
      + exists (EQ3 LNT); simpl; tauto.
    - assert (H0: SysPrf (Empty_set Formula) (LNN2LNT_formula (AxmEq4 LNN R))).
      { apply translateProof with (Empty_set (fol.Formula LNN)).
        unfold ClosedSystem in |- *.
        intros v f H0; induction H0.
        - intros f H0; induction H0.
        - exists (nil (A:=fol.Formula LNN)).
          exists (EQ4 LNN R).
          simpl; tauto.
      } 
      induction H0 as [x [x0 H0]].
      exists x; split.
      + intros v H1; induction (In_freeVarListFormulaE _ _ _ H1) as [x1 [H2 H3]].
        assert (H4: mem (fol.Formula LNT) (Empty_set Formula) x1) by auto. 
        induction H4.
      + exists x0; intros g H1.
        assert (H2: mem (fol.Formula LNT) (Empty_set Formula) g) by auto.
        induction H2.
    - assert (H0: SysPrf (Empty_set Formula) (LNN2LNT_formula (AxmEq5 LNN f))).
      { apply translateProof with (Empty_set (fol.Formula LNN)).
        - unfold ClosedSystem; intros v f0 H0; induction H0.
        - intros f0 H0; induction H0.
        - exists (nil (A:=fol.Formula LNN)).
          exists (EQ5 LNN f).
          simpl; tauto.
      } 
      induction H0 as [x [x0 H0]]; exists x; split.
      + intros v H1; induction (In_freeVarListFormulaE _ _ _ H1) as [x1 [H2 H3]].
        assert (H4: mem (fol.Formula LNT) (Empty_set Formula) x1) by auto. 
        induction H4.
      + exists x0.
        intros g H1.
        assert (H2: mem (fol.Formula LNT) (Empty_set Formula) g) by auto.
        induction H2.
  } 
  induction H0 as [x1 [H0 H1]]; now exists x1.
Qed.

(*To prove the strong contructive result we need the decidability of T*)

Theorem Rosser'sIncompleteness :
  (forall x : Formula, mem _ T x \/ ~ mem _ T x) ->
  exists f : Formula,
    (forall v : nat, ~ In v (freeVarFormula LNT f)) /\
      (SysPrf T f \/ SysPrf T (notH f) -> Inconsistent LNT T).
Proof.
  intros decide;
    set
      (A :=
         forallH  1
           (impH codeSysPrf
              (existH 2
                 (andH (LNN.LT (var 2) (var 1))
                    (substituteFormula LNN codeSysPrfNot 1 (var 2)))))). 
  destruct (FixPointLNT (LNN2LNT_formula A) 0) as [x [H0 H1]].
  exists x; split.
  -  intros v H; induction (H1 v) as [H2 H3].
     assert
       (H4: In v
              (List.remove  eq_nat_dec 0 (freeVarFormula LNT (LNN2LNT_formula A))))
       by (apply H2; assumption).
     cut (In v (List.remove eq_nat_dec 0 (freeVarFormula LNN A))).
     + clear H4.
       intros H4; unfold A in H4; SimplFreeVar. (* introduces H5 H6 H7 ? *)
       assert (H4: v <= 1).
       { apply
           (freeVarCodeSysPrf LNT codeLNTFunction codeLNTRelation codeArityLNTF
              codeArityLNTR codeArityLNTFIsPR codeArityLNTRIsPR 
              (LNT2LNN_formula repT) v0 freeVarRepT').
         apply H5.
       }
       * lia. 
       * assert (H4: v <= 1) by now apply freeVarCodeSysPrfN.
         lia.
     + eapply In_list_remove3.
       * apply LNN2LNT_freeVarFormula1.
         eapply in_remove, H4. 
       * eapply In_list_remove2, H4.
  - intros [H| H]; unfold Inconsistent.  
    + intros f; elim H.
      intros x0 H2; induction H2 as [x1 H2].
      induction (searchProof decide _ (notH x) _ x1).
      * decompose record H3.
        apply contradiction with x.
        -- assumption.
        -- exists x2, x3; assumption.
      * apply
          contradiction
          with
          (existH 2
             (andH
                (LNN2LNT_formula
                   (LNN.LT (var 2) (natToTermLNN (codePrf _ _ x1))))
                (substituteFormula LNT
                   (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 0
                      (natToTerm (codeFormula x))) 1 (var 2)))).
        -- apply impE with
             (existH 2
                (andH
                   (LNN2LNT_formula
                      (LNN.LT (var 2) (natToTermLNN (codePrf x0 x x1))))
                   (substituteFormula LNT
                      (substituteFormula LNT
                         (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 0
                            (natToTerm (codeFormula x))) 1 (var 2)) 1
                      (natToTerm (codePrf _ _ x1))))).
           ++ apply iffE1.
              apply sysExtend with PA.
              ** apply extendsPA.
              ** apply (reduceExist LNT).
                 --- apply closedPA.
                 --- apply (reduceAnd LNT).
                     +++ apply iffRefl.
                     +++ apply (subFormulaNil LNT).
                         intros H4; induction (freeVarSubFormula3 _ _ _ _ _ H4).
                         *** now apply (In_list_remove2 _ _ _ _ _ H5).
                         *** simpl in H5; decompose sum H5.
                             discriminate H6.
           ++ replace (LNN.LT (var 2) (natToTermLNN (codePrf _ _ x1))) 
                with
                (substituteFormula LNN (LNN.LT (var 2) (var 1)) 1
                   (natToTermLNN (codePrf _ _ x1))).
              ** apply impE with
                   (existH 2
                      (andH
                         (substituteFormula LNT
                            (LNN2LNT_formula (LNN.LT (var 2) (var 1))) 1
                            (natToTerm (codePrf x0 x x1)))
                         (substituteFormula LNT
                            (substituteFormula LNT
                               (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 0
                                  (natToTerm (codeFormula x))) 1 (var 2)) 1
                            (natToTerm (codePrf x0 x x1))))).
                 --- apply iffE1.
                     apply sysExtend with PA.
                     +++ apply extendsPA.
                     +++ apply (reduceExist LNT).
                         *** apply closedPA.
                         *** apply (reduceAnd LNT).
                             apply iffSym.
                             rewrite <- LNN2LNT_natToTerm.
                             apply LNN2LNT_subFormula.
                             apply iffRefl.
                 --- rewrite <- (subFormulaAnd LNT).
                     apply  impE  with
                       (existH 2
                          (substituteFormula LNT
                             (andH 
                                (LNN2LNT_formula (LNN.LT (var 2) 
                                                    (var 1)))
                                (substituteFormula LNT
                                   (substituteFormula LNT 
                                      (LNN2LNT_formula codeSysPrfNot) 1
                                      (var 2)) 0 (natToTerm (codeFormula x)))) 1
                             (natToTerm (codePrf x0 x x1)))).
                     +++ apply iffE1.
                         apply sysExtend with PA.
                         *** apply extendsPA.
                         *** apply (reduceExist LNT).
                             apply closedPA.
                             apply (reduceSub LNT).
                             apply closedPA.
                             apply (reduceAnd LNT).
                             apply iffRefl.
                             apply (subFormulaExch LNT).
                             discriminate.
                             intros H4; simpl in H4; decompose sum H4.
                             discriminate H5.
                             apply closedNatToTerm.
                     +++ replace (LNN.LT (var 2) (var 1)) 
                           with
                           (substituteFormula LNN 
                              (LNN.LT (var 2) (var 1)) 0
                              (natToTermLNN (codeFormula x))).
                         *** apply impE with
                               (existH 2
                                  (substituteFormula LNT
                                     (andH
                                        (substituteFormula LNT
                                           (LNN2LNT_formula 
                                              (LNN.LT (var 2) 
                                                 (var 1))) 0
                                           (natToTerm (codeFormula x)))
                                        (substituteFormula LNT
                                           (LNN2LNT_formula
                                              (substituteFormula LNN codeSysPrfNot 1 
                                                 (var 2))) 0
                                           (natToTerm (codeFormula x)))) 1
                                     (natToTerm (codePrf x0 x x1)))).
                             apply iffE1.
                             apply sysExtend with PA.
                             apply extendsPA.
                             apply (reduceExist LNT).
                             apply closedPA.
                             apply (reduceSub LNT).
                             apply closedPA.
                             apply (reduceAnd LNT).
                             apply iffSym.
                             rewrite <- LNN2LNT_natToTerm.
                             apply LNN2LNT_subFormula.
                             apply (reduceSub LNT).
                             apply closedPA.
                             replace (var 2) with (LNN2LNT_term (var 2)).
                             apply LNN2LNT_subFormula.
                             reflexivity.
                             rewrite <- (subFormulaAnd LNT).
                             replace
                               (existH 2
                                  (substituteFormula LNT
                                     (substituteFormula LNT
                                        (andH
                                           (LNN2LNT_formula 
                                              (LNN.LT (var 2) (var 1)))
                                           (LNN2LNT_formula
                                              (substituteFormula LNN 
                                                 codeSysPrfNot 1 (var 2)))) 0
                                        (natToTerm (codeFormula x))) 1 
                                     (natToTerm (codePrf x0 x x1)))) 
                               with
                               (substituteFormula LNT
                                  (existH 2
                                     (substituteFormula LNT
                                        (andH
                                           (LNN2LNT_formula 
                                              (LNN.LT (var 2) 
                                                 (var 1)))
                                           (LNN2LNT_formula
                                              (substituteFormula LNN codeSysPrfNot 1 
                                                 (var 2)))) 0
                                        (natToTerm (codeFormula x)))) 1 
                                  (natToTerm (codePrf x0 x x1))).
                             replace
                               (existH 2
                                  (substituteFormula LNT
                                     (andH (LNN2LNT_formula
                                                      (LNN.LT (var 2) 
                                                         (var 1)))
                                        (LNN2LNT_formula
                                           (substituteFormula LNN 
                                              codeSysPrfNot 1 (var 2)))) 0
                                     (natToTerm (codeFormula x)))) with
                               (substituteFormula LNT
                                  (existH 2
                                     (andH (LNN2LNT_formula
                                                      (LNN.LT (var 2) 
                                                         (var 1)))
                                        (LNN2LNT_formula
                                           (substituteFormula LNN 
                                              codeSysPrfNot 1 (var 2))))) 0
                                  (natToTerm (codeFormula x))).
                             apply
                               impE
                               with
                               (substituteFormula LNT
                                  (substituteFormula LNT
                                     (LNN2LNT_formula codeSysPrf) 0
                                     (natToTerm (codeFormula x))) 1 
                                  (natToTerm (codePrf _ _ x1))).
                             repeat rewrite <- (subFormulaImp LNT).
                             apply forallE.
                             replace
                               (forallH 1
                                  (substituteFormula LNT
                                     (impH (LNN2LNT_formula codeSysPrf)
                                        (existH 2
                                           (andH
                                              (LNN2LNT_formula 
                                                 (LNN.LT (var 2) 
                                                    (var 1)))
                                              (LNN2LNT_formula
                                                 (substituteFormula LNN 
                                                    codeSysPrfNot 1 
                                                    (var 2))))))
                                     0 (natToTerm (codeFormula x)))) 
                               with
                               (substituteFormula LNT
                                  (forallH 1
                                     (impH (LNN2LNT_formula codeSysPrf)
                                        (existH 2
                                           (andH
                                              (LNN2LNT_formula 
                                                 (LNN.LT (var 2) 
                                                    (var 1)))
                                              (LNN2LNT_formula
                                                 (substituteFormula LNN 
                                                    codeSysPrfNot 1 
                                                    (var 2)))))))
                                  0 (natToTerm (codeFormula x))).
                             apply impE with x.
                             apply iffE1.
                             apply sysExtend with PA.
                             apply extendsPA.
                             apply H0.
                             assumption.
                             rewrite (subFormulaForall LNT).
                             induction (eq_nat_dec 1 0) as [a | b].
                             ---- discriminate a.
                             ----induction 
                                 (In_dec eq_nat_dec 1 
                                    (freeVarTerm LNT (natToTerm (codeFormula x)))) 
                                 as [a | b0].
                                 ++++ elim (closedNatToTerm _ _ a).
                                 ++++ reflexivity.
                             ---- apply impE with
                                    (LNN2LNT_formula
                                       (substituteFormula LNN
                                          (substituteFormula LNN 
                                             codeSysPrf 0 
                                             (natToTermLNN (codeFormula x)))
                                          1 (natToTermLNN (codePrf x0 x x1)))).
                                  ++++ apply iffE1.
                                       apply sysExtend with PA.
                                       apply extendsPA.
                                       eapply iffTrans.
                                       **** apply LNN2LNT_subFormula.
                                       **** repeat rewrite <- LNN2LNT_natToTerm.
                                            apply (reduceSub LNT).
                                            apply closedPA.
                                            apply LNN2LNT_subFormula.
                                  ++++ apply T'prf2Tprf.
                                       apply codeSysPrfCorrect1.
                                       assumption.
                             ---- rewrite (subFormulaExist LNT).
                                  induction (eq_nat_dec 2 0) as [a | b]. 
                                  discriminate a.
                                  induction (In_dec eq_nat_dec 2 
                                               (freeVarTerm LNT 
                                                  (natToTerm (codeFormula x)))).
                                  elim (closedNatToTerm _ _ a).
                                  reflexivity.
                             ---- rewrite (subFormulaExist LNT).
                                  induction (eq_nat_dec 2 1).
                                  discriminate a.
                                  induction
                                    (In_dec eq_nat_dec 2 
                                       (freeVarTerm LNT 
                                          (natToTerm (codePrf x0 x x1)))) as [a | b0].
                                  elim (closedNatToTerm _ _ a).
                                  reflexivity.
                         *** unfold LNN.LT; rewrite (subFormulaRelation LNN).
                             simpl; reflexivity.
              ** unfold LNN.LT; rewrite (subFormulaRelation LNN).
                 simpl; reflexivity.
        -- apply nExist.
           set
             (E :=
                LNN2LNT_formula
                  (nat_rec (fun _ => fol.Formula LNN) 
                     (LNT2LNN_formula (equal Zero Zero))
                     (fun (n : nat) rec =>
                        andH
                          (notH
                             (substituteFormula LNN
                                (substituteFormula LNN codeSysPrfNot 0
                                   (natToTermLNN (codeFormula x))) 1 
                                (natToTermLNN n))) rec) (codePrf x0 x x1))). 
           assert (H4: forall x : nat, ~ In x (freeVarFormula LNT E)).
           { unfold E; clear H3 E; induction (codePrf x0 x x1).
             - simpl; auto.
             - intros x2; unfold nat_rec, nat_rect; intro H3.
               set
                 (Q :=
                    (fix F (n : nat) : (fun _ : nat => fol.Formula LNN) n :=
                       match n with
                       | O => LNT2LNN_formula (equal Zero Zero)
                       | S n0 =>
                           (fun (n1 : nat) (rec : fol.Formula LNN) =>
                             andH 
                                (notH
                                   (substituteFormula LNN
                                      (substituteFormula LNN codeSysPrfNot 0
                                         (natToTermLNN (codeFormula x))) 1 
                                      (natToTermLNN n1))) rec) n0 (F n0)
                       end) n).
               assert
                 (H4: In x2
                        (freeVarFormula LNN
                           (andH
                              (notH
                                 (substituteFormula LNN
                                    (substituteFormula LNN codeSysPrfNot 0
                                       (natToTermLNN (codeFormula x))) 1 
                                    (natToTermLNN n))) Q))) 
                 by now apply LNN2LNT_freeVarFormula1.
               clear H3; SimplFreeVar.
               ++ apply (Compat815.le_not_lt x2 1).
                 ** apply freeVarCodeSysPrfN.
                    assumption.
                 ** lia. 
               ++ rewrite <- LNT2LNN_natToTerm in H4.
                  rewrite LNT2LNN_freeVarTerm in H4.
                  apply (closedNatToTerm _ _ H4).
               ++ rewrite <- LNT2LNN_natToTerm in H4.
                  rewrite LNT2LNN_freeVarTerm in H4.
                  apply (closedNatToTerm _ _ H4).
               ++ apply (IHn x2).
                  now apply LNN2LNT_freeVarFormula2.
           } 
           apply impE with E.
           ** apply sysExtend with PA.
              --- apply extendsPA.
              --- apply impI.
                  apply forallI.
                  +++  intros [x2 [H5 H6]]; 
                         induction H6 as [x2 H6| x2 H6].
                       *** apply (closedPA 2).
                           exists x2; auto.
                       *** induction H6.
                           apply (H4 2); assumption.
                  +++ apply nAnd; unfold orH;
                        apply impTrans with
                        (LNN2LNT_formula (LNN.LT (var 2) 
                                            (natToTermLNN (codePrf x0 x x1)))).
                      *** apply impI, nnE; apply Axm; right; constructor.
                      *** apply impI; apply impE with E.
                          ---- apply impE with
                                 (LNN2LNT_formula 
                                    (LNN.LT (var 2)
                                       (natToTermLNN (codePrf x0 x x1)))).
                               do 2 apply sysWeaken.
                               apply PAboundedLT.
                               intros n H5; rewrite (subFormulaImp LNT).
                               rewrite (subFormulaNot LNT).
                               apply impE with
                                 (impH E
                                    (notH
                                       (substituteFormula LNT
                                          (substituteFormula LNT 
                                             (LNN2LNT_formula codeSysPrfNot) 0
                                             (natToTerm (codeFormula x))) 1 
                                          (natToTerm n)))).
                               apply iffE2.
                               apply (reduceImp LNT).
                               apply (subFormulaNil LNT).
                               apply H4.
                               apply (reduceNot LNT).
                               apply (subFormulaTrans LNT).
                               intros H6; SimplFreeVar.
                               apply (Compat815.le_not_lt 2 1).
                               apply freeVarCodeSysPrfN.
                               apply LNN2LNT_freeVarFormula1.
                               apply H7. 
                               apply Nat.lt_succ_diag_r.
                               unfold E; clear E H4 H3.
                               apply impI.
                               induction (codePrf x0 x x1).
                               elim (Nat.nlt_0_r _ H5).
                               unfold nat_rec, nat_rect.
                               set
                                 (Q :=
                                    (fix F (n1 : nat) : 
                                      (fun _ : nat => fol.Formula LNN) n1 :=
                                       match n1 with
                                       | O => LNT2LNN_formula (equal Zero Zero)
                                       | S n2 =>
                                           (fun (n3 : nat) (rec : fol.Formula LNN) =>
                                              andH
                                                (notH
                                                   (substituteFormula LNN
                                                      (substituteFormula LNN 
                                                         codeSysPrfNot 0
                                                         (natToTermLNN 
                                                            (codeFormula x))) 1 
                                                      (natToTermLNN n3))) rec) n2 
                                             (F n2)
                                       end) n0).
                               induction (Compat815.le_lt_or_eq _ _ 
                                            (Compat815.lt_n_Sm_le _ _ H5)).
                               apply impE with (LNN2LNT_formula Q).
                               apply sysWeaken.
                               apply impI.
                               apply (IHn0 H3).
                               rewrite LNN2LNT_and. 
                               eapply andE2.
                               apply Axm; right; constructor.
                               rewrite H3.
                               apply impE with
                                 (LNN2LNT_formula
                                    (notH
                                       (substituteFormula LNN
                                          (substituteFormula LNN codeSysPrfNot 0
                                             (natToTermLNN (codeFormula x))) 1 
                                          (natToTermLNN n0)))).
                               apply sysWeaken.
                               apply iffE1.
                               apply iffTrans with
                                 (notH
                                    (LNN2LNT_formula
                                       (substituteFormula LNN
                                          (substituteFormula LNN codeSysPrfNot 0
                                             (natToTermLNN (codeFormula x))) 1 
                                          (natToTermLNN n0)))).
                               apply iffRefl.
                               apply (reduceNot LNT).
                               rewrite <- LNN2LNT_natToTerm.
                               rewrite <- LNN2LNT_natToTerm.
                               apply
                                 iffTrans
                                 with
                                 (substituteFormula LNT
                                    (LNN2LNT_formula
                                       (substituteFormula LNN codeSysPrfNot 0
                                          (natToTermLNN (codeFormula x)))) 1
                                    (LNN2LNT_term (natToTermLNN n0))).
                               apply LNN2LNT_subFormula.
                               apply (reduceSub LNT).
                               apply closedPA.
                               apply LNN2LNT_subFormula.
                               eapply andE1.
                               rewrite LNN2LNT_and. 
                               apply Axm; right; constructor.
                               apply Axm; right; constructor.
                          ---- apply Axm; left; right; constructor.
           ** unfold E; clear H4 E; induction (codePrf x0 x x1).
              --- simpl; apply eqRefl.
              --- unfold nat_rec, nat_rect; rewrite LNN2LNT_and.
                  apply andI.
                  +++ induction
                      (eq_nat_dec
                         (checkPrf LNT codeLNTFunction 
                            codeLNTRelation codeArityLNTF 
                            codeArityLNTR
                            (codeFormula (notH x)) n) 0) as [a | b].
                      *** unfold codeSysPrfNot; apply T'prf2Tprf.
                          apply codeSysPrfNCorrect3.
                           intros A0 p H4; rewrite H4 in a.
                           rewrite
                             (checkPrfCorrect1 LNT codeLNTFunction 
                                codeLNTRelation codeArityLNTF
                                codeArityLNTR codeArityLNTFIsCorrect1 
                                codeArityLNTRIsCorrect1)
                             in a.
                           discriminate a.
                      *** decompose record
                            (checkPrfCorrect2 LNT codeLNTFunction 
                               codeLNTRelation codeArityLNTF
                               codeArityLNTR codeArityLNTFIsCorrect1 
                               codeArityLNTFIsCorrect2
                               codeArityLNTRIsCorrect1 codeArityLNTRIsCorrect2 
                               codeLNTFunctionInj
                               codeLNTRelationInj _ _ b).
                          rewrite <- H6.
                          assert (H4: x2 = notH x).
                          { eapply codeFormulaInj.
                            apply codeLNTFunctionInj.
                            apply codeLNTRelationInj.
                            assumption.
                          } 
                          cut (code.codePrf LNT codeLNTFunction 
                                 codeLNTRelation x3 x2 x4 = n).
                          ---- generalize x4; clear H6 x4; rewrite H4.
                               intros x4 H6; apply T'prf2Tprf.
                               apply codeSysPrfNCorrect2.
                               eapply H3.
                               apply Nat.lt_lt_succ_r.
                               rewrite <- H6.
                               apply Nat.lt_succ_diag_r.
                          ---- assumption.
                  +++ apply IHn; intros B q H4.
                      eapply H3.
                      apply Nat.lt_lt_succ_r.
                      apply H4.
    + unfold Inconsistent; intros f; elim H.
      intros x0 [x1 H2]; induction (searchProof decide _ x _ x1).
      * decompose record H3.
        apply contradiction with x.
        -- exists x2, x3; assumption.
        -- assumption.
      * apply contradiction with
          (substituteFormula LNT (LNN2LNT_formula A) 0
             (natToTermLNT 
                (code.codeFormula LNT codeLNTFunction codeLNTRelation x))).
        -- unfold A; replace
                       (LNN2LNT_formula
                          (forallH  1
                             (impH codeSysPrf
                                (existH 2
                                   (andH
                                      (LNN.LT (var 2) (var 1))
                                      (substituteFormula LNN codeSysPrfNot 1
                                         (var 2)))))))
             with
             (forallH 1
                (impH (LNN2LNT_formula codeSysPrf)
                   (existH 2
                      (andH (LNN2LNT_formula (LNN.LT (var 2) 
                                                (var 1)))
                         (LNN2LNT_formula
                            (substituteFormula LNN 
                               codeSysPrfNot 1 (var 2))))))).
           ++ rewrite (subFormulaForall LNT).
              induction (eq_nat_dec 1 0) as [a | b].
              ** discriminate a.
              ** induction 
                  (In_dec eq_nat_dec 1
                     (freeVarTerm LNT
                        (natToTermLNT (code.codeFormula LNT 
                                         codeLNTFunction codeLNTRelation x)))).
        --- elim (closedNatToTerm _ _ a).
        --- clear b0 b; 
              set
                (E :=
                   LNN2LNT_formula
                     (nat_rec (fun _ => fol.Formula LNN) 
                        (LNT2LNN_formula (equal Zero Zero))
                        (fun (n : nat) rec =>
                           andH 
                             (notH
                                (substituteFormula LNN
                                   (substituteFormula LNN codeSysPrf 0
                                      (natToTermLNN (codeFormula x))) 1 
                                   (natToTermLNN n))) rec) (S (codePrf _ _ x1)))).
            assert (H4: forall x : nat, ~ In x (freeVarFormula LNT E)).
            { unfold E; clear H3 E.
              induction (S (codePrf x0 (notH x) x1)).
              - simpl; auto.
              - intros x2; unfold nat_rec, nat_rect; intros H3.
                cut
                  (In x2
                     (freeVarFormula LNN
                        (andH 
                           (notH
                              (substituteFormula LNN
                                 (substituteFormula LNN codeSysPrf 0
                                    (natToTermLNN (codeFormula x))) 1 
                                 (natToTermLNN n)))
                           ((fix F (n : nat) : (fun _ : nat => fol.Formula LNN) n :=
              match n with
              | O => LNT2LNN_formula (equal Zero Zero)
              | S n0 =>
                  (fun (n1 : nat) (rec : fol.Formula LNN) =>
                   andH
                     (notH 
                        (substituteFormula LNN
                           (substituteFormula LNN codeSysPrf 0
                              (natToTermLNN (codeFormula x))) 1
                           (natToTermLNN n1))) rec) n0 
                    (F n0)
              end) n)))).
                ++ clear H3; intros H3; SimplFreeVar.
                   ** apply (Compat815.le_not_lt x2 1).
                      --- apply
                          (freeVarCodeSysPrf LNT codeLNTFunction 
                             codeLNTRelation codeArityLNTF
                             codeArityLNTR codeArityLNTFIsPR codeArityLNTRIsPR 
                             (LNT2LNN_formula repT) v0 freeVarRepT').
                          apply H4.
                      --- lia. 
                   ** rewrite <- LNT2LNN_natToTerm in H3.
                      rewrite LNT2LNN_freeVarTerm in H3.
                      apply (closedNatToTerm _ _ H3).
                   ** rewrite <- LNT2LNN_natToTerm in H3.
                      rewrite LNT2LNN_freeVarTerm in H3.
                      apply (closedNatToTerm _ _ H3).
                   ** assert
                       (H4: In x2
                              (freeVarFormula LNT
                                 (LNN2LNT_formula
                                    (nat_rec (fun _ : nat => fol.Formula LNN)
                                       (LNT2LNN_formula (equal Zero Zero))
                                       (fun (n : nat) (rec : fol.Formula LNN) =>
                                          andH
                                            (notH
                                               (substituteFormula LNN
                                                  (substituteFormula LNN codeSysPrf 0
                                                     (natToTermLNN (codeFormula x))) 
                                                  1 
                                                  (natToTermLNN n))) rec) n)))) by
                      apply LNN2LNT_freeVarFormula2, H3.
                      apply (IHn _ H4).
                ++ apply LNN2LNT_freeVarFormula1, H3.
            } 
            apply impE with E.
            +++ set
                (G :=
                   substituteFormula LNT
                     (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 0
                        (natToTerm (codeFormula x))) 1 
                     (natToTerm (codePrf x0 (notH x) x1))).
                apply impE with G.
                ***  apply sysExtend with PA.
                     assumption.
                     repeat apply impI.
                     apply forallI.
                     intros [x2 [H5 H6]].
                     induction H6 as [x2 H6| x2 H6].
                     induction H6 as [x2 H6| x2 H6].
                     apply (closedPA 1).
                     exists x2; auto.
                     induction H6.
                     unfold G in H5; SimplFreeVar.
                     induction H6.
                     apply (H4 _ H5).
                     rewrite (subFormulaImp LNT).
                     rewrite (subFormulaExist LNT).
                     induction (eq_nat_dec 2 0) as [a | b].
                     discriminate a.
                     induction
                       (In_dec eq_nat_dec 2
                          (freeVarTerm LNT
                             (natToTermLNT (code.codeFormula LNT 
                                              codeLNTFunction codeLNTRelation x))))
                       as [a | b0].
                     elim (closedNatToTerm _ _ a).
                     clear b0 b; rewrite (subFormulaAnd LNT).
                     apply impE with
                       (impH 
                          (substituteFormula LNT (LNN2LNT_formula codeSysPrf) 0
                             (natToTermLNT
                                (code.codeFormula LNT codeLNTFunction 
                                   codeLNTRelation x)))
                          (existH 2
                             (andH
                                (LNN2LNT_formula (LNN.LT (var 2) 
                                                    (var 1)))
                                (substituteFormula LNT
                                   (LNN2LNT_formula
                                      (substituteFormula LNN 
                                         codeSysPrfNot 1 (var 2))) 0
                                   (natToTermLNT
                                      (code.codeFormula LNT 
                                         codeLNTFunction codeLNTRelation x)))))).
                     repeat simple apply sysWeaken.
                     apply iffE1.
                     apply (reduceImp LNT).
                     apply iffRefl.
                     apply (reduceExist LNT).
                     apply closedPA.
                     apply (reduceAnd LNT).
                     apply  iffTrans  with
                       (LNN2LNT_formula
                          (substituteFormula LNN (LNN.LT (var 2) 
                                                    (var 1)) 0
                             (natToTermLNN
                                (code.codeFormula LNT codeLNTFunction 
                                   codeLNTRelation x)))).
                     rewrite <- LNN2LNT_iff.
                     apply NN2PA.
                     apply (folLogic.iffRefl LNN).
                     rewrite <- LNN2LNT_natToTerm.
                     apply LNN2LNT_subFormula.
                     apply iffRefl.
                     apply orE with
                       (LNN2LNT_formula
                          (orH 
                             (LNN.LT (var 1) 
                                (natToTermLNN (codePrf x0 (notH x) x1)))
                             (LNT2LNN_formula
                                (equal (var 1) 
                                   (natToTerm (codePrf x0 (notH x) x1))))))
                       (LNN2LNT_formula
                          (LNN.LT (natToTermLNN (codePrf x0 (notH x) x1))
                             (var 1))).
                     repeat simple apply sysWeaken.
                     apply
                       impE
                       with
                       (LNN2LNT_formula
                          (orH 
                             (LNN.LT (var 1) 
                                (natToTermLNN (codePrf x0 (notH x) x1)))
                             (orH
                                (LNT2LNN_formula
                                   (equal (var 1) 
                                      (natToTerm (codePrf x0 (notH x) x1))))
                                (LNN.LT (natToTermLNN (codePrf x0 (notH x) x1)) 
                                   (var 1))))).
                     repeat rewrite LNN2LNT_or.
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
                     apply NN2PA.
                     simpl; rewrite LNT2LNN_natToTerm.
                     apply nn9.
                     apply impI.
                     apply impE with G.
                     apply impE with E.
                     apply impE with
                       (LNN2LNT_formula
                          (LNN.LT (var 1) 
                             (natToTermLNN (S (codePrf x0 (notH x) x1))))).
                     repeat simple apply sysWeaken.
                     apply PAboundedLT.
                     intros n H5; repeat rewrite (subFormulaImp LNT).
                     repeat apply impI.
                     fold codeFormula;
                       apply
                         contradiction
                       with
                       (substituteFormula LNT
                          (substituteFormula LNT (LNN2LNT_formula codeSysPrf) 0
                             (natToTermLNT (codeFormula x))) 1 (natToTerm n)).
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
                     unfold E; apply impE with
                       (LNN2LNT_formula
                          (nat_rec (fun _ : nat => fol.Formula LNN)
                             (LNT2LNN_formula (equal Zero Zero))
                             (fun (n1 : nat) (rec : fol.Formula LNN) =>
                                andH 
                                  (notH
                                     (substituteFormula LNN
                                        (substituteFormula LNN codeSysPrf 0
                                           (natToTermLNN (codeFormula x))) 1 
                                        (natToTermLNN n1))) rec) n0)).
                     apply sysWeaken.
                     repeat apply impI.
                     apply IHn0.
                     assumption.
                     unfold nat_rec, nat_rect; rewrite LNN2LNT_and.
                     eapply andE2.
                     apply Axm; right; constructor.
                     unfold E, nat_rec, nat_rect; rewrite H3.
                     rewrite LNN2LNT_and.
                     apply
                       impE
                       with
                       (LNN2LNT_formula
                          (notH
                             (substituteFormula LNN
                                (substituteFormula LNN codeSysPrf 0
                                   (natToTermLNN (codeFormula x))) 1 
                                (natToTermLNN n0)))).
                     apply sysWeaken.
                     apply iffE1.
                     apply iffTrans with
                       (notH
                          (LNN2LNT_formula
                             (substituteFormula LNN
                                (substituteFormula LNN codeSysPrf 0
                                   (natToTermLNN (codeFormula x))) 1 
                                (natToTermLNN n0)))).
                     apply iffRefl.
                     apply (reduceNot LNT).
                     repeat rewrite <- LNN2LNT_natToTerm.
                     apply
                       iffTrans
                       with
                       (substituteFormula LNT
                          (LNN2LNT_formula
                             (substituteFormula LNN codeSysPrf 0 
                                (natToTermLNN (codeFormula x))))
                          1 (LNN2LNT_term (natToTermLNN n0))).
                     apply LNN2LNT_subFormula.
                     apply (reduceSub LNT).
                     apply closedPA.
                     apply LNN2LNT_subFormula.
                     eapply andE1.
                     apply Axm; right; constructor.
                     apply impE with (substituteFormula LNT E 1 (natToTerm n)).
                     apply iffE1.
                     apply (subFormulaNil LNT).
                     apply H4.
                     apply Axm; left; right; constructor.
                     apply impE with
                       (LNN2LNT_formula
                          (orH
                             (LNN.LT (var 1) 
                                (natToTermLNN (codePrf x0 (notH x) x1)))
                             (LNT2LNN_formula
                                (equal (var 1) (natToTerm 
                                                  (codePrf x0 (notH x) x1)))))).
                     repeat simple apply sysWeaken.
                     replace
                       (impH
                          (LNN2LNT_formula
                             (orH
                                (LNN.LT (var 1) 
                                   (natToTermLNN (codePrf x0 (notH x) x1)))
                                (LNT2LNN_formula
                                   (equal (var 1) 
                                      (natToTerm (codePrf x0 (notH x) x1))))))
                          (LNN2LNT_formula
                             (LNN.LT (var 1)
                                (natToTermLNN (S (codePrf x0 (notH x) x1))))))
                       with
                       (LNN2LNT_formula
                          (impH 
                             (orH 
                                (LNN.LT (var 1) 
                                   (natToTermLNN (codePrf x0 (notH x) x1)))
                                (LNT2LNN_formula
                                   (equal (var 1) (natToTerm 
                                                     (codePrf x0 (notH x) x1)))))
                             (LNN.LT (var 1) 
                                (natToTermLNN (S (codePrf x0 (notH x) x1)))))).
                     apply NN2PA.
                     simpl; rewrite LNT2LNN_natToTerm.
                     apply nnPlusNotNeeded.
                     reflexivity.
                     apply Axm; right; constructor.
                     apply Axm; left; right; constructor.
                     apply Axm; do 2 left; right; constructor.
                     repeat apply impI.
                     apply sysWeaken.
                     apply existI with (natToTerm (codePrf x0 (notH x) x1)).
                     rewrite (subFormulaAnd LNT).
                     apply andI.
                     apply impE with
                       (LNN2LNT_formula
                          (LNN.LT (natToTermLNN (codePrf x0 (notH x) x1))
                             (var 1))).
                     repeat simple apply sysWeaken.
                     apply impTrans  with
                       (LNN2LNT_formula
                          (substituteFormula LNN (LNN.LT (var 2) 
                                                    (var 1)) 2
                             (natToTermLNN (codePrf x0 (notH x) x1)))).
                     replace
                       (impH
                          (LNN2LNT_formula
                             (LNN.LT (natToTermLNN (codePrf x0 (notH x) x1))
                                (var 1)))
                          (LNN2LNT_formula
                             (substituteFormula LNN 
                                (LNN.LT (var 2) (var 1)) 2
                                (natToTermLNN (codePrf x0 (notH x) x1))))) 
                       with
                       (LNN2LNT_formula
                          (impH 
                             (LNN.LT (natToTermLNN (codePrf x0 (notH x) x1))
                                (var 1))
                             (substituteFormula LNN (LNN.LT (var 2) 
                                                       (var 1)) 2
                                (natToTermLNN (codePrf x0 (notH x) x1))))).
                     apply NN2PA.
                     unfold LNN.LT; apply (folLogic.impI LNN).
                     rewrite (subFormulaRelation LNN).
                     simpl;  apply (folLogic.Axm LNN); right; constructor.
                     reflexivity.
                     apply iffE1.
                     rewrite <- LNN2LNT_natToTerm.
                     apply LNN2LNT_subFormula.
                     apply Axm; right; constructor.
                     apply sysWeaken.
                     apply sysWeaken.
                     apply impE with
                       (substituteFormula LNT
                          (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 0
                             (natToTerm (codeFormula x))) 1 
                          (natToTerm (codePrf x0 (notH x) x1))).
                     apply sysWeaken.
                     apply iffE2.
                     fold codeFormula; 
                       apply iffTrans with
                       (substituteFormula LNT
                          (substituteFormula LNT
                             (substituteFormula LNT 
                                (LNN2LNT_formula codeSysPrfNot) 1 (var 2)) 0
                             (natToTermLNT (codeFormula x))) 2
                          (natToTerm (codePrf x0 (notH x) x1))).
                     repeat (apply (reduceSub LNT); [ apply closedPA | idtac ]).
                     replace (var 2) with (LNN2LNT_term (var 2)).
                     apply LNN2LNT_subFormula.
                     reflexivity.
                     apply iffTrans with
                       (substituteFormula LNT
                          (substituteFormula LNT
                             (substituteFormula LNT (LNN2LNT_formula codeSysPrfNot) 0
                                (natToTermLNT (codeFormula x))) 1 (var 2)) 2
                          (natToTerm (codePrf x0 (notH x) x1))).
                     repeat (apply (reduceSub LNT); [ apply closedPA | idtac ]).
                     apply (subFormulaExch LNT).
                     discriminate.
                     intros H5; SimplFreeVar.
                     discriminate H6.
                     apply closedNatToTerm.
                     apply (subFormulaTrans LNT).
                     unfold not in |- *; intros; SimplFreeVar.
                     apply (Compat815.le_not_lt 2 1).
                     apply freeVarCodeSysPrfN.
                     apply LNN2LNT_freeVarFormula1.
                     assumption.
                     apply Nat.lt_succ_diag_r.
                     apply Axm; right; constructor.
                *** unfold G; apply impE with
                      (LNN2LNT_formula
                         (substituteFormula LNN
                            (substituteFormula LNN codeSysPrfNot 0
                               (natToTermLNN (codeFormula x))) 1
                            (natToTermLNN (codePrf x0 (notH x) x1)))).
                    apply iffE1.
                    repeat rewrite <- LNN2LNT_natToTerm.
                    apply
                      iffTrans
                      with
                      (substituteFormula LNT
                         (LNN2LNT_formula
                            (substituteFormula LNN codeSysPrfNot 0
                               (natToTermLNN (codeFormula x)))) 1
                         (LNN2LNT_term (natToTermLNN (codePrf x0 (notH x) x1)))).
                    apply LNN2LNT_subFormula.
                    apply sysExtend with PA.
                    assumption.
                    apply (reduceSub LNT).
                    apply closedPA.
                    apply LNN2LNT_subFormula.
                    apply T'prf2Tprf.
                    apply codeSysPrfNCorrect1.
                    assumption.
            +++ clear H4; unfold E; clear E.
                induction (S (codePrf x0 (notH x) x1)).
                *** simpl; apply eqRefl.
                *** unfold nat_rec, nat_rect; rewrite LNN2LNT_and.
                    apply andI.
                    ---- induction
                        (eq_nat_dec
                           (checkPrf LNT codeLNTFunction codeLNTRelation 
                              codeArityLNTF codeArityLNTR
                              (codeFormula x) n) 
                           0) as [a | b].
                         ++++ unfold codeSysPrf, codeFormula in |- *.
                              apply T'prf2Tprf.
                              apply codeSysPrfCorrect3.
                              intros A0 p H4; rewrite H4 in a.
                              rewrite
                                (checkPrfCorrect1 LNT codeLNTFunction 
                                   codeLNTRelation codeArityLNTF
                                   codeArityLNTR codeArityLNTFIsCorrect1 
                                   codeArityLNTRIsCorrect1)
                                in a.
                              discriminate a.
                         ++++ decompose record
                                (checkPrfCorrect2 LNT 
                                   codeLNTFunction codeLNTRelation 
                                   codeArityLNTF
                                   codeArityLNTR codeArityLNTFIsCorrect1 
                                   codeArityLNTFIsCorrect2
                                   codeArityLNTRIsCorrect1 
                                   codeArityLNTRIsCorrect2 codeLNTFunctionInj
                                   codeLNTRelationInj _ _ b).
                              rewrite <- H6.
                              assert (H4: x2 = x). 
                              {
                                eapply (codeFormulaInj LNT).
                                apply codeLNTFunctionInj.
                                apply codeLNTRelationInj.
                                assumption.
                              } 
                              rewrite <- H4.
                              apply T'prf2Tprf.
                              apply codeSysPrfCorrect2.
                              rewrite <- H4 in H3.
                              apply H3 with x4.
                              rewrite <- H6.
                              apply Nat.lt_succ_diag_r.
                    ---- apply IHn; intros B q H4; eapply H3.
                         apply Nat.lt_lt_succ_r.
                         apply H4.
           ++ reflexivity.
        -- apply impE with (notH x).
           ++ apply cp2, iffE2.
              apply sysExtend with PA.
              apply extendsPA.
              assumption.
           ++ assumption.
Qed.

End Rosser's_Incompleteness.

From hydras.Ackermann Require Import codePA.
From hydras.Ackermann Require Import PAconsistent.

Theorem PAIncomplete :
 exists f : Formula,
   (Sentence f) /\ ~(SysPrf PA f \/ SysPrf PA (notH f)).
Proof.
  assert
    (H: Expressible NN 1 codePA
          (substituteFormula LNN (primRecFormula 1 (proj1_sig codePAIsPR)) 0
             (natToTermLNN 1))).
  { apply (Representable2Expressible _ closedNN1).
    simpl.
    apply nn1.
    apply primRecRepresentable.
  }
  destruct  H as [H H0]; simpl in H0.
  assert
    (H1: exists f : Formula,
        (forall v : nat, ~ In v (freeVarFormula LNT f)) /\
          (SysPrf PA f \/ SysPrf PA (notH f) -> Inconsistent LNT PA)).
  { eapply Rosser'sIncompleteness with
      (repT := 
         LNN2LNT_formula
           (substituteFormula LNN
              (primRecFormula 1 (proj1_sig codePAIsPR)) 0
              (natToTermLNN 1)))
      (v0 := 1).
    - unfold Included; auto.
    - intros v H1; assert (H2: v <= 1 /\ v <> 0).
      { apply H.
        apply LNN2LNT_freeVarFormula1.
        apply H1.
      } 
      destruct v as [| n].
    +  induction H2 as [H2 H3].
       now elim H3.
    + destruct n.
      * reflexivity.
      * lia. 
    - intros f H1; rewrite <- LNN2LNT_natToTerm.
      eapply impE.
      + apply iffE1.
        apply LNN2LNT_subFormula.
      + apply NN2PA.
        assert
          (H2: if codePA (codeFormula f)
               then
                 LNN.SysPrf NN
                   (substituteFormula LNN
                      (substituteFormula LNN 
                         (primRecFormula 1 (proj1_sig codePAIsPR)) 0
                         (LNN.Succ LNN.Zero)) 1 (LNN.natToTerm (codeFormula f)))
               else
                 LNN.SysPrf NN
                   (notH
                      (substituteFormula LNN
                         (substituteFormula LNN (primRecFormula 1 
                                                   (proj1_sig codePAIsPR)) 0
                            (LNN.Succ LNN.Zero)) 1 
                         (LNN.natToTerm (codeFormula f))))) by  apply H0.
        clear H0.
        assert (H0: codePA (codeFormula f) = true) by now apply codePAcorrect3.
        now rewrite H0 in H2.
    - intros f H1; rewrite <- LNN2LNT_natToTerm.
      eapply impE with
        (LNN2LNT_formula
           (notH
              (substituteFormula LNN
                 (substituteFormula LNN
                    (primRecFormula 1 (proj1_sig codePAIsPR)) 0
                    (LNN.Succ LNN.Zero)) 1 (LNN.natToTerm (codeFormula f))))).
      + simpl; apply cp2.
        apply iffE2.
        apply LNN2LNT_subFormula.
      + apply NN2PA.
        assert
          (H2: if codePA (codeFormula f)
               then
                 LNN.SysPrf NN
                   (substituteFormula LNN
                      (substituteFormula LNN (primRecFormula 1 
                                                (proj1_sig codePAIsPR)) 0
                         (LNN.Succ LNN.Zero)) 1 (LNN.natToTerm (codeFormula f)))
               else
                 LNN.SysPrf NN
                   (notH
                      (substituteFormula LNN
                         (substituteFormula LNN 
                            (primRecFormula 1 (proj1_sig codePAIsPR)) 0
                            (LNN.Succ LNN.Zero)) 1 
                         (LNN.natToTerm (codeFormula f))))).
        * apply H0. 
        * clear H0.
          assert (H0: codePA (codeFormula f) = false) by 
            now apply codePAcorrect2.
          now rewrite H0 in H2.
    - apply PAdec.
  }  
  clear H H0; decompose record H1.
  exists x; split.
  - assumption.
  - intro H; unfold Inconsistent in H2.
    induction PAconsistent.
    auto.
Qed.

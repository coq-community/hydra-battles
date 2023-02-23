Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import ListExt.

Require Import folProp.
Require Import folProof.
Require Export folLogic.
Require Import subProp.
Require Import folReplace.
Require Import Arith.

Section More_Logic_Rules.

Variable L : Language.
Let Formula := Formula L.
Let Formulas := Formulas L.
Let System := System L.
Let Term := Term L.
Let Terms := Terms L.
Let var := var L.
Let apply := apply L.
Let equal := equal L.
Let atomic := atomic L.
Let orH := orH L.
Let andH := andH L.
Let existH := existH L.
Let iffH := iffH L.
Let ifThenElseH := ifThenElseH L.
Let Prf := Prf L.
Let SysPrf := SysPrf L.

Lemma rebindForall (T : System) (a b : nat) (f : Formula):
  ~ In b (freeVarFormula L (forallH a f)) ->
  SysPrf T (iffH (forallH a f) 
              (forallH b (substituteFormula L f a (var b)))).
Proof.
  intros H; eapply (sysExtend L) with (Empty_set Formula).
  - intros x H0; destruct H0.
  - apply (iffI L).
    + apply (impI L), (forallI L).
      intros [x [H0 H1]].
      destruct H1 as [x H1| x H1]; [ induction H1 | induction H1 ].
      * auto.
      * apply forallE; apply Axm; right; constructor.
    + apply (impI L), (forallI L).
      intros [x [H0 H1]] ; destruct H1 as [x H1| x H1]; 
        [induction H1 | induction H1].
     * assert (H1: In a (freeVarFormula L (substituteFormula L f a (var b))))
       by (eapply In_list_remove1; apply H0).
       induction (freeVarSubFormula3 _ _ _ _ _ H1).
       elim (In_list_remove2 _ _ _ _ _ H2).
       -- auto.
       -- elim (In_list_remove2 _ _ _ _ _ H0).
          destruct H2 as [H2| H2].
          auto.
          elim H2.
     * set (A1 := forallH b (substituteFormula L f a (var b))) in *.
       rewrite <- (subFormulaId L f a).
       apply (impE L) with
         (substituteFormula L (substituteFormula L f a (var b)) b 
            (fol.var L a)).
       -- apply (iffE1 L).
          apply (subFormulaTrans L); apply H.
       -- apply forallE, Axm; right; constructor.
Qed.

Lemma rebindExist (T : System) (a b : nat) (f : Formula):
  ~ In b (freeVarFormula L (existH a f)) ->
  SysPrf T (iffH (existH a f) (existH b (substituteFormula L f a (var b)))).
Proof.
  intro H; unfold existH, fol.existH.  
  apply (reduceNot L); eapply (iffTrans L).
  - apply (rebindForall T a b (notH f)), H. 
  - rewrite (subFormulaNot L); apply (iffRefl L).
Qed.

Lemma subSubTerm (t : Term) (v1 v2 : nat) (s1 s2 : Term):
  v1 <> v2 ->
  ~ In v1 (freeVarTerm L s2) ->
  substituteTerm L (substituteTerm L t v1 s1) v2 s2 =
    substituteTerm L 
      (substituteTerm L t v2 s2) v1 (substituteTerm L s1 v2 s2).
Proof.
  intros H H0. 
  elim t using Term_Terms_ind with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             substituteTerms L n (substituteTerms L n ts v1 s1) v2 s2 =
               substituteTerms L n (substituteTerms L n ts v2 s2) v1
                 (substituteTerm L s1 v2 s2)); simpl in |- *.
  - intros n. 
    destruct (eq_nat_dec v1 n)  as [ e | n0].
    + destruct (eq_nat_dec v2 n)  as [e0 | n0].
      * elim H; transitivity n; auto.
      * simpl in |- *; destruct (eq_nat_dec v1 n)as [e0 | n1].
        -- reflexivity.
        -- elim n1;auto.
    + simpl in |- *; destruct (eq_nat_dec v2 n) as [e | n1].
      * rewrite subTermNil; easy. 
      * simpl in |- *; destruct (eq_nat_dec v1 n) as [e | ].
        --  elim n0; auto.
        -- reflexivity.
  - intros f t0 H1;  rewrite H1; reflexivity.
  - reflexivity.
  - intros  n t0 H1 t1 H2; rewrite H1, H2; easy. 
Qed.

Lemma subSubTerms (n : nat) (ts : Terms n) (v1 v2 : nat) (s1 s2 : Term):
  v1 <> v2 ->
  ~ In v1 (freeVarTerm L s2) ->
  substituteTerms L n (substituteTerms L n ts v1 s1) v2 s2 =
    substituteTerms L n (substituteTerms L n ts v2 s2) v1
      (substituteTerm L s1 v2 s2).
Proof.
  intros H H0; induction ts as [| n t ts Hrects].
  - reflexivity.
  - simpl in |- *; rewrite Hrects, subSubTerm.
    + reflexivity.
    + assumption. 
    + assumption.
Qed.

Lemma subSubFormula (f : Formula) (v1 v2 : nat) (s1 s2 : Term):
 v1 <> v2 ->
 ~ In v1 (freeVarTerm L s2) ->
 forall T : System,
 SysPrf T
   (iffH (substituteFormula L (substituteFormula L f v1 s1) v2 s2)
      (substituteFormula L (substituteFormula L f v2 s2) v1
         (substituteTerm L s1 v2 s2))).
Proof.
  intros H H0 T; apply (sysExtend L) with (Empty_set Formula).
  - intros x H1; destruct H1.
  - elim f using Formula_depth_ind2; intros.
    + repeat rewrite (subFormulaEqual L).
      rewrite subSubTerm; auto.
      rewrite (subSubTerm t0); auto.
      apply (iffRefl L).
    + repeat rewrite (subFormulaRelation L).
      rewrite subSubTerms; auto.
      apply (iffRefl L).
    + repeat rewrite (subFormulaImp L).
      apply (reduceImp L); auto.
    + repeat rewrite (subFormulaNot L).
      apply (reduceNot L); auto.
    + set (v' :=
             newVar
               (v1
                  :: v2
                  :: freeVarFormula L (forallH v a) ++
                  freeVarTerm L s1 ++ freeVarTerm L s2)) in *.
      assert (H2: v' <> v1).
      { intro H2;
        elim
          (newVar1
             (v1
                :: v2
                :: freeVarFormula L (forallH v a) ++
                freeVarTerm L s1 ++ freeVarTerm L s2)).
        fold v' ; simpl; auto.
      } 
      assert (H3: v' <> v2).
      { intro H3; 
        elim
          (newVar1
             (v1
                :: v2
                :: freeVarFormula L (forallH v a) ++
                freeVarTerm L s1 ++ freeVarTerm L s2)).
        fold v'; simpl; auto.
      } 
      assert (H4: ~ In v' (freeVarFormula L (forallH v a))).
      { intro H4; 
        elim
          (newVar1
             (v1
                :: v2
                :: freeVarFormula L (forallH v a) ++
                freeVarTerm L s1 ++ freeVarTerm L s2)).
        fold v' ;simpl; auto with datatypes.
      } 
      assert (H5: ~ In v' (freeVarTerm L s1)).
      { intro H5; 
        elim
          (newVar1
             (v1
                :: v2
                :: freeVarFormula L (forallH v a) ++
                freeVarTerm L s1 ++ freeVarTerm L s2)).
        fold v' ;  simpl; repeat right; auto with datatypes.
      } 
      assert (H6: ~ In v' (freeVarTerm L s2)).
      { intro H6; 
          elim
            (newVar1
               (v1
                  :: v2
                  :: freeVarFormula L (forallH v a) ++
                  freeVarTerm L s1 ++ freeVarTerm L s2)).
       fold v' ; simpl;  repeat right; auto with datatypes.
     }
     apply impE with
       (iffH
          (substituteFormula L
             (substituteFormula L
                (forallH v' (substituteFormula L a v (var v'))) v1 s1) v2
             s2)
          (substituteFormula L
             (substituteFormula L
                (forallH v' (substituteFormula L a v (var v'))) v2 s2) v1
             (substituteTerm L s1 v2 s2))).
     apply (iffE2 L).
      * assert
          (H7: folProof.SysPrf L (Empty_set Formula)
                 (iffH (forallH v a)
                    (forallH v' (substituteFormula L a v (var v')))))
          by (apply rebindForall; auto).
       repeat first
       [ apply (reduceIff L)
       | apply (reduceSub L)
       | apply (notInFreeVarSys L) ]; auto.
       * assert (H7: 
                  forall (f : Formula) (x v : nat) (s : Term),
                    x <> v ->
                    ~ In x (freeVarTerm L s) ->
                    substituteFormula L (forallH x f) v s =
                      forallH x (substituteFormula L f v s)). 
         { intros f0 x v0 s H7; rewrite (subFormulaForall L).
           destruct (eq_nat_dec x v0) as [e | n0].
           - elim H7; auto.
           - destruct (In_dec eq_nat_dec x (freeVarTerm L s)) as [i | n1]. 
         + intro H8; elim H8; auto.
         + reflexivity.
     }
     repeat rewrite H7; try easy. 
     --  apply (reduceForall L).
         apply (notInFreeVarSys L).
         apply H1.
         apply eqDepth with a.
         symmetry  in |- *.
         apply subFormulaDepth.
         apply depthForall.
     --  intro H8; induction (freeVarSubTerm3 _ _ _ _ _ H8).
         elim H5; eapply In_list_remove1.
         apply H9.
         now apply H6. 
Qed.

End More_Logic_Rules.


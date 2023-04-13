Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import primRec.
Require Import cPair.
Require Import Arith.
Require Import folProp.
Require Import code.
Require Import codeList.
Require Import codeFreeVar.
Require Import extEqualNat.
Require Vector.
Require Import prLogic.
Require Import Compat815.
From Coq Require Import Lia.
Import LispAbbreviations. 

Section close.

Variable L : Language.
Variable codeF : Functions L -> nat.
Variable codeR : Relations L -> nat.

Let Formula := Formula L.
Let codeFormula := codeFormula L codeF codeR.

Definition codeCloseList : nat -> nat -> nat :=
  evalStrongRec 1
    (fun l recs f : nat =>
     switchPR l
       (cPair 3
          (cPair (car (pred l))
             (codeNth (l - S (cdr (pred l))) recs))) f).
    
Lemma codeCloseListCorrect (l : list nat) (f : Formula):
 codeCloseList (codeList l) (codeFormula f) = 
   codeFormula (closeList L l f).
Proof.
  set (g :=
         fun l recs f : nat =>
           switchPR l
             (cPair 3
                (cPair (car (pred l)) 
                   (codeNth (l - S (cdr (pred l))) recs)))
             f).
  induction l as [| a l Hrecl].
  - simpl; unfold codeCloseList, evalStrongRec in |- *; simpl.
    rewrite cPairProjections1; reflexivity.
  - simpl; unfold codeCloseList; fold g.
    assert
      (H :forall n m : nat,
          m < n ->
          extEqual 1
            (evalComposeFunc 1 1 (Vector.cons _ 
                                    (evalStrongRecHelp 1 g n) 0 (Vector.nil _))
               (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 g m)).
    { intros n m H; apply (evalStrongRecHelp2 1); assumption. } 
    simpl in H; unfold evalStrongRec in |- *.
    unfold evalComposeFunc, evalOneParamList, evalList.
    rewrite computeEvalStrongRecHelp.
    unfold compose2, evalComposeFunc, evalOneParamList, evalList in |- *.
    unfold g at 1; rewrite H.
    + simpl; repeat rewrite cPairProjections1 || rewrite cPairProjections2.
      rewrite <- Hrecl; reflexivity.
    + simpl; apply Compat815.le_lt_n_Sm, cPairLe2A.
Qed.

Lemma codeCloseListIsPR : isPR 2 codeCloseList.
Proof.
  unfold codeCloseList; apply evalStrongRecIsPR.
  apply compose3_3IsPR with
    (f1 := fun l recs f : nat => l)
    (f2 := fun l recs f : nat =>
             cPair 3
               (cPair (car (pred l))
                  (codeNth (l - S (cdr (pred l))) recs)))
    (f3 := fun l recs f : nat => f).
  - apply pi1_3IsPR.
  - apply filter110IsPR with
      (g := fun l recs : nat =>
              cPair 3
                (cPair (car (pred l))
                   (codeNth (l - S (cdr (pred l))) recs))).
    apply compose2_2IsPR with
      (f := fun l recs : nat => 3)
      (g := fun l recs : nat =>
              cPair (car (pred l))
                (codeNth (l - S (cdr (pred l))) recs)).
    + apply filter10IsPR with (g := fun _ : nat => 3).
      apply const1_NIsPR.
    + apply compose2_2IsPR with
        (f := fun l recs : nat => car (pred l))
        (g := fun l recs : nat => codeNth (l - S (cdr (pred l))) recs).
      * apply filter10IsPR with (g := fun l : nat => car (pred l)).
        apply compose1_1IsPR.
        -- apply predIsPR.
        -- apply cPairPi1IsPR.
      * apply callIsPR with (g := fun l : nat => cdr (pred l)).
        apply compose1_1IsPR.
        -- apply predIsPR.
        -- apply cPairPi2IsPR.
      * apply cPairIsPR.
    + apply cPairIsPR.
  - apply pi3_3IsPR.
  - apply switchIsPR.
Qed.

Definition codeClose (f : nat) : nat :=
  codeCloseList (codeNoDup (codeFreeVarFormula f)) f.

Lemma codeCloseCorrect (f : Formula) :
  codeClose (codeFormula f) = codeFormula (close L f).
Proof.
  unfold close, codeClose, codeFormula;
    rewrite codeFreeVarFormulaCorrect, codeNoDupCorrect.
  apply codeCloseListCorrect.
Qed.

Lemma codeCloseIsPR : isPR 1 codeClose.
Proof.
  unfold codeClose;
    apply compose1_2IsPR with
    (f := fun f : nat => codeNoDup (codeFreeVarFormula f))
    (f' := fun f : nat => f).
  - apply compose1_1IsPR.
    + apply codeFreeVarFormulaIsPR.
    + apply codeNoDupIsPR.
  - apply idIsPR.
  - apply codeCloseListIsPR.
Qed.

End close.

Require Import PA.
Require Import codeSubFormula.

Section Code_PA.

Let codeTerm := codeTerm LNT codeLNTFunction.
Let codeFormula := codeFormula LNT codeLNTFunction codeLNTRelation.
Let codeFormulaInj :=
  codeFormulaInj LNT codeLNTFunction codeLNTRelation codeLNTFunctionInj
    codeLNTRelationInj.

Definition codeOpen : nat -> nat :=
  evalStrongRec 0
    (fun f recs : nat =>
     switchPR (car f)
       (switchPR (pred (car f))
          (switchPR (pred (pred (car f)))
             (switchPR (pred (pred (pred (car f)))) f
                (codeNth (f - S (cdr (cdr f))) recs)) f) f) f).

Lemma codeOpenCorrect (f : Formula):
  codeOpen (codeFormula f) = codeFormula (open f).
Proof.
  unfold codeOpen, open;
    set (g :=
           fun f recs : nat =>
             switchPR (car f)
               (switchPR (pred (car f))
                  (switchPR (pred (pred (car f)))
                     (switchPR (pred (pred (pred (car f)))) f
                        (codeNth (f - S (cdr (cdr f))) recs)) f) f) f).
  induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
    simpl; unfold evalStrongRec.
  - simpl ; unfold g ;
      repeat rewrite cPairProjections1 || rewrite cPairProjections2; 
      reflexivity.
  - simpl in |- *; unfold g at 1 in |- *;
      repeat rewrite cPairProjections1 || rewrite cPairProjections2; 
      reflexivity.
  - simpl in |- *; unfold g at 1 in |- *;
      repeat rewrite cPairProjections1 || rewrite cPairProjections2; 
      reflexivity.
  - simpl in |- *; unfold g at 1 in |- *;
      repeat rewrite cPairProjections1 || rewrite cPairProjections2; 
      reflexivity.
  - unfold evalComposeFunc, evalOneParamList, evalList;
      rewrite computeEvalStrongRecHelp.
    unfold compose2, evalComposeFunc, evalOneParamList, evalList.
    unfold g at 1; repeat rewrite evalStrongRecHelp1.
    unfold pred; 
      repeat rewrite cPairProjections1 || rewrite cPairProjections2.
    + simpl; apply Hrecf.
    + eapply Nat.le_lt_trans.
      * apply cPairLe2A.
      * rewrite cPairProjections2.
        apply cPairLt2.
Qed.

Lemma codeOpenIsPR : isPR 1 codeOpen.
Proof.
  unfold codeOpen; apply evalStrongRecIsPR.
  apply
    compose2_3IsPR
    with
    (f1 := fun f recs : nat => car f)
    (f2 := fun f recs : nat =>
             switchPR (pred (car f))
               (switchPR (pred (pred (car f)))
                  (switchPR (pred (pred (pred (car f)))) f
                     (codeNth (f - S (cdr (cPairPi2 f))) recs)) f) f)
    (f3 := fun f recs : nat => f).
  - apply filter10IsPR.
    apply cPairPi1IsPR.
  - apply compose2_3IsPR with
      (f1 := fun f recs : nat => pred (car f))
      (f2 := fun f recs : nat =>
               switchPR (pred (pred (car f)))
                 (switchPR (pred (pred (pred (car f)))) f
                    (codeNth (f - S (cdr (cdr f))) recs)) f)
      (f3 := fun f recs : nat => f).
    + apply filter10IsPR with (g := fun f : nat => pred (car f)).
      apply compose1_1IsPR.
      * apply cPairPi1IsPR.
      * apply predIsPR.
    + apply compose2_3IsPR with
        (f1 := fun f recs : nat => pred (pred (car f)))
        (f2 := fun f recs : nat =>
                 switchPR (pred (pred (pred (car f)))) f
                   (codeNth (f - S (cdr (cdr f))) recs))
        (f3 := fun f recs : nat => f).
      * apply filter10IsPR with 
          (g := fun f : nat => pred (pred (car f))).
        apply compose1_1IsPR with (f := fun f : nat => pred (car f)).
        -- apply compose1_1IsPR.
           ++ apply cPairPi1IsPR.
           ++ apply predIsPR.
        -- apply predIsPR.
      * apply compose2_3IsPR with
          (f1 := fun f recs : nat => pred (pred (pred (car f))))
          (f2 := fun f recs : nat => f)
          (f3 := fun f recs : nat => codeNth (f - S (cdr (cdr f))) recs).
        -- apply filter10IsPR with 
             (g := fun f : nat => pred (pred (pred (car f)))).
           apply compose1_1IsPR with 
             (f := fun f : nat => pred (pred (car f))).
           ++ apply compose1_1IsPR with 
                (f := fun f : nat => pred (car f)).
              ** apply compose1_1IsPR.
                 apply cPairPi1IsPR.
                 apply predIsPR.
              ** apply predIsPR.
           ++ apply predIsPR.
        -- apply pi1_2IsPR.
        -- apply callIsPR with (g := fun f : nat => cdr (cdr f)).
           apply compose1_1IsPR; apply cPairPi2IsPR.
        -- apply switchIsPR.
      * apply pi1_2IsPR.
      * apply switchIsPR.
    + apply pi1_2IsPR.
    + apply switchIsPR.
  - apply pi1_2IsPR.
  - apply switchIsPR.
Qed.

Definition codeInductionSchema (f : nat) : bool :=
  let n := 
    car (cdr (cddddr  (codeOpen f))) in
  let g := cdr (cdr (cddddr (codeOpen f))) in
  Nat.eqb
    (codeClose
       (codeImp (codeSubFormula g n (codeTerm Zero))
          (codeImp
             (codeForall n
                (codeImp g (codeSubFormula g n 
                              (codeTerm (Succ (var n))))))
             (codeForall n g)))) f.

Lemma codeInductionSchemaCorrect1 (f : Formula) :
 InductionSchema f -> codeInductionSchema (codeFormula f) = true.
Proof.
  intros [x [x0 H]]; unfold PA7 in H; rewrite H; clear H f.
  lazy beta delta [codeInductionSchema] in |- *.
  rewrite codeOpenCorrect;
    replace
      (open
         (close LNT
            (impH (substituteFormula LNT x x0 Zero)
               (impH
                  (forallH x0
                     (impH x 
                        (substituteFormula LNT x x0 (Succ (var x0)))))
                  (forallH x0 x))))) 
    with
    (impH (substituteFormula LNT x x0 Zero)
       (impH (forallH x0 
                (impH x (substituteFormula LNT x x0 (Succ (var x0)))))
          (forallH x0 x))).
  - replace
      (cadr (cddddr
               (codeFormula
                  (impH (substituteFormula LNT x x0 Zero)
                     (impH
                        (forallH x0
                           (impH x
                              (substituteFormula LNT x x0 
                                 (Succ (var x0)))))
                        (forallH x0 x)))))) 
      with x0.
    + replace
        (cddr
           (cddddr
              (codeFormula
                 (impH (substituteFormula LNT x x0 Zero)
                    (impH
                       (forallH x0
                          (impH x
                             (substituteFormula LNT x x0 
                                (Succ (var x0)))))
                       (forallH x0 x)))))) 
         with (codeFormula x).
      * cbv zeta; unfold codeFormula; rewrite <- codeCloseCorrect.
        replace
          (codeClose
             (codeImp
                (codeSubFormula
                   (code.codeFormula LNT codeLNTFunction 
                      codeLNTRelation x) x0
                   (codeTerm Zero))
                (codeImp
                   (codeForall x0
                      (codeImp
                         (code.codeFormula LNT codeLNTFunction 
                            codeLNTRelation x)
                         (codeSubFormula
                            (code.codeFormula LNT 
                               codeLNTFunction codeLNTRelation x)
                            x0 (codeTerm (Succ (var x0))))))
                   (codeForall x0
                      (code.codeFormula LNT codeLNTFunction 
                         codeLNTRelation x)))))
          with
          (codeClose
             (code.codeFormula LNT codeLNTFunction codeLNTRelation
                (impH (substituteFormula LNT x x0 Zero)
                   (impH
                      (forallH x0
                         (impH x (substituteFormula LNT x x0 
                                    (Succ (var x0)))))
                      (forallH x0 x))))).
      -- rewrite Nat.eqb_refl; reflexivity.
      -- simpl; unfold codeTerm; repeat rewrite codeSubFormulaCorrect.
         reflexivity.
      * simpl; 
          repeat rewrite cPairProjections1 || rewrite cPairProjections2.
        reflexivity.
    + simpl in |- *.
      repeat rewrite cPairProjections1 || rewrite cPairProjections2.
      reflexivity.
  - unfold close.
      induction
        (List.nodup Nat.eq_dec
           (freeVarFormula LNT
              (impH (substituteFormula LNT x x0 Zero)
                 (impH
                    (forallH x0
                       (impH x (substituteFormula LNT x x0 
                                  (Succ (var x0)))))
             (forallH x0 x))))).
    + reflexivity.
    + simpl; assumption.
Qed.

Lemma codeInductionSchemaCorrect2 (f : Formula):
 codeInductionSchema (codeFormula f) = true -> InductionSchema f.
Proof.
  intros H; lazy beta delta [codeInductionSchema] in H;
    rewrite codeOpenCorrect in H.
  set
    (n := car (cdr (cddddr (codeFormula (open f))))) in *.
  set
    (g := cdr (cdr (cddddr (codeFormula (open f))))) in *.
  cbv zeta in H.
  induction
    (eq_nat_dec
       (codeImp (codeSubFormula g n (codeTerm Zero))
          (codeImp
             (codeForall n
                (codeImp g (codeSubFormula g n 
                              (codeTerm (Succ (var n))))))
             (codeForall n g))) 
       (codeFormula (open f))) as [a | b].
  - rewrite a in H; unfold codeFormula in H; 
      rewrite codeCloseCorrect in H;  fold codeFormula in H.
    destruct (formula_eqdec LNT LNT_eqdec (close LNT (open f)) f) 
      as [a0 | b].
    + unfold codeImp at 1 in a.
      destruct (open f) as [t t0| r t| f0 f1| f0| n0 f0]; simpl in a;
        try
          match goal with
          | h:(cPair ?X1 ?X2 = cPair ?X3 ?X4) |- _ =>
              assert False by (cut (X1 = X3);
              [ discriminate | eapply cPairInj1; apply h]) ; contradiction
          end.
        assert (H0: codeSubFormula g n (codeTerm Zero) = codeFormula f0).
        { eapply cPairInj1, cPairInj2; apply a. }
        assert 
          (H1: codeImp
                 (codeForall n 
                    (codeImp g (codeSubFormula g n 
                                  (codeTerm (Succ (var n))))))
                 (codeForall n g) = 
                 codeFormula f1).
        { eapply cPairInj2; eapply cPairInj2; apply a. }
        clear a.
        Opaque cPairPi1.
        Opaque cPairPi2.
        unfold codeImp at 1 in H1.
        destruct f1 as [t t0| r t| f1 f2| f1| n0 f1]; simpl in H1;
          try
            match goal with
            | h:(cPair ?X1 ?X2 = cPair ?X3 ?X4) |- _ =>
                assert False by
                (cut (X1 = X3);
                [ discriminate | eapply cPairInj1; apply h ]); 
                 contradiction
            end.
        assert
          (H2: codeForall n (codeImp g 
                               (codeSubFormula g n 
                                  (codeTerm (Succ (var n))))) =
                 codeFormula f1).
        { eapply cPairInj1; eapply cPairInj2; apply H1. }
        assert (H3: codeForall n g = codeFormula f2).
        { eapply cPairInj2; eapply cPairInj2; apply H1. }
        clear H1.
        unfold codeForall at 1 in H3;
          destruct f2 as [t t0| r t| f2 f3| f2| n0 f2]; simpl in H3;
          try
            match goal with
            | h:(cPair ?X1 ?X2 = cPair ?X3 ?X4) |- _ =>
                assert False by (cut (X1 = X3);
                [ discriminate | eapply cPairInj1; apply h ]); 
                contradiction
            end.
        simpl in (value of n).
        simpl in (value of g).
        unfold InductionSchema in |- *.
        exists f2, n0.
        unfold PA7; replace (substituteFormula LNT f2 n0 Zero) with f0.
      * replace (forallH n0 (impH f2 
                               (substituteFormula LNT f2 n0 
                                  (Succ (var n0)))))
          with f1.
        -- symmetry; apply a0.
        -- apply codeFormulaInj; simpl; rewrite <- codeSubFormulaCorrect.
           symmetry; unfold n, g in H2.
           repeat 
             rewrite cPairProjections1 in H2 || 
                                            rewrite cPairProjections2 
               in H2; apply H2.
      * apply codeFormulaInj; rewrite <- codeSubFormulaCorrect.
        symmetry; unfold n, g in H0.
        repeat 
          rewrite cPairProjections1 in H0 || rewrite cPairProjections2
            in H0; apply H0.
    + rewrite nat_eqb_false in H. 
      * discriminate H.
      * unfold not in |- *; intros; apply b.
        apply codeFormulaInj, H0.
  - rewrite nat_eqb_false in H.
    discriminate H.
    unfold not in |- *; intros; apply b.
    rewrite <- codeOpenCorrect, <- H0.
    unfold codeImp;
      generalize
        (cPair (codeSubFormula g n (codeTerm Zero))
           (cPair 1
              (cPair
                 (codeForall n
                    (cPair 1
                       (cPair g (codeSubFormula g n 
                                   (codeTerm (Succ (var n)))))))
                 (codeForall n g)))).
    intros n0; unfold codeClose;
      assert
        (H1: forall m : nat,
            m <= codeNoDup (codeFreeVarFormula (cPair 1 n0)) ->
            cPair 1 n0 = codeOpen (codeCloseList m (cPair 1 n0))).
    { induction (codeNoDup (codeFreeVarFormula (cPair 1 n0))).
      intros m H1; replace m with 0 by lia.
      - unfold codeCloseList, evalStrongRec.
        unfold evalComposeFunc, evalOneParamList, evalList; simpl.
        rewrite cPairProjections1.
        unfold codeOpen, evalStrongRec.
        unfold evalComposeFunc, evalOneParamList, evalList.
        rewrite computeEvalStrongRecHelp.
        unfold compose2, evalComposeFunc, evalOneParamList, evalList.
        repeat rewrite cPairProjections1.
        simpl; repeat rewrite cPairProjections1; reflexivity.
      - intros m H1; destruct  (Compat815.le_lt_or_eq _ _ H1) as [H2 | H2].
        + apply IHn1.
          apply Compat815.lt_n_Sm_le.
          assumption.
        + rewrite H2.
          unfold codeCloseList in |- *.
          set (g0 :=
                 fun l recs f0 : nat =>
                   switchPR l
                     (cPair 3
                        (cPair (car (pred l))
                           (codeNth (l - S (cdr (pred l))) recs)))
                     f0).
          unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
          rewrite computeEvalStrongRecHelp.
          unfold compose2,  evalComposeFunc, evalOneParamList, evalList.
          assert
            (H3: forall n m : nat,
                m < n ->
                extEqual 1
                  (evalComposeFunc 1 1 (Vector.cons _
                                          (evalStrongRecHelp 1 g0 n) 0 
                                          (Vector.nil _))
                     (fun b : nat => codeNth (n - S m) b)) 
                  (evalStrongRec 1 g0 m)).
          { intros n2 m0; apply (evalStrongRecHelp2 1). }
          simpl in H3.
          unfold g0 at 1; rewrite H3; simpl. 
          * repeat rewrite cPairProjections1.
            unfold codeCloseList in IHn1.
            move g0 after IHn1; fold g0 in IHn1.
            set (A := evalStrongRec 1 g0 (cdr n1) (cPair 1 n0)) in *.
            unfold codeOpen.
            set
              (g1 :=
                 fun f0 recs : nat =>
                   switchPR (car f0)
                     (switchPR (pred (car f0))
                        (switchPR (pred (pred (car f0)))
                           (switchPR (pred (pred (pred (car f0)))) f0
                              (codeNth (f0 - S (cdr (cdr f0))) recs)) 
                           f0) f0) f0).
            unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
            rewrite computeEvalStrongRecHelp; unfold compose2. 
            unfold evalComposeFunc, evalOneParamList, evalList;
              unfold g1 at 1 in |- *.
            unfold pred at 1 in |- *.
            repeat rewrite cPairProjections1.
            repeat rewrite evalStrongRecHelp1.
            simpl; repeat rewrite cPairProjections2.
            unfold A; unfold codeOpen in IHn1.
            move g1 after IHn1; fold g1 in IHn1; apply IHn1.
            apply cPairLe2A.
            repeat rewrite cPairProjections2.
            eapply Nat.le_lt_trans; [ idtac | apply cPairLt2 ].
            apply cPairLe2; simpl; apply Compat815.le_lt_n_Sm.
          * specialize (cPairLe2A n1); lia. 
    } 
    apply H1, le_n.
Qed.

Lemma codeInductionSchemaCorrect3 (f : Formula):
 ~ InductionSchema f -> codeInductionSchema (codeFormula f) = false.
Proof.
  intros H; assert (H0: forall x : bool, x = true \/ x = false) by
   (intros x; destruct x; auto). 
  destruct (H0 (codeInductionSchema (codeFormula f))) as [H1 | H1].
  - elim H; now apply codeInductionSchemaCorrect2.
  - assumption.
Qed.

Lemma codeInductionSchemaIsPR : isPRrel 1 codeInductionSchema.
Proof.
  lazy beta delta [codeInductionSchema];
    set (A := fun f : nat => cddddr (cdr (codeOpen f))).
  assert (H: isPR 1 A).
  { unfold A in |- *.
    apply compose1_1IsPR with (g := iterate cPairPi2 5) (f := codeOpen).
    - apply codeOpenIsPR.
    - apply iterateIsPR, cPairPi2IsPR.
  } 
  assert
    (H0: isPRrel 1
           (fun f : nat =>
              let n := car (A f) in
              let g := cdr (A f) in
              Nat.eqb
                (codeClose
                   (codeImp (codeSubFormula g n (codeTerm Zero))
                      (codeImp
                         (codeForall n
                            (codeImp g (codeSubFormula g n
                                          (codeTerm (Succ (var n))))))
                         (codeForall n g)))) f)).
  { unfold isPRrel; apply compose1_2IsPR with
      (g := charFunction 2 Nat.eqb)
      (f' := fun f : nat => f)
      (f := fun f : nat =>
              codeClose
                (codeImp
                   (codeSubFormula (cdr (A f)) (car (A f))
                      (codeTerm Zero))
                   (codeImp
                      (codeForall (car (A f))
                         (codeImp (cdr (A f))
                            (codeSubFormula (cdr (A f)) 
                               (car (A f))
                               (codeTerm (Succ (var (car (A f))))))))
                      (codeForall (car (A f)) (cdr (A f)))))).
    - apply compose1_1IsPR with
        (f := fun f : nat =>
                codeImp
                  (codeSubFormula (cdr (A f)) (car (A f)) (codeTerm Zero))
                  (codeImp
                     (codeForall (car (A f))
                        (codeImp (cdr (A f))
                           (codeSubFormula (cdr (A f)) 
                              (car (A f))
                              (codeTerm (Succ (var (car (A f))))))))
                     (codeForall (car (A f)) (cdr (A f))))).
      + apply compose1_2IsPR with
          (f := fun f : nat =>
                  codeSubFormula (cdr (A f)) (car (A f)) (codeTerm Zero))
          (f' := fun f : nat =>
                   codeImp
                     (codeForall (car (A f))
                        (codeImp (cdr (A f))
                           (codeSubFormula (cdr (A f)) 
                              (car (A f))
                              (codeTerm (Succ (var (car (A f))))))))
                     (codeForall (car (A f)) (cdr (A f)))).
        * apply compose1_3IsPR with
            (f1 := fun f : nat => cdr (A f))
            (f2 := fun f : nat => car (A f))
            (f3 := fun f : nat => codeTerm Zero).
          -- apply compose1_1IsPR.
             ++ assumption.
             ++ apply cPairPi2IsPR.
          -- apply compose1_1IsPR.
             assumption.
             apply cPairPi1IsPR.
          -- apply const1_NIsPR.
          -- apply codeSubFormulaIsPR.
        * apply compose1_2IsPR with
            (f := fun f : nat =>
                    codeForall (car (A f))
                      (codeImp (cdr (A f))
                         (codeSubFormula (cdr (A f)) (car (A f))
                            (codeTerm (Succ (var (car (A f))))))))
            (f' := fun f : nat => codeForall (car (A f)) (cdr (A f))).
          -- apply compose1_2IsPR with
               (f := fun f : nat => car (A f))
               (f' := fun f : nat =>
                        codeImp (cdr (A f))
                          (codeSubFormula (cdr (A f)) (car (A f))
                             (codeTerm (Succ (var (car (A f))))))).
             ++ apply compose1_1IsPR.
                assumption.
                apply cPairPi1IsPR.
             ++ apply compose1_2IsPR with
                  (f := fun f : nat => cdr (A f))
                  (f' := fun f : nat =>
                           codeSubFormula (cdr (A f)) (car (A f))
                             (codeTerm (Succ (var (car (A f)))))).
                ** apply compose1_1IsPR.
                   assumption.
                   apply cPairPi2IsPR.
                ** apply compose1_3IsPR with
                     (f1 := fun f : nat => cdr (A f))
                     (f2 := fun f : nat => car (A f))
                     (f3 := fun f : nat => codeTerm (Succ (var (car (A f))))).
                   apply compose1_1IsPR.
                   assumption.
                   apply cPairPi2IsPR.
                   apply compose1_1IsPR.
                   assumption.
                   apply cPairPi1IsPR.
                   assert
                     (H0: isPR 1 
                            (fun f : nat => 
                               cPair 3 (S (cPair (cPair 0 (car (A f))) 0)))).
                   { apply compose1_2IsPR with
                       (f := fun f : nat => 3)
                       (f' := fun f : nat => S (cPair (cPair 0 (car (A f))) 0)).
                     - apply const1_NIsPR.
                     - apply compose1_1IsPR with 
                         (f := fun f : nat => cPair (cPair 0 (car (A f))) 0).
                       + apply compose1_2IsPR with
                           (f := fun f : nat => cPair 0 (car (A f)))
                           (f' := fun f : nat => 0).
                         * apply compose1_2IsPR with 
                             (f := fun f : nat => 0)
                             (f' := fun f : nat => car (A f)).
                           -- apply const1_NIsPR.
                           -- apply compose1_1IsPR.
                              assumption.
                              apply cPairPi1IsPR.
                           -- apply cPairIsPR.
                         * apply const1_NIsPR.
                         * apply cPairIsPR.
                       + apply succIsPR.
                     - apply cPairIsPR.
                   } 
                   destruct H0 as (x, p).
                   exists x.
                   eapply extEqualTrans.
                   apply p.
                   simpl in |- *.
                   intros c; reflexivity.
                   apply codeSubFormulaIsPR.
                ** apply codeImpIsPR.
             ++ apply codeForallIsPR.
          -- apply compose1_2IsPR  with
               (f := fun f : nat => car (A f))
               (f' := fun f : nat => cdr (A f)).
             ++ apply compose1_1IsPR.
                assumption.
                apply cPairPi1IsPR.
             ++ apply compose1_1IsPR.
                assumption.
                apply cPairPi2IsPR.
             ++ apply codeForallIsPR.
          -- apply codeImpIsPR.
        * apply codeImpIsPR.
      + apply codeCloseIsPR.
    - apply idIsPR.
    - apply eqIsPR.
  } 
  apply H0.
Qed.

Definition codePA : nat -> bool :=
  orRel 1 (Nat.eqb (codeFormula PA6))
    (orRel 1 (Nat.eqb (codeFormula PA5))
       (orRel 1 (Nat.eqb (codeFormula PA4))
          (orRel 1 (Nat.eqb (codeFormula PA3))
             (orRel 1 (Nat.eqb (codeFormula PA2))
                (orRel 1 (Nat.eqb (codeFormula PA1)) 
                   codeInductionSchema))))).

Lemma codePAcorrect1 (f : Formula):
 codePA (codeFormula f) = true -> mem Formula PA f.
Proof.
  intros H; destruct (PAdec f) as [H0 | H0].
  - assumption.
  - unfold codePA, orRel, nat_rec, nat_rect in H.
    unfold PA; destruct (eq_nat_dec (codeFormula PA6) (codeFormula f))
      as [a | b].
    + rewrite a, Nat.eqb_refl in H.
      replace f with PA6.
      * right; constructor.
      * eapply codeFormulaInj; apply a.
    + left; rewrite nat_eqb_false in H.
      * clear b.
        destruct (eq_nat_dec (codeFormula PA5) (codeFormula f)) as [a | b].
        -- rewrite a, Nat.eqb_refl in H.
           replace f with PA5.
           ++ right; constructor.
           ++ eapply codeFormulaInj; apply a.
        -- left.
           rewrite nat_eqb_false in H.
           ++ clear b; destruct (eq_nat_dec (codeFormula PA4) (codeFormula f))
                as [a | b].
              ** rewrite a in H.
                 rewrite Nat.eqb_refl in H.
                 replace f with PA4.
                 right; constructor.
                 eapply codeFormulaInj.
                 apply a.
              ** left.
                 rewrite nat_eqb_false in H.
                 clear b. 
                 induction (eq_nat_dec (codeFormula PA3) (codeFormula f))
                             as [a | b]. 
                 rewrite a in H.
                 rewrite Nat.eqb_refl in H.
                 replace f with PA3.
                 right; constructor.
                 eapply codeFormulaInj.
                 apply a.
                 left.
                 rewrite nat_eqb_false in H.
                 clear b.
                 induction (eq_nat_dec (codeFormula PA2) (codeFormula f)) 
                   as [a | b].
                 rewrite a, Nat.eqb_refl in H.
                 replace f with PA2.
                 right; constructor.
                 eapply codeFormulaInj.
                 apply a.
                 left.
                 rewrite nat_eqb_false in H.
                 clear b.
                 induction (eq_nat_dec (codeFormula PA1) (codeFormula f))
                   as [a | b].
                 rewrite a, Nat.eqb_refl in H.
                 replace f with PA1.
                 right; constructor.
                 eapply codeFormulaInj.
                 apply a.
                 left.
                 rewrite nat_eqb_false in H.
                 apply codeInductionSchemaCorrect2.
                 simpl in H.
                 assumption.
                 assumption.
                 assumption.
                 assumption.
                 assumption.
           ++ assumption.
      * assumption.
Qed.

Lemma codePAcorrect2 (f : Formula):
 ~ mem Formula PA f -> codePA (codeFormula f) = false.
Proof.
  intros H ; assert (H0: forall x : bool, x = true \/ x = false).
  { intros x; destruct x; auto. } 
  induction (H0 (codePA (codeFormula f)))  as [H1 | H1].
  - elim H; apply codePAcorrect1; assumption.
  - assumption.
Qed.

Lemma codePAcorrect3 (f : Formula):
  mem Formula PA f -> codePA (codeFormula f) = true.
Proof.
  intros H; unfold codePA, orRel, nat_rec, nat_rect.
  do 6 try induction H.
  - assert (H0: codeInductionSchema (codeFormula x) = true).
    + apply codeInductionSchemaCorrect1, H.
    + rewrite H0; repeat rewrite orb_true_b; 
        repeat rewrite orb_b_true; reflexivity.
  - destruct H.
    generalize (codeFormula PA1); intro n. 
    rewrite Nat.eqb_refl.
    repeat rewrite orb_true_b; repeat rewrite orb_b_true; reflexivity.
  - generalize (codeFormula PA2); intro n. 
    rewrite Nat.eqb_refl.
    repeat rewrite orb_true_b; repeat rewrite orb_b_true; reflexivity.
  - generalize (codeFormula PA3); intros n.
    rewrite Nat.eqb_refl.
    repeat rewrite orb_true_b; repeat rewrite orb_b_true; reflexivity.
  - generalize (codeFormula PA4); intros n.
    rewrite Nat.eqb_refl.
    repeat rewrite orb_true_b; repeat rewrite orb_b_true; reflexivity.
  - generalize (codeFormula PA5); intros n.
    rewrite Nat.eqb_refl.
    repeat rewrite orb_true_b; repeat rewrite orb_b_true; reflexivity.
  - rewrite Nat.eqb_refl.
    repeat rewrite orb_true_b; repeat rewrite orb_b_true; reflexivity.
Qed.

Lemma codePAIsPR : isPRrel 1 codePA.
Proof.
  unfold codePA in |- *.
  assert (H: forall n : nat, isPRrel 1 (Nat.eqb n)).
  { intros n; apply compose1_2IsPR with
      (f := fun f : nat => n)
      (f' := fun f : nat => f)
      (g := charFunction 2 Nat.eqb).
    - apply const1_NIsPR.
    - apply idIsPR.
    - apply eqIsPR.
  }
  repeat apply orRelPR; try apply H.
  apply codeInductionSchemaIsPR.
Qed.

End Code_PA.

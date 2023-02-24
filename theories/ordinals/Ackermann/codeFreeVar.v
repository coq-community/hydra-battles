Require Import primRec.
Require Import cPair.
Require Import Coq.Lists.List.
Require Import ListExt.
Require Import Arith.
Require Export codeList.
Require Import folProp.
Require Import code.
Require Import Compat815.

Import LispAbbreviations.
Section Code_Free_Vars.

Variable L : Language.
Variable codeF : Functions L -> nat.
Variable codeR : Relations L -> nat.

Let Formula := Formula L.
Let Formulas := Formulas L.
Let System := System L.
Let Term := Term L.
Let Terms := Terms L.
Let apply := apply L.
Let ifThenElseH := ifThenElseH L.

Definition codeFreeVarTermTerms : nat -> nat :=
  evalStrongRec 0
    (fun t recs : nat =>
     cPair
       (switchPR (car t) (cdr (codeNth (t - S (cdr t)) recs))
          (S (cPair (cdr t) 0)))
       (switchPR t
          (codeApp (car (codeNth (t - S (car (pred t))) recs))
             (cdr (codeNth (t - S (cdr (pred t))) recs))) 0)).

Definition codeFreeVarTerm (t : nat) : nat :=
  car (codeFreeVarTermTerms t).

Definition codeFreeVarTerms (t : nat) : nat :=
  cdr (codeFreeVarTermTerms t).

Lemma codeFreeVarTermCorrect :
 forall t : Term,
 codeFreeVarTerm (codeTerm L codeF t) = codeList (freeVarTerm L t).
Proof.
 intros t; elim t using  Term_Terms_ind
  with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
           codeFreeVarTerms (codeTerms L codeF n ts) =
           codeList (freeVarTerms L n ts)); intros.
 - simpl; unfold codeTerm, codeFreeVarTerm, codeFreeVarTermTerms,
     evalStrongRec in |- *.
   simpl; repeat rewrite cPairProjections1 || rewrite cPairProjections2.
   simpl; reflexivity.
 - unfold freeVarTerm; fold (freeVarTerms L (arity L (inr (Relations L) f)) t0).
   rewrite <- H; clear H.
   unfold codeTerm; fold (codeTerms L codeF (arity L (inr (Relations L) f)) t0).
   generalize (codeTerms L codeF (arity L (inr (Relations L) f)) t0).
   intros n; unfold codeFreeVarTerm, codeFreeVarTermTerms.
   set
     (g := fun t1 recs : nat =>
             cPair
               (switchPR (car t1) (cdr 
                                          (codeNth (t1 - S (cdr t1)) recs))
                  (S (cPair (cdr t1) 0)))
               (switchPR t1
                  (codeApp (car (codeNth 
                                        (t1 - S (car (pred t1))) recs))
                     (cdr (codeNth (t1 - S (cdr (pred t1))) recs))) 0))      in *.
   unfold evalStrongRec, evalComposeFunc, evalOneParamList.
   rewrite computeEvalStrongRecHelp.
   unfold compose2 in |- *.
   unfold evalComposeFunc in |- *.
   unfold g at 1 in |- *.
   repeat rewrite cPairProjections1 || rewrite cPairProjections2.
   rewrite (evalStrongRecHelp1 g (cPair (S (codeF f)) n) n).
   + simpl; repeat rewrite cPairProjections1 || rewrite cPairProjections2.
     unfold codeFreeVarTerms; unfold codeFreeVarTermTerms.
     fold g; reflexivity.
   + apply cPairLt2.
 - simpl; unfold codeTerms, codeFreeVarTerms, codeFreeVarTermTerms.
   unfold evalStrongRec; simpl; 
     repeat rewrite cPairProjections1 || rewrite cPairProjections2.
   reflexivity.
 - unfold freeVarTerms; fold (freeVarTerm L t0);
     fold (freeVarTerms L n t1); rewrite <- codeAppCorrect.
   rewrite <- H; rewrite <- H0; clear H H0.
   unfold codeTerms.
   fold (codeTerm L codeF t0); fold (codeTerms L codeF n t1).
   generalize (codeTerm L codeF t0) (codeTerms L codeF n t1).
   clear t0 t1.
   intros n0 n1; unfold codeFreeVarTerms at 1 in |- *.
   unfold codeFreeVarTermTerms in |- *.
   unfold evalStrongRec in |- *.
   set
     (g :=
        fun t0 recs : nat =>
          cPair
            (switchPR (car t0) 
               (cdr (codeNth (t0 - S (cdr t0)) recs))
               (S (cPair (cdr t0) 0)))
            (switchPR t0
               (codeApp (car (codeNth (t0 - S (car (pred t0))) recs))
                  (cdr (codeNth (t0 - S (cdr (pred t0))) recs))) 0)) 
     in *.
   unfold evalComposeFunc, evalOneParamList. 
   rewrite computeEvalStrongRecHelp.
   unfold compose2, evalComposeFunc; unfold g at 1.
   rewrite
     (evalStrongRecHelp1 g (S (cPair n0 n1))
        (car (pred (S (cPair n0 n1))))).
   + rewrite
       (evalStrongRecHelp1 g (S (cPair n0 n1)) 
          (cdr (pred (S (cPair n0 n1))))).
     simpl; repeat rewrite cPairProjections1 || rewrite cPairProjections2.
     reflexivity.
     simpl; rewrite cPairProjections2.
     apply Compat815.le_lt_n_Sm.
     apply cPairLe2.
   + simpl; rewrite cPairProjections1.
     apply Compat815.le_lt_n_Sm.
     apply cPairLe1.
Qed.

Lemma codeFreeVarTermsCorrect (n : nat) (ts : Terms n):
 codeFreeVarTerms (codeTerms L codeF n ts) = codeList (freeVarTerms L n ts).
Proof.
  induction ts as [| n t ts Hrects].
  - simpl; unfold codeTerms, codeFreeVarTerms, codeFreeVarTermTerms.
    unfold evalStrongRec; simpl.
    repeat rewrite cPairProjections1 || rewrite cPairProjections2.
    reflexivity.
  - unfold freeVarTerms; fold (freeVarTerm L t); fold (freeVarTerms L n ts).
    rewrite <- codeAppCorrect.
    rewrite <- Hrects.
    rewrite <- codeFreeVarTermCorrect; clear Hrects.
    unfold codeTerms; fold (codeTerm L codeF t); fold (codeTerms L codeF n ts).
    generalize (codeTerm L codeF t) (codeTerms L codeF n ts).
    clear t ts.
    intros n0 n1;
      unfold codeFreeVarTerms at 1; unfold codeFreeVarTermTerms.
    unfold evalStrongRec in |- *.
    set
      (g :=
         fun t0 recs : nat =>
           cPair
             (switchPR (car t0)
                (cdr (codeNth (t0 - S (cdr t0)) recs))
                (S (cPair (cdr t0) 0)))
             (switchPR t0
                (codeApp (car (codeNth (t0 - S (car (pred t0))) recs))
                   (cdr (codeNth (t0 - S (cdr (pred t0))) recs))) 0)). 
    unfold evalComposeFunc, evalOneParamList.
    rewrite computeEvalStrongRecHelp.
    unfold compose2, evalComposeFunc; unfold g at 1.
    + rewrite
        (evalStrongRecHelp1 g (S (cPair n0 n1)) 
           (car (pred (S (cPair n0 n1))))).
      * rewrite  (evalStrongRecHelp1 g (S (cPair n0 n1)) 
                    (cdr (pred (S (cPair n0 n1))))).
        -- simpl; repeat rewrite cPairProjections1 || rewrite cPairProjections2.
           reflexivity.
        -- simpl; rewrite cPairProjections2.
           apply Compat815.le_lt_n_Sm.
           apply cPairLe2.
      * simpl; rewrite cPairProjections1.
        apply Nat.lt_succ_r.
        apply cPairLe1.
Qed.

Lemma codeFreeVarTermTermsIsPR : isPR 1 codeFreeVarTermTerms.
Proof.
  unfold codeFreeVarTermTerms; apply evalStrongRecIsPR.
  apply
    compose2_2IsPR
    with
    (f := fun t recs : nat =>
            switchPR (car t)
              (cdr (codeNth (t - S (cdr t)) recs))
              (S (cPair (cdr t) 0)))
    (g := fun t recs : nat =>
            switchPR t
              (codeApp (car (codeNth (t - S (car (pred t))) recs))
                 (cdr (codeNth (t - S (cdr (pred t))) recs))) 0).
  - apply compose2_3IsPR with
      (f1 := fun t recs : nat => car t)
      (f2 := fun t recs : nat => cdr (codeNth (t - S (cdr t)) recs))
      (f3 := fun t recs : nat => S (cPair (cdr t) 0)).
    + apply filter10IsPR.
      apply cPairPi1IsPR.
    + apply compose2_1IsPR with 
        (f := fun t recs : nat => codeNth (t - S (cdr t)) recs).
      * apply compose2_2IsPR with
          (f := fun t recs : nat => t - S (cdr t))
          (g := fun t recs : nat => recs).
        -- apply filter10IsPR with 
             (g := fun t : nat => t - S (cdr t)).
           apply compose1_2IsPR with
             (f := fun t : nat => t) (f' := fun t : nat => S (cdr t)).
           ++ apply idIsPR.
           ++ apply compose1_1IsPR.
              apply cPairPi2IsPR.
              apply succIsPR.
           ++ apply minusIsPR.
        -- apply pi2_2IsPR.
        -- apply codeNthIsPR.
      * apply cPairPi2IsPR.
    + apply filter10IsPR with (g := fun t : nat => S (cPair (cdr t) 0)).
      apply compose1_1IsPR with (f := fun t : nat => cPair (cdr t) 0).
      * apply compose1_2IsPR with (f := cPairPi2) (f' := fun _ : nat => 0).
        -- apply cPairPi2IsPR.
        -- apply const1_NIsPR.
        -- apply cPairIsPR.
      * apply succIsPR.
    + apply switchIsPR.
  - apply compose2_3IsPR with
      (f1 := fun t recs : nat => t)
      (f2 := fun t recs : nat =>
               codeApp (car (codeNth (t - S (car (pred t))) recs))
                 (cdr (codeNth (t - S (cdr (pred t))) recs)))
      (f3 := fun t recs : nat => 0).
    + apply pi1_2IsPR.
    + apply compose2_2IsPR with
        (f := fun t recs : nat =>
                car (codeNth (t - S (car (pred t))) recs))
        (g := fun t recs : nat =>
                cdr (codeNth (t - S (cdr (pred t))) recs)).
      * apply compose2_1IsPR with 
          (f := fun t recs : nat => codeNth (t - S (car (pred t))) recs).
        -- apply compose2_2IsPR with
             (f := fun t recs : nat => t - S (car (pred t)))
             (g := fun t recs : nat => recs).
           ++ apply filter10IsPR with
                (g := fun t : nat => t - S (car (pred t))).
              apply compose1_2IsPR with 
                (f := fun t : nat => t)
                (f' := fun t : nat => S (car (pred t))).
              ** apply idIsPR.
              ** apply compose1_1IsPR with 
                   (f := fun t : nat => car (pred t)).
                 apply compose1_1IsPR.
                 apply predIsPR.
                 apply cPairPi1IsPR.
                 apply succIsPR.
              ** apply minusIsPR.
           ++ apply pi2_2IsPR.
           ++ apply codeNthIsPR.
        -- apply cPairPi1IsPR.
      * apply compose2_1IsPR with 
          (f := fun t recs : nat => codeNth (t - S (cdr (pred t))) recs).
        -- apply compose2_2IsPR with
             (f := fun t recs : nat => t - S (cdr (pred t)))
             (g := fun t recs : nat => recs).
           ++ apply filter10IsPR with 
             (g := fun t : nat => t - S (cdr (pred t))).
              apply compose1_2IsPR with 
                (f := fun t : nat => t) 
                (f' := fun t : nat => S (cdr (pred t))).
              ** apply idIsPR.
              ** apply compose1_1IsPR with 
                   (f := fun t : nat => cdr (pred t)).
                 apply compose1_1IsPR.
                 apply predIsPR.
                 apply cPairPi2IsPR.
                 apply succIsPR.
              ** apply minusIsPR.
           ++ apply pi2_2IsPR.
           ++ apply codeNthIsPR.
        -- apply cPairPi2IsPR.
      * apply codeAppIsPR.
    + exists (composeFunc 2 0 (PRnil _) zeroFunc).
      simpl; auto.
    + apply switchIsPR.
  - apply cPairIsPR.
Qed.

Lemma codeFreeVarTermIsPR : isPR 1 codeFreeVarTerm.
Proof.
  unfold codeFreeVarTerm; apply compose1_1IsPR.
  - apply codeFreeVarTermTermsIsPR.
  - apply cPairPi1IsPR.
Qed.

Lemma codeFreeVarTermsIsPR : isPR 1 codeFreeVarTerms.
Proof.
  unfold codeFreeVarTerms; apply compose1_1IsPR.
  - apply codeFreeVarTermTermsIsPR.
  - apply cPairPi2IsPR.
Qed.

Definition codeFreeVarFormula : nat -> nat :=
  evalStrongRec 0
    (fun f recs : nat =>
     switchPR (car f)
       (switchPR (pred (car f))
          (switchPR (pred (pred (car f)))
             (switchPR (pred (pred (pred (car f))))
                (codeFreeVarTerms (cdr f))
                (codeListRemove (cadr f)
                   (codeNth (f - S (cddr f)) recs)))
             (codeNth (f - S (cdr f)) recs))
          (codeApp (codeNth (f - S (cadr  f)) recs)
             (codeNth (f - S (cddr f)) recs)))
       (codeApp (codeFreeVarTerm (cadr f))
          (codeFreeVarTerm (cddr f)))).

Lemma codeFreeVarFormulaCorrect (f : Formula) :
  codeFreeVarFormula (codeFormula L codeF codeR f) =
    codeList (freeVarFormula L f).
Proof.
  set
    (g :=
       fun f recs : nat =>
         switchPR (car f)
           (switchPR (pred (car f))
              (switchPR (pred (pred (car f)))
                 (switchPR (pred (pred (pred (car f))))
                    (codeFreeVarTerms (cdr f))
                    (codeListRemove (car (cdr f))
                       (codeNth (f - S (cdr (cdr f))) recs)))
                 (codeNth (f - S (cdr f)) recs))
              (codeApp (codeNth (f - S (car (cdr f))) recs)
                 (codeNth (f - S (cdr (cdr f))) recs)))
           (codeApp (codeFreeVarTerm (car (cdr f)))
              (codeFreeVarTerm (cdr (cdr f))))) 
    in *.
  induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf].
  - simpl; rewrite <- codeAppCorrect; repeat rewrite <- codeFreeVarTermCorrect.
    generalize (codeTerm L codeF t) (codeTerm L codeF t0).
    clear t t0; intros n n0. 
    unfold codeFreeVarFormula, evalStrongRec; simpl.
    repeat rewrite cPairProjections1 || rewrite cPairProjections2.
    simpl; reflexivity.
  - simpl; rewrite <- codeFreeVarTermsCorrect.
    generalize (codeTerms L codeF (arity L (inl (Functions L) r)) t).
    clear t.
    intros n; unfold codeFreeVarFormula, evalStrongRec.
    unfold evalStrongRecHelp, evalComposeFunc, evalOneParamList, 
      evalPrimRecFunc.
    repeat rewrite cPairProjections1 || rewrite cPairProjections2.
    simpl; repeat rewrite cPairProjections1 || rewrite cPairProjections2.
    reflexivity.
  - simpl; rewrite <- codeAppCorrect.
    rewrite <- Hrecf1.
    rewrite <- Hrecf0.
    clear Hrecf0 Hrecf1.
    unfold codeFreeVarFormula; fold g; unfold evalStrongRec. 
    unfold evalComposeFunc, evalOneParamList.
    rewrite computeEvalStrongRecHelp.
    simpl in |- *.
    repeat rewrite cPairProjections1 || rewrite cPairProjections2.
    unfold g at 1 in |- *.
    repeat rewrite cPairProjections1 || rewrite cPairProjections2.
    rewrite
      (evalStrongRecHelp1 g
         (cPair 1
            (cPair (codeFormula L codeF codeR f1) 
               (codeFormula L codeF codeR f0)))
         (codeFormula L codeF codeR f1)).
    + rewrite
        (evalStrongRecHelp1 g
           (cPair 1
              (cPair (codeFormula L codeF codeR f1)
                 (codeFormula L codeF codeR f0)))
           (codeFormula L codeF codeR f0)).
      * simpl; unfold evalStrongRec, evalComposeFunc, evalOneParamList.
        simpl; repeat rewrite cPairProjections1 || rewrite cPairProjections2.
        reflexivity.
      * eapply Nat.lt_le_trans.
        -- apply cPairLt2.
        -- apply cPairLe3.
           ++ apply le_n.
           ++ apply cPairLe2.
    + eapply Nat.lt_le_trans.
      * apply cPairLt2.
      * apply cPairLe3.
        -- apply le_n.
        -- apply cPairLe1.
  - simpl; rewrite <- Hrecf; clear Hrecf.
    generalize (codeFormula L codeF codeR f).
    clear f.
    intros n; unfold codeFreeVarFormula at 1; fold g.
    unfold evalStrongRec, evalComposeFunc, evalOneParamList.
    rewrite computeEvalStrongRecHelp; unfold evalComposeFunc, compose2.
    unfold evalList, pred;
      repeat rewrite cPairProjections1 || rewrite cPairProjections2.
    unfold g at 1; repeat rewrite cPairProjections1 || rewrite cPairProjections2.
    rewrite (evalStrongRecHelp1 g (cPair 2 n) n).
    simpl; reflexivity.
    apply cPairLt2; simpl. 
  - simpl; rewrite <- codeListRemoveCorrect.
    rewrite <- Hrecf; generalize (codeFormula L codeF codeR f).
    clear Hrecf f; intros n0.
    unfold codeFreeVarFormula at 1; fold g; unfold evalStrongRec.
    unfold evalComposeFunc, evalOneParamList, evalList.
    rewrite computeEvalStrongRecHelp.
    unfold evalComposeFunc, compose2, evalList, pred.  
    repeat rewrite cPairProjections1 || rewrite cPairProjections2.
    unfold g at 1; 
      repeat rewrite cPairProjections1 || rewrite cPairProjections2.
    rewrite (evalStrongRecHelp1 g (cPair 3 (cPair n n0)) n0).
    + simpl; reflexivity.
    + eapply Nat.lt_le_trans.
      * apply cPairLt2.
      * apply cPairLe3.
        -- apply le_n.
        -- apply cPairLe2.
Qed.

Lemma codeFreeVarFormulaIsPR : isPR 1 codeFreeVarFormula.
Proof.
  unfold codeFreeVarFormula; apply evalStrongRecIsPR.
  assert (H: isPR 1 (fun x : nat => pred (car x))).
  { apply compose1_1IsPR.
    - apply cPairPi1IsPR.
    - apply predIsPR.
  } 
  assert (H0: isPR 1 (fun x : nat => pred (pred (car x)))).
  { 
    apply compose1_1IsPR with (f := fun x : nat => pred (car x)).
    apply H. 
    apply predIsPR.
  } 
  assert (H1: isPR 1 (fun x : nat => pred (pred (pred (car x))))).
  { apply compose1_1IsPR with 
      (f := fun x : nat => pred (pred (car x))).
    apply H0. 
    apply predIsPR.
  } 
  apply compose2_3IsPR with
    (f1 := fun f recs : nat => car f)
    (f2 := fun f recs : nat =>
             switchPR (pred (car f))
               (switchPR (pred (pred (car f)))
                  (switchPR (pred (pred (pred (car f))))
                     (codeFreeVarTerms (cdr f))
                     (codeListRemove (car (cdr f))
                        (codeNth (f - S (cdr (cdr f))) recs)))
                  (codeNth (f - S (cdr f)) recs))
               (codeApp (codeNth (f - S (car (cdr f))) recs)
                  (codeNth (f - S (cdr (cdr f))) recs)))
    (f3 := fun f recs : nat =>
             codeApp (codeFreeVarTerm (car (cdr f)))
               (codeFreeVarTerm (cdr (cdr f)))).
  - apply filter10IsPR; apply cPairPi1IsPR.
  - apply compose2_3IsPR with
      (f1 := fun f recs : nat => pred (car f))
      (f2 := fun f recs : nat =>
               switchPR (pred (pred (car f)))
                 (switchPR (pred (pred (pred (car f))))
                    (codeFreeVarTerms (cdr f))
                    (codeListRemove (car (cdr f))
                       (codeNth (f - S (cdr (cdr f))) recs)))
                 (codeNth (f - S (cdr f)) recs))
      (f3 := fun f recs : nat =>
               codeApp (codeNth (f - S (car (cdr f))) recs)
                 (codeNth (f - S (cdr (cdr f))) recs)).
    + apply filter10IsPR with (g := fun x : nat => pred (car x)), H.
    + apply compose2_3IsPR with
        (f1 := fun f recs : nat => pred (pred (car f)))
        (f2 := fun f recs : nat =>
                 switchPR (pred (pred (pred (car f))))
                   (codeFreeVarTerms (cdr f))
                   (codeListRemove (car (cdr f))
                      (codeNth (f - S (cdr (cdr f))) recs)))
        (f3 := fun f recs : nat => codeNth (f - S (cdr f)) recs).
      * apply filter10IsPR with 
          (g := fun x : nat => pred (pred (car x))), H0.
      * apply compose2_3IsPR with
          (f1 := fun f recs : nat => pred (pred (pred (car f))))
          (f2 := fun f recs : nat => codeFreeVarTerms (cdr f))
          (f3 := fun f recs : nat =>
                   codeListRemove (car (cdr f))
                     (codeNth (f - S (cdr (cdr f))) recs)).
      -- apply filter10IsPR with 
           (g := fun x : nat => pred (pred (pred (car x)))), H1.
      -- apply filter10IsPR with 
           (g := fun f : nat => codeFreeVarTerms (cdr f)).
         apply compose1_1IsPR.
         ++ apply cPairPi2IsPR.
         ++ apply codeFreeVarTermsIsPR.
      -- apply compose2_2IsPR with
           (f := fun f recs : nat => car (cdr f))
           (g := fun f recs : nat => codeNth 
                                       (f - S (cddr f)) recs).
         ++ apply filter10IsPR with (g := fun f : nat => car (cdr f)).
            apply compose1_1IsPR.
            apply cPairPi2IsPR.
            apply cPairPi1IsPR.
         ++ apply compose2_2IsPR with
              (f := fun f recs : nat => f - S (cddr f))
              (g := fun f recs : nat => recs).
            apply filter10IsPR with (g := fun f : nat => f - S (cddr f)).
            apply compose1_2IsPR with
              (f := fun f : nat => f)
              (f' := fun f : nat => S (cddr f)).
            apply idIsPR.
            apply compose1_1IsPR with (f := fun f : nat => cddr f).
            apply compose1_1IsPR; apply cPairPi2IsPR.
            apply succIsPR.
            apply minusIsPR.
            apply pi2_2IsPR.
            apply codeNthIsPR.
         ++ apply codeListRemoveIsPR.
      -- apply switchIsPR.
      * apply compose2_2IsPR with
          (f := fun f recs : nat => f - S (cdr f))
          (g := fun f recs : nat => recs).
        -- apply filter10IsPR with (g := fun f : nat => f - S (cdr f)).
           apply compose1_2IsPR with 
             (f := fun f : nat => f) 
             (f' := fun f : nat => S (cdr f)).
           ++ apply idIsPR.
           ++ apply compose1_1IsPR.
              ** apply cPairPi2IsPR.
              ** apply succIsPR.
           ++ apply minusIsPR.
        -- apply pi2_2IsPR.
        -- apply codeNthIsPR.
      * apply switchIsPR.
    + apply compose2_2IsPR with
        (f := fun f recs : nat => codeNth (f - S (car (cdr f))) recs)
        (g := fun f recs : nat => codeNth (f - S (cddr f)) recs).
      * apply compose2_2IsPR with
          (f := fun f recs : nat => f - S (car (cdr f)))
          (g := fun f recs : nat => recs).
        apply filter10IsPR with (g := fun f : nat => f - S (car (cdr f))).
        -- apply compose1_2IsPR with
             (f := fun f : nat => f)
             (f' := fun f : nat => S (car (cdr f))).
           ++ apply idIsPR.
           ++ apply compose1_1IsPR with 
                (f := fun f : nat => car (cdr f)).
              ** apply compose1_1IsPR.
                 apply cPairPi2IsPR.
                 apply cPairPi1IsPR.
              ** apply succIsPR.
           ++ apply minusIsPR.
        -- apply pi2_2IsPR.
        -- apply codeNthIsPR.
      * apply compose2_2IsPR with
          (f := fun f recs : nat => f - S (cddr f))
          (g := fun f recs : nat => recs).
        -- apply filter10IsPR with
             (g := fun f : nat => f - S (cddr f)).
           apply  compose1_2IsPR with
             (f := fun f : nat => f)
             (f' := fun f : nat => S (cddr f)).
           ++ apply idIsPR.
           ++ apply compose1_1IsPR with 
                (f := fun f : nat => cddr f).
              ** apply compose1_1IsPR; apply cPairPi2IsPR.
              ** apply succIsPR.
           ++ apply minusIsPR.
        -- apply pi2_2IsPR.
        -- apply codeNthIsPR.
      * apply codeAppIsPR.
    + apply switchIsPR.
  - apply filter10IsPR  with
    (g := fun f : nat =>
          codeApp (codeFreeVarTerm (car (cdr f)))
            (codeFreeVarTerm (cddr f))).
    apply compose1_2IsPR with
      (f := fun f : nat => codeFreeVarTerm (car (cdr f)))
      (f' := fun f : nat => codeFreeVarTerm (cddr f)).
    + apply compose1_1IsPR with (f := fun f : nat => car (cdr f)).
      * apply compose1_1IsPR.
        -- apply cPairPi2IsPR.
        -- apply cPairPi1IsPR.
      * apply codeFreeVarTermIsPR.
    + apply compose1_1IsPR with (f := fun f : nat => cddr f).
      * apply compose1_1IsPR; apply cPairPi2IsPR.
      * apply codeFreeVarTermIsPR.
    + apply codeAppIsPR.
  - apply switchIsPR.
Qed.

Definition codeFreeVarListFormula : nat -> nat :=
  evalStrongRec 0
    (fun l recs : nat =>
     switchPR l
       (codeApp (codeFreeVarFormula (car (pred l)))
          (codeNth (l - S (cdr (pred l))) recs)) 0).

Lemma codeFreeVarListFormulaCorrect (l : list Formula):
 codeFreeVarListFormula (codeList (map (codeFormula L codeF codeR) l)) =
 codeList (freeVarListFormula L l).
Proof.
  unfold codeFreeVarListFormula;
    set
      (A :=
         fun l0 recs : nat =>
           switchPR l0
             (codeApp (codeFreeVarFormula (car (pred l0)))
                (codeNth (l0 - S (cdr (pred l0))) recs)) 0) 
    in *.
  induction l as [| a l Hrecl];
    unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList in |- *;
    rewrite computeEvalStrongRecHelp;
    unfold compose2, evalComposeFunc, evalOneParamList, evalList in |- *.
  - simpl; rewrite cPairProjections1; reflexivity.
  - unfold A at 1; rewrite evalStrongRecHelp1; simpl. 
    + repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
      rewrite Hrecl, codeFreeVarFormulaCorrect.
      apply codeAppCorrect.
    + apply Compat815.le_lt_n_Sm, cPairLe2A.
Qed.

Lemma codeFreeVarListFormulaIsPR : isPR 1 codeFreeVarListFormula.
Proof.
  unfold codeFreeVarListFormula; apply evalStrongRecIsPR.
  apply compose2_3IsPR with
    (f1 := fun l recs : nat => l)
    (f2 := fun l recs : nat =>
             codeApp (codeFreeVarFormula (car (pred l)))
               (codeNth (l - S (cdr (pred l))) recs))
    (f3 := fun l recs : nat => 0).
  - apply pi1_2IsPR.
  - apply compose2_2IsPR with
    (f := fun l recs : nat => codeFreeVarFormula (car (pred l)))
    (g := fun l recs : nat => codeNth (l - S (cdr (pred l))) recs).
    + apply filter10IsPR with
        (g := fun l : nat => codeFreeVarFormula (car (pred l))).
      apply compose1_1IsPR with (f := fun l : nat => car (pred l)).
      * apply compose1_1IsPR.
        -- apply predIsPR.
        -- apply cPairPi1IsPR.
      * apply codeFreeVarFormulaIsPR.
    + apply callIsPR with (g := fun l : nat => cdr (pred l)).
      apply compose1_1IsPR.
      * apply predIsPR.
      * apply cPairPi2IsPR.
    + apply codeAppIsPR.
  - apply filter10IsPR with (g := fun _ : nat => 0), const1_NIsPR.
  - apply switchIsPR.
Qed.

End Code_Free_Vars.

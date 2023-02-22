
Require Import primRec.
Require Import cPair.
Require Import Arith Lia.
Require Import code.
Require Import folProp.
Require Import extEqualNat.
Require Import codeList.
Require Import Compat815.
Import LispAbbreviations. 
Section Well_Formed_Term.

Variable L : Language.
Variable codeF : Functions L -> nat.
Variable codeArityF : nat -> nat.
Hypothesis codeArityFIsPR : isPR 1 codeArityF.
Hypothesis
  codeArityFIsCorrect1 :
    forall f : Functions L, codeArityF (codeF f) = S (arity L (inr _ f)).
Hypothesis
  codeArityFIsCorrect2 :
    forall n : nat, codeArityF n <> 0 -> exists f : Functions L, codeF f = n.

Let Term := Term L.
Let Terms := Terms L.
Let var := var L.
Let apply := apply L.

Definition wellFormedTermTerms : nat -> nat :=
  evalStrongRec 0
    (fun t recs : nat =>
     cPair
       (switchPR (cPairPi1 t)
          (charFunction 2 Nat.eqb (codeArityF (pred (cPairPi1 t)))
             (S (codeLength (cPairPi2 t))) *
           cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)) 1)
       (switchPR t
          (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs) *
           cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)) 1)).

Definition wellFormedTerm (t : nat) : nat := cPairPi1 (wellFormedTermTerms t).

Definition wellFormedTerms (ts : nat) : nat :=
  cPairPi2 (wellFormedTermTerms ts).

Lemma lengthTerms :
 forall (n : nat) (ts : Terms n), codeLength (codeTerms L codeF n ts) = n.
Proof.
  intros n ts; induction ts as [| n t ts Hrects].
  - reflexivity.
  - replace (codeTerms L codeF (S n) (Tcons L n t ts)) with
      (S (cPair (codeTerm L codeF t) (codeTerms L codeF n ts)));
      [ idtac | reflexivity ].
    unfold codeLength, evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
    set
      (A :=
         fun n0 Hrecs : nat =>
           switchPR n0 (S (codeNth (n0 - S (cPairPi2 (pred n0))) Hrecs)) 0). 
    rewrite computeEvalStrongRecHelp.
    unfold compose2, evalComposeFunc, evalOneParamList, evalList;
      unfold A at 1;
      rewrite evalStrongRecHelp1.
    + simpl; rewrite cPairProjections1,  cPairProjections2.
      now f_equal. 
    + generalize (cPair (codeTerm L codeF t) (codeTerms L codeF n ts)).
      simpl; intros n0; apply Nat.lt_succ_r.
      apply Nat.le_trans with (cPair (cPairPi1 n0) (cPairPi2 n0)).
      * apply cPairLe2.
      * rewrite cPairProjections; apply le_n.
Qed.

Lemma wellFormedTermCorrect1 :
  forall t : Term, wellFormedTerm (codeTerm L codeF t) = 1.
Proof.
  intros t; 
    set
      (A :=
         fun t recs : nat =>
           cPair
             (switchPR (cPairPi1 t)
                (charFunction 2 Nat.eqb (codeArityF (pred (cPairPi1 t)))
                   (S (codeLength (cPairPi2 t))) *
                   cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)) 1)
             (switchPR t
                (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs) *
                   cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)) 1)). 
  elim t using  Term_Terms_ind  with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             wellFormedTerms (codeTerms L codeF n ts) = 1); 
    simpl.
  -  intro n; unfold codeTerm, wellFormedTerm, wellFormedTermTerms.
     fold A; unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
     rewrite computeEvalStrongRecHelp.
     unfold compose2, evalComposeFunc, evalOneParamList, evalList; simpl;
       unfold A at 1;  repeat rewrite cPairProjections1; simpl; reflexivity.
  - intros f t0 H; replace (codeTerm L codeF (fol.apply L f t0)) with
      (cPair (S (codeF f)) (codeTerms L codeF _ t0)); [ idtac | reflexivity ].
    unfold wellFormedTerm, wellFormedTermTerms; fold A.
    unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList;
      rewrite computeEvalStrongRecHelp.
    unfold compose2, evalComposeFunc, evalOneParamList, evalList; simpl; unfold A at 1.
    repeat rewrite cPairProjections1.
    rewrite evalStrongRecHelp1.
    simpl; rewrite codeArityFIsCorrect1,  cPairProjections2; simpl.
    rewrite lengthTerms, Nat.eqb_refl; simpl. 
    rewrite Nat.add_comm; simpl; apply H.
    rewrite cPairProjections2; apply cPairLt2.
  - unfold wellFormedTerms, wellFormedTermTerms; fold A.
    unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList;
      rewrite computeEvalStrongRecHelp.
    unfold compose2, evalComposeFunc, evalOneParamList, evalList; simpl;
      rewrite cPairProjections1.
    unfold A; now rewrite cPairProjections2.
  - intros n t0 H t1 H0; unfold wellFormedTerms, wellFormedTermTerms.
    fold A; unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
    rewrite computeEvalStrongRecHelp.
    unfold compose2, evalComposeFunc, evalOneParamList, evalList; simpl;
      unfold A at 1; rewrite cPairProjections1; rewrite cPairProjections2.
    replace (codeTerms L codeF (S n) (Tcons L n t0 t1)) with
      (S (cPair (codeTerm L codeF t0) (codeTerms L codeF n t1)));
      [ idtac | reflexivity ].
    repeat rewrite evalStrongRecHelp1.
    + simpl; rewrite cPairProjections1.
      rewrite cPairProjections2.
      unfold wellFormedTerm, wellFormedTermTerms in H.
      unfold A; rewrite H.
      unfold wellFormedTerms, wellFormedTermTerms in H0; rewrite H0.
      reflexivity.
    + simpl; rewrite cPairProjections2.
      apply Nat.lt_succ_r.
      apply cPairLe2.
    + simpl; rewrite cPairProjections1.
      apply Nat.lt_succ_r.
      apply cPairLe1.
Qed.

Lemma wellFormedTermsCorrect1 (n : nat) (ts : Terms n):
  wellFormedTerms (codeTerms L codeF n ts) = 1.
Proof.
  set
    (A :=
       fun t recs : nat =>
         cPair
           (switchPR (cPairPi1 t)
              (charFunction 2 Nat.eqb (codeArityF (pred (cPairPi1 t)))
                 (S (codeLength (cPairPi2 t))) *
                 cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)) 1)
           (switchPR t
              (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs) *
                 cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)) 1)).
  induction ts as [| n t ts Hrects].
  - unfold wellFormedTerms, wellFormedTermTerms; fold A.
    unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList; 
      rewrite computeEvalStrongRecHelp.
    unfold compose2, evalComposeFunc, evalOneParamList, evalList; simpl.
    rewrite cPairProjections1; unfold A; now rewrite cPairProjections2.
  - unfold wellFormedTerms, wellFormedTermTerms; fold A.
    unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList;
      rewrite computeEvalStrongRecHelp;
      unfold compose2, evalComposeFunc, evalOneParamList, evalList; simpl.
    unfold A at 1; rewrite cPairProjections1,  cPairProjections2.
    replace (codeTerms L codeF (S n) (Tcons L n t ts)) with
      (S (cPair (codeTerm L codeF t) (codeTerms L codeF n ts)));
      [ idtac | reflexivity ].
    repeat rewrite evalStrongRecHelp1.  
    + simpl; rewrite cPairProjections1, cPairProjections2.
      replace (cPairPi1 (evalStrongRec 0 A (codeTerm L codeF t))) with
        (wellFormedTerm (codeTerm L codeF t)).
      * rewrite (wellFormedTermCorrect1 t).
        unfold wellFormedTerms, wellFormedTermTerms in Hrects.
        unfold A; now rewrite Hrects.
      * reflexivity.
    + simpl; rewrite cPairProjections2.
      apply Nat.lt_succ_r.
      apply cPairLe2.
    + simpl; rewrite cPairProjections1; apply Nat.lt_succ_r.
      apply cPairLe1.
Qed.

Lemma multLemma1 : forall a b : nat, a * b <> 0 -> a <> 0. 
Proof. 
  intros a b H H0; apply H; now subst a. 
Qed. 

Lemma multLemma2 : forall a b : nat, a * b <> 0 -> b <> 0.
Proof.
  intros a b H; rewrite Nat.mul_comm in H; eapply multLemma1, H.
Qed. 


Remark wellFormedTermTermsCorrect2 :
 forall n : nat,
 (wellFormedTerm n <> 0 -> exists t : Term, codeTerm L codeF t = n) /\
 (wellFormedTerms n <> 0 ->
  exists m : nat, (exists ts : Terms m, codeTerms L codeF m ts = n)).
Proof.
  assert
    (H: forall m n : nat,
        n < m ->
        (wellFormedTerm n <> 0 -> exists t : Term, codeTerm L codeF t = n) /\
          (wellFormedTerms n <> 0 ->
           exists m : nat, (exists ts : Terms m, codeTerms L codeF m ts = n))).
  { intro m; induction m as [| m Hrecm].
    - intros n H; inversion H.
    - intros n H; assert (H': n <= m) by lia.
      rewrite Nat.lt_eq_cases in H'; destruct H' as [H0 | H0].
      + apply Hrecm; auto.
      + unfold wellFormedTerm, wellFormedTerms, wellFormedTermTerms. 
        set
          (A :=
             fun t recs : nat =>
               cPair
                 (switchPR (cPairPi1 t)
                    (charFunction 2 Nat.eqb (codeArityF (pred (cPairPi1 t)))
                       (S (codeLength (cPairPi2 t))) *
                       cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)) 1)
                 (switchPR t
                    (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs) *
                       cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)) 1)). 
        unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList;
          rewrite computeEvalStrongRecHelp.
        unfold compose2, evalComposeFunc, evalOneParamList, evalList; simpl;
          rewrite cPairProjections1.
        split.
        * unfold A at 1; rewrite cPairProjections1.
          assert (H1: cPair (cPairPi1 n) (cPairPi2 n) = n)
          by apply cPairProjections.
          destruct (cPairPi1 n); simpl.
          -- exists (var (cPairPi2 n)).
             transitivity (cPair 0 (cPairPi2 n)).
             ++ reflexivity.
             ++ assumption.
          -- rewrite evalStrongRecHelp1.
             ++ simpl; intros H2.
                induction (eq_nat_dec (codeArityF n0) (S (codeLength (cPairPi2 n))))
                            as [a | b].
                ** assert (H3: wellFormedTerms (cPairPi2 n) <> 0)
                   by  eapply multLemma2, H2.
                   assert (H4: cPairPi2 n < m).
                   { apply Nat.lt_le_trans with (cPair (S n0) (cPairPi2 n)).
                     - apply cPairLt2. 
                     - rewrite H1, H0; apply le_n.
                   }
                   induction (Hrecm _ H4) as [_ H6]. 
                   induction (H6 H3) as [x [x0 H5]].
                   assert (H7: codeArityF n0 <> 0).
                   { intro H7; rewrite H7 in a; discriminate a. }
                   induction (codeArityFIsCorrect2 _ H7) as [x1 H8].
                   rewrite <- H8 in a.
                   rewrite codeArityFIsCorrect1 in a.
                   injection a; clear a.
                   intro H9; rewrite <- H5 in H9.
                   rewrite lengthTerms in H9.
                   cut (codeTerms L codeF x x0 = cPairPi2 n).
                   --- clear H5; generalize x0; clear x0.
                       rewrite <- H9.
                       intros x0 H5.
                       exists (apply x1 x0).
                       transitivity (cPair (S n0) (cPairPi2 n)).
                       +++ rewrite <- H8.
                           now rewrite <- H5.
                       +++ assumption.
                   --- assumption.
                ** rewrite nat_eqb_false in H2.
                   --- elim H2; reflexivity.
                   --- assumption.
             ++ apply Nat.lt_le_trans with (cPair (S n0) (cPairPi2 n)).
                ** apply cPairLt2.
                ** rewrite H1; apply le_n.
        * unfold A at 1; rewrite cPairProjections2; destruct n.
          -- simpl; intros H1; exists 0.
             exists (Tnil L); easy.
          -- repeat rewrite evalStrongRecHelp1.
             ++ simpl; intros H1; assert (H2: cPairPi1 n < m).
                { rewrite <- H0; apply Nat.lt_succ_r. 
                  apply Nat.le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
                  - apply cPairLe1.
                  - rewrite cPairProjections.
                    apply le_n.
                } assert (H3: cPairPi2 n < m).
                { rewrite <- H0.
                  apply Nat.lt_succ_r.
                  apply Nat.le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
                  - apply cPairLe2.
                  - rewrite cPairProjections; apply le_n.
                }
                induction (Hrecm _ H2) as [H4 H5]. 
                induction (Hrecm _ H3) as [_ H6].
                assert (H7: wellFormedTerm (cPairPi1 n) <> 0)
                  by  eapply multLemma1, H1.
                assert (H8: wellFormedTerms (cPairPi2 n) <> 0) 
                  by eapply multLemma2, H1.
                induction (H4 H7) as [x H9].
                induction (H6 H8) as [x0 H10].
                induction H10 as (x1, H10).
                exists (S x0), (Tcons L x0 x x1).
                rewrite <- (cPairProjections n).
                now rewrite <- H9, <- H10.
             ++ simpl; apply Nat.lt_succ_r.
                apply Nat.le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
                ** apply cPairLe2.
                ** rewrite cPairProjections; apply le_n.
             ++ apply Nat.lt_succ_r.
                apply Nat.le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
                ** apply cPairLe1.
                ** rewrite cPairProjections; apply le_n.
  }
  intros n; eapply H; apply Nat.lt_succ_diag_r .
Qed.

Lemma wellFormedTermCorrect2 :
  forall n : nat,
    wellFormedTerm n <> 0 -> exists t : Term, codeTerm L codeF t = n.
Proof.
  intro n; eapply proj1; apply wellFormedTermTermsCorrect2.
Qed.

Lemma wellFormedTermsCorrect2 :
  forall n : nat,
    wellFormedTerms n <> 0 ->
    exists m : nat, (exists ts : Terms m, codeTerms L codeF m ts = n).
Proof.
  intro n; eapply proj2; apply wellFormedTermTermsCorrect2.
Qed.

Remark wellFormedTermTermsIsPR : isPR 1 wellFormedTermTerms.
Proof.
  unfold wellFormedTermTerms; apply evalStrongRecIsPR.
  apply
    compose2_2IsPR
    with
    (f := fun t recs : nat =>
            switchPR (cPairPi1 t)
              (charFunction 2 Nat.eqb (codeArityF (pred (cPairPi1 t)))
                 (S (codeLength (cPairPi2 t))) *
                 cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)) 1)
    (g := fun t recs : nat =>
            switchPR t
              (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs) *
                 cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)) 1).
  - apply compose2_3IsPR with
      (f1 := fun t recs : nat => cPairPi1 t)
      (f2 := fun t recs : nat =>
               charFunction 2 Nat.eqb (codeArityF (pred (cPairPi1 t)))
                 (S (codeLength (cPairPi2 t))) *
                 cPairPi2 (codeNth (t - S (cPairPi2 t)) recs))
      (f3 := fun t recs : nat => 1).
    + apply filter10IsPR.
      apply cPairPi1IsPR.
    + apply compose2_2IsPR with
        (f := fun t recs : nat =>
                charFunction 2 Nat.eqb (codeArityF (pred (cPairPi1 t)))
                  (S (codeLength (cPairPi2 t))))
        (g := fun t recs : nat => cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)).
      * apply filter10IsPR with
          (g := fun t : nat =>
                  charFunction 2 Nat.eqb (codeArityF (pred (cPairPi1 t)))
                    (S (codeLength (cPairPi2 t)))).
        apply
          compose1_2IsPR
          with
          (f := fun t : nat => codeArityF (pred (cPairPi1 t)))
          (f' := fun t : nat => S (codeLength (cPairPi2 t))).
        -- apply compose1_1IsPR with (f := fun t : nat => pred (cPairPi1 t)).
           ++ apply compose1_1IsPR.
              ** apply cPairPi1IsPR.
              ** apply predIsPR.
           ++ apply codeArityFIsPR.
        -- apply compose1_1IsPR with (f := fun t : nat => codeLength (cPairPi2 t)).
           ++ apply compose1_1IsPR.
              ** apply cPairPi2IsPR.
              ** apply codeLengthIsPR.
           ++ apply succIsPR.
        -- apply eqIsPR.
      * apply compose2_1IsPR with 
          (f := fun t recs : nat => codeNth (t - S (cPairPi2 t)) recs).
        -- apply compose2_2IsPR with
             (f := fun t recs : nat => t - S (cPairPi2 t))
             (g := fun t recs : nat => recs).
           apply filter10IsPR with (g := fun t : nat => t - S (cPairPi2 t)).
           apply
             compose1_2IsPR
             with (f := fun t : nat => t) (f' := fun t : nat => S (cPairPi2 t)).
           apply idIsPR.
           apply compose1_1IsPR.
           apply cPairPi2IsPR.
           apply succIsPR.
           apply minusIsPR.
           apply pi2_2IsPR.
           apply codeNthIsPR.
        -- apply cPairPi2IsPR.
      * apply multIsPR.
    + apply filter10IsPR with (g := fun _ : nat => 1).
      apply const1_NIsPR.
    + apply switchIsPR.
  - apply
      compose2_3IsPR
      with
      (f1 := fun t recs : nat => t)
      (f2 := fun t recs : nat =>
               cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs) *
                 cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs))
      (f3 := fun t recs : nat => 1).
    + apply pi1_2IsPR.
    + apply compose2_2IsPR with
        (f := fun t recs : nat =>
                cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs))
        (g := fun t recs : nat =>
                cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)).
      * apply
          compose2_1IsPR
          with (f := fun t recs : nat => codeNth (t - S (cPairPi1 (pred t))) recs).
        -- apply compose2_2IsPR with
             (f := fun t recs : nat => t - S (cPairPi1 (pred t)))
             (g := fun t recs : nat => recs).
           ++ apply filter10IsPR with (g := fun t : nat => t - S (cPairPi1 (pred t))).
              apply
                compose1_2IsPR
                with (f := fun t : nat => t) 
                     (f' := fun t : nat => S (cPairPi1 (pred t))).
              ** apply idIsPR.
              ** apply compose1_1IsPR with (f := fun t : nat => cPairPi1 (pred t)).
                 --- apply compose1_1IsPR.
                     +++ apply predIsPR.
                     +++ apply cPairPi1IsPR.
                 --- apply succIsPR.
              ** apply minusIsPR.
           ++ apply pi2_2IsPR.
           ++ apply codeNthIsPR.
        -- apply cPairPi1IsPR.
      * apply compose2_1IsPR
          with (f := fun t recs : nat => codeNth (t - S (cPairPi2 (pred t))) recs).
        -- apply compose2_2IsPR with
             (f := fun t recs : nat => t - S (cPairPi2 (pred t)))
             (g := fun t recs : nat => recs).
           ++ apply filter10IsPR with (g := fun t : nat => t - S (cPairPi2 (pred t))).
              apply compose1_2IsPR with 
                (f := fun t : nat => t) (f' := fun t : nat => S (cPairPi2 (pred t))).
              ** apply idIsPR.
              ** apply compose1_1IsPR with (f := fun t : nat => cPairPi2 (pred t)).
                 --- apply compose1_1IsPR.
                     +++ apply predIsPR.
                     +++ apply cPairPi2IsPR.
                 --- apply succIsPR.
              ** apply minusIsPR.
           ++ apply pi2_2IsPR.
           ++ apply codeNthIsPR.
        -- apply cPairPi2IsPR.
      * apply multIsPR.
    + apply filter10IsPR with (g := fun _ : nat => 1).
      apply const1_NIsPR.
    + apply switchIsPR.
  - apply cPairIsPR.
Qed.

Lemma wellFormedTermIsPR : isPR 1 wellFormedTerm.
Proof.
  unfold wellFormedTerm; apply compose1_1IsPR.
  - apply wellFormedTermTermsIsPR.
  - apply cPairPi1IsPR.
Qed.

Lemma wellFormedTermsIsPR : isPR 1 wellFormedTerms.
Proof.
  unfold wellFormedTerms; apply compose1_1IsPR.
  - apply wellFormedTermTermsIsPR.
  - apply cPairPi2IsPR.
Qed.

Section Well_Formed_Formula.

Variable codeR : Relations L -> nat.
Variable codeArityR : nat -> nat.
Hypothesis codeArityRIsPR : isPR 1 codeArityR.
Hypothesis
  codeArityRIsCorrect1 :
    forall r : Relations L, codeArityR (codeR r) = S (arity L (inl _ r)).
Hypothesis
  codeArityRIsCorrect2 :
    forall n : nat, codeArityR n <> 0 -> exists r : Relations L, codeR r = n.

Let Formula := Formula L.
Let equal := equal L.
Let atomic := atomic L.

Let forallH := forallH L.

Definition wellFormedFormula : nat -> nat :=
  evalStrongRec 0
    (fun f recs : nat =>
     switchPR (cPairPi1 f)
       (switchPR (pred (cPairPi1 f))
          (switchPR (pred (pred (cPairPi1 f)))
             (switchPR (pred (pred (pred (cPairPi1 f))))
                (charFunction 2 Nat.eqb
                   (codeArityR (pred (pred (pred (pred (cPairPi1 f))))))
                   (S (codeLength (cPairPi2 f))) *
                 wellFormedTerms (cPairPi2 f))
                (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))
             (codeNth (f - S (cPairPi2 f)) recs))
          (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs *
           codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))
       (wellFormedTerm (cPairPi1 (cPairPi2 f)) *
        wellFormedTerm (cPairPi2 (cPairPi2 f)))).

Lemma wellFormedFormulaCorrect1 :
 forall f : Formula, wellFormedFormula (codeFormula L codeF codeR f) = 1.
Proof.
  intros f;
    set
      (A :=
         fun f recs : nat =>
           switchPR (cPairPi1 f)
             (switchPR (pred (cPairPi1 f))
                (switchPR (pred (pred (cPairPi1 f)))
                   (switchPR (pred (pred (pred (cPairPi1 f))))
                      (charFunction 2 Nat.eqb
                         (codeArityR (pred (pred (pred (pred (cPairPi1 f))))))
                         (S (codeLength (cPairPi2 f))) * wellFormedTerms (cPairPi2 f))
                      (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))
                   (codeNth (f - S (cPairPi2 f)) recs))
                (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs *
                   codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))
             (wellFormedTerm (cPairPi1 (cPairPi2 f)) *
                wellFormedTerm (cPairPi2 (cPairPi2 f)))).
  unfold wellFormedFormula; fold A;
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf]; intros;
 unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList in |- *;
 rewrite computeEvalStrongRecHelp;
 unfold compose2, evalComposeFunc, evalOneParamList, evalList in |- *;
 simpl in |- *; unfold A at 1 in |- *;
 repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
  - simpl; repeat rewrite wellFormedTermCorrect1; reflexivity.
  - simpl; rewrite wellFormedTermsCorrect1.
    rewrite codeArityRIsCorrect1.
    rewrite lengthTerms.
    rewrite Nat.eqb_refl; reflexivity.
  - rewrite evalStrongRecHelp1 with (m := codeFormula L codeF codeR f0).
    + rewrite evalStrongRecHelp1 with (m := codeFormula L codeF codeR f1).
      * simpl; now rewrite Hrecf1, Hrecf0.
      * eapply Nat.le_lt_trans; [ idtac | apply cPairLt2 ].
        apply cPairLe1.
    + eapply Nat.le_lt_trans; [ idtac | apply cPairLt2 ].
      apply cPairLe2.
  - rewrite evalStrongRecHelp1 with (m := codeFormula L codeF codeR f).
    + simpl; assumption.
    + apply cPairLt2.
  - rewrite evalStrongRecHelp1 with (m := codeFormula L codeF codeR f).
    + simpl; assumption.
    + eapply Nat.le_lt_trans; [ idtac | apply cPairLt2 ].
      apply cPairLe2.
Qed.

Lemma wellFormedFormulaCorrect2 :
  forall n : nat,
    wellFormedFormula n <> 0 ->
    exists f : Formula, codeFormula L codeF codeR f = n.
Proof.
  assert
    (H: forall m n : nat,
        n < m ->
        wellFormedFormula n <> 0 ->
        exists f : Formula, codeFormula L codeF codeR f = n).
  { intro m; induction m as [| m Hrecm].
    - intros n H; lia.
    - intros n H; assert (H': n <= m) by lia.
      rewrite Nat.lt_eq_cases in H'; destruct H'. 
      + apply Hrecm; auto.
      + unfold wellFormedFormula; 
          set
            (A :=
               fun f recs : nat =>
                 switchPR (cPairPi1 f)
                   (switchPR (pred (cPairPi1 f))
                      (switchPR (pred (pred (cPairPi1 f)))
                         (switchPR (pred (pred (pred (cPairPi1 f))))
                            (charFunction 2 Nat.eqb
                               (codeArityR (pred (pred (pred (pred (cPairPi1 f))))))
                               (S (codeLength (cPairPi2 f))) * 
                               wellFormedTerms (cPairPi2 f))
                            (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))
                         (codeNth (f - S (cPairPi2 f)) recs))
                      (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs *
                         codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))
                   (wellFormedTerm (cPairPi1 (cPairPi2 f)) *
                      wellFormedTerm (cPairPi2 (cPairPi2 f)))).
        unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList;
          rewrite computeEvalStrongRecHelp.
        unfold compose2, evalComposeFunc, evalOneParamList, evalList; simpl.
        rewrite cPairProjections1; unfold A at 1.
        assert (H1: cPair (cPairPi1 n) (cPairPi2 n) = n) 
        by apply cPairProjections.
        destruct (cPairPi1 n); simpl in |- *.
        intros H2; assert (H3: wellFormedTerm (cPairPi1 (cPairPi2 n)) <> 0).
        { eapply multLemma1; apply H2. }
        assert (H4: wellFormedTerm (cPairPi2 (cPairPi2 n)) <> 0) 
          by eapply multLemma2, H2.
        induction (wellFormedTermCorrect2 _ H3) as [x H5].
        induction (wellFormedTermCorrect2 _ H4) as [x0 H6].
        exists (equal x x0).
        simpl; rewrite H5,  H6,  cPairProjections.
        assumption.
        destruct n0.
        * simpl; assert (H2: cPairPi2 n < m).
          { apply Nat.lt_le_trans with (cPair 1 (cPairPi2 n)).
            - apply cPairLt2.
            - rewrite H1, H0; apply le_n.
          } assert (H3: cPairPi1 (cPairPi2 n) < m).
          { apply Nat.le_lt_trans with
              (cPair (cPairPi1 (cPairPi2 n)) (cPairPi2 (cPairPi2 n))).
            - apply cPairLe1.
            - now rewrite cPairProjections.
          } 
          assert (H4: cPairPi2 (cPairPi2 n) < m).
          { apply Nat.le_lt_trans with
              (cPair (cPairPi1 (cPairPi2 n)) (cPairPi2 (cPairPi2 n))).
            - apply cPairLe2.
            - now rewrite cPairProjections.
          }
          -- repeat rewrite evalStrongRecHelp1.
             ++ intros H5;
                  assert (H6: evalStrongRec 0 A (cPairPi1 (cPairPi2 n)) <> 0).
                { eapply multLemma1.
                  apply H5.
                }
                assert (H7: evalStrongRec 0 A (cPairPi2 (cPairPi2 n)) <> 0)
                  by eapply multLemma2, H5. 
                induction (Hrecm _ H3 H6) as [x H8].
                induction (Hrecm _ H4 H7) as [x0 H9].
                exists (impH x x0); simpl; rewrite H8, H9.
                now rewrite cPairProjections.
             ++ eapply Nat.lt_le_trans.
                ** apply H4.
                ** rewrite H0.
                   apply le_n.
             ++ eapply Nat.lt_le_trans.
                ** apply H3.
                ** rewrite H0.
                   apply le_n.
        * destruct n0.
          -- simpl; assert (H2: cPairPi2 n < m).
             { apply Nat.lt_le_trans with (cPair 2 (cPairPi2 n)).
               apply cPairLt2.
               rewrite H1.
               rewrite H0.
               apply le_n.
             } 
             repeat rewrite evalStrongRecHelp1.
             ++ intros H3; induction (Hrecm _ H2 H3).
                exists (notH x); simpl; now rewrite H4.
             ++ eapply Nat.lt_le_trans.
                ** apply H2.  
                ** rewrite H0; apply le_n.
          -- destruct n0.
             ++ simpl; assert (H2: cPairPi2 n < m).
                { apply Nat.lt_le_trans with (cPair 3 (cPairPi2 n)).
                  - apply cPairLt2.
                  - rewrite H1, H0; apply le_n.
                }
                assert (H3: cPairPi2 (cPairPi2 n) < m).
                { apply Nat.le_lt_trans with
                    (cPair (cPairPi1 (cPairPi2 n)) (cPairPi2 (cPairPi2 n))).
                  - apply cPairLe2.
                  - now rewrite cPairProjections.
                }
                repeat rewrite evalStrongRecHelp1.
                ** intros H4; induction (Hrecm _ H3 H4) as [x H5].
                   exists (forallH (cPairPi1 (cPairPi2 n)) x).
                   simpl; now rewrite H5,  cPairProjections.
                ** eapply Nat.lt_le_trans.
                   --- apply H3.
                   --- rewrite H0; apply le_n.
             ++ simpl;
                  induction (eq_nat_dec (codeArityR n0) (S (codeLength (cPairPi2 n))))
                            as [a | ?].
                ** assert (H2: codeArityR n0 <> 0).
                   { intro H2; rewrite H2 in a; discriminate a. }
                   induction (codeArityRIsCorrect2 _ H2) as [x H3].
                   intros H4; assert (H5: wellFormedTerms (cPairPi2 n) <> 0)
                   by eapply multLemma2, H4.
                   rewrite <- H3 in a.
                   rewrite codeArityRIsCorrect1 in a.
                   injection a.
                   clear a.
                   intros H6; induction (wellFormedTermsCorrect2 _ H5) as [x0 [x1 H7]].
                   rewrite <- H7 in H6.
                   rewrite lengthTerms in H6.
                   cut (codeTerms L codeF x0 x1 = cPairPi2 n).
                   --- generalize x1; clear H7 x1.
                       rewrite <- H6.
                       intros x1 H7; exists (atomic x x1); simpl; now rewrite H7, H3.
                   --- assumption.
                ** rewrite nat_eqb_false.
                   intros H2; simpl in H2; elim H2.
                   reflexivity.
                   assumption.
  } 
  intros n H0; eapply H.
  apply Nat.lt_succ_diag_r.
  assumption.
Qed.

Lemma wellFormedFormulaIsPR : isPR 1 wellFormedFormula.
Proof.
  unfold wellFormedFormula; apply evalStrongRecIsPR.
  assert (H: isPR 2 (fun f recs : nat => cPairPi1 f))
  by  apply filter10IsPR, cPairPi1IsPR.
  assert (H0: isPR 2 (fun f recs : nat => pred (cPairPi1 f))).
  { apply compose2_1IsPR with (f := fun f recs : nat => cPairPi1 f).
    - assumption.
    - apply predIsPR.
  } 
  assert (H1: isPR 2 (fun f recs : nat => pred (pred (cPairPi1 f)))).
  { apply compose2_1IsPR with (f := fun f recs : nat => pred (cPairPi1 f)).
    - assumption.
    - apply predIsPR.
  }
  assert (H2 : isPR 2 (fun f recs : nat => pred (pred (pred (cPairPi1 f))))).
  { apply compose2_1IsPR with (f := fun f recs : nat => pred (pred (cPairPi1 f))).
    - assumption.
    - apply predIsPR.
  }
  assert
    (H3: forall g : nat -> nat,
        isPR 1 g -> isPR 2 (fun f recs : nat => codeNth (f - S (g f)) recs)).
  { intros g H3.
    apply
      compose2_2IsPR
      with (f := fun f recs : nat => f - S (g f)) (g := fun f recs : nat => recs).
    - apply filter10IsPR with (g := fun f : nat => f - S (g f)).
      apply
        compose1_2IsPR with (f := fun f : nat => f) (f' := fun f : nat => S (g f)).
      + apply idIsPR.
      + apply compose1_1IsPR.
        * assumption.
        * apply succIsPR.
      + apply minusIsPR.
    - apply pi2_2IsPR.
    - apply codeNthIsPR.
  }
  apply
    compose2_3IsPR
    with
    (f1 := fun f recs : nat => cPairPi1 f)
    (f2 := fun f recs : nat =>
             switchPR (pred (cPairPi1 f))
               (switchPR (pred (pred (cPairPi1 f)))
                  (switchPR (pred (pred (pred (cPairPi1 f))))
                     (charFunction 2 Nat.eqb
                        (codeArityR (pred (pred (pred (pred (cPairPi1 f))))))
                        (S (codeLength (cPairPi2 f))) *
                        wellFormedTerms (cPairPi2 f))
                     (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))
                  (codeNth (f - S (cPairPi2 f)) recs))
               (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs *
                  codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))
    (f3 := fun f recs : nat =>
             wellFormedTerm (cPairPi1 (cPairPi2 f)) *
               wellFormedTerm (cPairPi2 (cPairPi2 f))).
  - assumption.
  - apply
      compose2_3IsPR
      with
      (f1 := fun f recs : nat => pred (cPairPi1 f))
      (f2 := fun f recs : nat =>
               switchPR (pred (pred (cPairPi1 f)))
                 (switchPR (pred (pred (pred (cPairPi1 f))))
                    (charFunction 2 Nat.eqb
                       (codeArityR (pred (pred (pred (pred (cPairPi1 f))))))
                       (S (codeLength (cPairPi2 f))) *
                       wellFormedTerms (cPairPi2 f))
                    (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))
                 (codeNth (f - S (cPairPi2 f)) recs))
      (f3 := fun f recs : nat =>
               codeNth (f - S (cPairPi1 (cPairPi2 f))) recs *
                 codeNth (f - S (cPairPi2 (cPairPi2 f))) recs).
    + assumption.
    + apply
        compose2_3IsPR
        with
        (f1 := fun f recs : nat => pred (pred (cPairPi1 f)))
        (f2 := fun f recs : nat =>
                 switchPR (pred (pred (pred (cPairPi1 f))))
                   (charFunction 2 Nat.eqb
                      (codeArityR (pred (pred (pred (pred (cPairPi1 f))))))
                      (S (codeLength (cPairPi2 f))) * wellFormedTerms (cPairPi2 f))
                   (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs))
        (f3 := fun f recs : nat => codeNth (f - S (cPairPi2 f)) recs).
      * assumption.
      * apply
          compose2_3IsPR
          with
          (f1 := fun f recs : nat => pred (pred (pred (cPairPi1 f))))
          (f2 := fun f recs : nat =>
                   charFunction 2 Nat.eqb
                     (codeArityR (pred (pred (pred (pred (cPairPi1 f))))))
                     (S (codeLength (cPairPi2 f))) * wellFormedTerms (cPairPi2 f))
          (f3 := fun f recs : nat => codeNth (f - S (cPairPi2 (cPairPi2 f))) recs).
        -- assumption.
        -- apply filter10IsPR with
             (g := fun f : nat =>
                     charFunction 2 Nat.eqb
                       (codeArityR (pred (pred (pred (pred (cPairPi1 f))))))
                       (S (codeLength (cPairPi2 f))) * wellFormedTerms (cPairPi2 f)).
           apply
             compose1_2IsPR
             with
             (f := fun f : nat =>
                     charFunction 2 Nat.eqb
                       (codeArityR (pred (pred (pred (pred (cPairPi1 f))))))
                       (S (codeLength (cPairPi2 f))))
             (f' := fun f : nat => wellFormedTerms (cPairPi2 f)).
           ++ apply
               compose1_2IsPR
               with
               (f := fun f : nat => codeArityR (pred (pred (pred (pred (cPairPi1 f))))))
               (f' := fun f : nat => S (codeLength (cPairPi2 f))).
              ** apply
                  compose1_1IsPR
                  with (f := fun f : nat => pred (pred (pred (pred (cPairPi1 f))))).
                 --- apply
                     compose1_1IsPR with
                     (f := fun f : nat => pred (pred (pred (cPairPi1 f))));
                     try apply predIsPR.
                     apply compose1_1IsPR 
                       with (f := fun f : nat => pred (pred (cPairPi1 f)));
                       try apply predIsPR.
                     apply compose1_1IsPR with (f := fun f : nat => pred (cPairPi1 f));
                       try apply predIsPR.
                     apply compose1_1IsPR.
                     apply cPairPi1IsPR.
                     apply predIsPR.
                 --- apply codeArityRIsPR.
              ** apply compose1_1IsPR with (f := fun f : nat => codeLength (cPairPi2 f)).
                 --- apply compose1_1IsPR.
                     +++ apply cPairPi2IsPR.
                     +++ apply codeLengthIsPR.
                 --- apply succIsPR.
              ** apply eqIsPR.
           ++ apply compose1_1IsPR.
              ** apply cPairPi2IsPR.
              ** apply wellFormedTermsIsPR.
           ++ apply multIsPR.
        -- apply H3 with (g := fun f : nat => cPairPi2 (cPairPi2 f)).
           apply compose1_1IsPR; apply cPairPi2IsPR.
        -- apply switchIsPR.
      * apply H3.
        apply cPairPi2IsPR.
      * apply switchIsPR.
    + apply
        compose2_2IsPR
        with
        (f := fun f recs : nat => codeNth (f - S (cPairPi1 (cPairPi2 f))) recs)
        (g := fun f recs : nat => codeNth (f - S (cPairPi2 (cPairPi2 f))) recs).
      * apply H3 with (g := fun f : nat => cPairPi1 (cPairPi2 f)).
        apply compose1_1IsPR.
        -- apply cPairPi2IsPR.
        -- apply cPairPi1IsPR.
      * apply H3 with (g := fun f : nat => cPairPi2 (cPairPi2 f)).
        apply compose1_1IsPR; apply cPairPi2IsPR.
      * apply multIsPR.
    + apply switchIsPR.
  - apply filter10IsPR with
      (g := fun f : nat =>
              wellFormedTerm (cPairPi1 (cPairPi2 f)) *
                wellFormedTerm (cPairPi2 (cPairPi2 f))).
    apply
      compose1_2IsPR
      with
      (f := fun f : nat => wellFormedTerm (cPairPi1 (cPairPi2 f)))
      (f' := fun f : nat => wellFormedTerm (cPairPi2 (cPairPi2 f))).
    + apply compose1_1IsPR with (f := fun f : nat => cPairPi1 (cPairPi2 f)).
      * apply compose1_1IsPR.
        -- apply cPairPi2IsPR.
        -- apply cPairPi1IsPR.
      * apply wellFormedTermIsPR.
    + apply compose1_1IsPR with (f := fun f : nat => cPairPi2 (cPairPi2 f)).
      * apply compose1_1IsPR; apply cPairPi2IsPR.
      * apply wellFormedTermIsPR.
    + apply multIsPR.
  - apply switchIsPR.
Qed.

End Well_Formed_Formula.

End Well_Formed_Term.

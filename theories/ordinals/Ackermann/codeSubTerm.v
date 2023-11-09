Require Import primRec.
Require Import cPair.
Require Import Arith.
Require Import folProp.
Require Import code.
Require Import extEqualNat.
Require Vector.
Require Import Compat815.
Import LispAbbreviations. 
Require Import NewNotations.
Import PRNotations.

Section Code_Substitute_Term.

Generalizable All Variables. 
Variable L : Language.
Context `(cL : Lcode L cf cr).

Let Formula := Formula L.
Let Formulas := Formulas L.
Let System := System L.
Let Term := Term L.
Let Terms := Terms L.

Definition codeSubTermTerms : nat -> nat -> nat -> nat :=
  evalStrongRec 2
    (fun t recs v s : nat =>
       cPair
         (switchPR (car t)
            (cPair (car t) (cdr (codeNth (t - S (cdr t)) recs)))
            (switchPR (charFunction 2 Nat.eqb (cdr t) v) s t))
         (switchPR t
            (S
               (cPair (car (codeNth (t - S (car (pred t))) recs))
                  (cdr (codeNth (t - S (cdr (pred t))) recs)))) 0)).

Definition codeSubTerm (t s v : nat) : nat :=
  car (codeSubTermTerms t s v).

Definition codeSubTerms (t s v : nat) : nat :=
  cdr (codeSubTermTerms t s v).

Lemma codeSubTermCorrect :
  forall (t : Term) (v : nat) (s : Term),
    codeSubTerm (codeTerm t) v (codeTerm s) =
      codeTerm (substT t v s).
Proof.
  set
    (g :=
       fun t0 recs v0 s0 : nat =>
         cPair
           (switchPR (car t0)
              (cPair (car t0) (cdr (codeNth (t0 - S (cdr t0)) recs)))
              (switchPR (charFunction 2 Nat.eqb (cdr t0) v0) s0 t0))
           (switchPR t0
              (S
                 (cPair (car (codeNth (t0 - S (car (pred t0))) recs))
                    (cdr (codeNth (t0 - S (cdr (pred t0))) recs)))) 0)).
  
  intros t v s; elim t using  Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             codeSubTerms (codeTerms ts) v (codeTerm s) =
               codeTerms (substTs ts v s)).
    - intro n; simpl; replace (codeTerm (var n)) with (cPair 0 n).
      + unfold codeSubTerm, codeSubTermTerms, evalStrongRec; simpl.
        repeat rewrite cPairProjections1 || rewrite cPairProjections2.
        simpl; induction (eq_nat_dec v n) as [a | b].
        * rewrite a, Nat.eqb_refl; simpl; reflexivity.
        * rewrite nat_eqb_false; simpl. 
          -- reflexivity.
          -- auto.
      + reflexivity.
    - intros f t0 H; simpl;
        transitivity
          (cPair (S (cf f))
             (codeTerms (substTs t0 v s))).
      + rewrite <- H; 
          replace (codeTerm (apply f t0)) 
          with
          (cPair (S (cf f))  (codeTerms  t0)).
        * generalize (cf f) 
            (codeTerms  t0).
          clear H t0 f; intros n n0; unfold codeSubTerm, codeSubTermTerms.
          fold g; unfold evalStrongRec, evalComposeFunc, evalOneParamList.
          unfold evalList; rewrite computeEvalStrongRecHelp.
          -- unfold compose2, evalComposeFunc, evalOneParamList, evalList.
             unfold pred;
               repeat rewrite cPairProjections1 || rewrite cPairProjections2.
             unfold g at 1;
               repeat rewrite cPairProjections1 || rewrite cPairProjections2.
             assert
               (H: extEqual _
                     (evalComposeFunc 2 1
                        (Vector.cons _ 
                           (evalStrongRecHelp 2 g (cPair (S n) n0)) 0
                           (Vector.nil _))
                        (fun b : nat => codeNth (cPair (S n) n0 - S n0) b))
                     (evalStrongRec 2 g n0)) 
               by (apply (evalStrongRecHelp2 2), cPairLt2).
             simpl in H; rewrite H; clear H.
             simpl; reflexivity.
        * reflexivity.
      + reflexivity.
    - simpl; unfold codeTerms, codeSubTerms, codeSubTermTerms, evalStrongRec.
      simpl;
        repeat rewrite cPairProjections1 || rewrite cPairProjections2.
      reflexivity.
    - intros n t0 H t1 H0 ; simpl.
      transitivity
        (S (cPair (codeTerm (substT t0 v s))
              (codeTerms (substTs t1 v s)))).
      + rewrite <- H, <-  H0.
        replace (codeTerms  (Tcons t0 t1)) 
          with
          (S (cPair (codeTerm t0) (codeTerms t1))).
        * generalize (codeTerm t0) (codeTerms t1).
          clear H0 t1 H t0 n; intros n n0.
          unfold codeSubTerms at 1; unfold codeSubTermTerms; fold g.
          unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
          rewrite computeEvalStrongRecHelp.
          unfold compose2, evalComposeFunc, evalOneParamList, evalList, pred.
          repeat rewrite cPairProjections1 || rewrite cPairProjections2.
          unfold g;
            repeat rewrite cPairProjections1 || rewrite cPairProjections2.
          unfold pred;
            repeat rewrite cPairProjections1 || rewrite cPairProjections2.
          assert
            (H: extEqual _
                  (evalComposeFunc 2 1
                     (Vector.cons _ (evalStrongRecHelp 2 g 
                                       (S (cPair n n0))) 0 (Vector.nil _))
                     (fun b : nat => codeNth (S (cPair n n0) - S n) b))
                  (evalStrongRec 2 g n)).
          { apply (evalStrongRecHelp2 2).
            apply Compat815.le_lt_n_Sm.
            apply cPairLe1.
          } 
          simpl in H; rewrite H; clear H.
          assert
            (H: extEqual _
                  (evalComposeFunc 2 1
                     (Vector.cons _ 
                        (evalStrongRecHelp 2 g (S (cPair n n0))) 0 
                        (Vector.nil _))
                     (fun b : nat => codeNth (S (cPair n n0) - S n0) b))
                  (evalStrongRec 2 g n0)).
          { apply (evalStrongRecHelp2 2).
            apply Compat815.le_lt_n_Sm.
            apply cPairLe2.
          } 
          simpl in H; rewrite H; clear H; simpl.
          reflexivity.
        * reflexivity.
      + reflexivity.
Qed.

Lemma codeSubTermsCorrect :
  forall (n : nat) (ts : Terms n) (v : nat) (s : Term),
    codeSubTerms (codeTerms ts) v (codeTerm s) =
      codeTerms  (substTs ts v s).
Proof.
  set
    (g :=
       fun t0 recs v0 s0 : nat =>
         cPair
           (switchPR (car t0)
              (cPair (car t0) (cdr (codeNth (t0 - S (cdr t0)) recs)))
              (switchPR (charFunction 2 Nat.eqb (cdr t0) v0) s0 t0))
           (switchPR t0
              (S
                 (cPair (car (codeNth (t0 - S (car (pred t0))) recs))
                    (cdr (codeNth (t0 - S (cdr (pred t0))) recs)))) 0)).
  intros n ts v s; induction ts as [| n t ts Hrects].
  - simpl; unfold codeTerms, codeSubTerms, codeSubTermTerms, evalStrongRec.
    simpl; repeat rewrite cPairProjections1 || rewrite cPairProjections2.
    reflexivity.
  - simpl; transitivity
             (S (cPair (codeTerm (substT t v s))
                   (codeTerms  (substTs ts v s)))).
    + rewrite <- Hrects, <- codeSubTermCorrect.
      replace (codeTerms (Tcons t ts)) with
        (S (cPair (codeTerm t) (codeTerms ts))).
      * generalize (codeTerm t) (codeTerms ts).
        clear Hrects ts t n; intros n n0.
        unfold codeSubTerms at 1; unfold codeSubTermTerms; fold g.
        unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
        rewrite computeEvalStrongRecHelp.
        unfold compose2, evalComposeFunc, evalOneParamList, evalList.
        unfold pred;
          repeat rewrite cPairProjections1 || rewrite cPairProjections2.
        unfold g at 1; 
          repeat rewrite cPairProjections1 || rewrite cPairProjections2.
        unfold pred;
          repeat rewrite cPairProjections1 || rewrite cPairProjections2.
        assert
          (H:
            extEqual _
               (evalComposeFunc 2 1
                  (Vector.cons _ (evalStrongRecHelp 2 g (S (cPair n n0))) 0 
                     (Vector.nil _))
                  (fun b : nat => codeNth (S (cPair n n0) - S n) b))
               (evalStrongRec 2 g n)).
        { apply (evalStrongRecHelp2 2).
          apply Compat815.le_lt_n_Sm.
          apply cPairLe1.
        } 
        simpl in H; rewrite H; clear H.
        assert
          (H: extEqual _
                (evalComposeFunc 2 1
                   (Vector.cons _ (evalStrongRecHelp 2 g 
                                     (S (cPair n n0))) 0 (Vector.nil _))
                   (fun b : nat => codeNth (S (cPair n n0) - S n0) b))
                (evalStrongRec 2 g n0)).
        { apply (evalStrongRecHelp2 2).
          apply Compat815.le_lt_n_Sm.
          apply cPairLe2.
        } 
        simpl in H; rewrite H; clear H.
        simpl; reflexivity.
      * reflexivity.
    + reflexivity.
Qed.

#[export] Instance codeSubTermTermsIsPR : isPR 3 codeSubTermTerms.
Proof.
  unfold codeSubTermTerms; apply evalStrongRecIsPR.
  apply compose4_2IsPR with
    (f1 := fun t recs v s : nat =>
             switchPR (car t)
               (cPair (car t)
                  (cdr (codeNth (t - S (cdr t)) recs)))
               (switchPR (charFunction 2 Nat.eqb (cdr t) v) s t))
    (f2 := fun t recs v s : nat =>
             switchPR t
               (S
                  (cPair (car (codeNth (t - S (car (pred t))) recs))
                     (cdr (codeNth (t - S (cdr (pred t))) recs)))) 0).
  - apply compose4_3IsPR with
      (f1 := fun t recs v s : nat => car t)
      (f2 := fun t recs v s : nat =>
               cPair (car t) (cdr (codeNth (t - S (cdr t)) recs)))
      (f3 := fun t recs v s : nat =>
               switchPR (charFunction 2 Nat.eqb (cdr t) v) s t).
    + apply filter1000IsPR with (g := cPairPi1).
      apply cPairPi1IsPR.
    + apply filter1100IsPR with
        (g := fun t recs : nat =>
                cPair (car t) (cdr (codeNth (t - S (cdr t)) recs))).
      apply compose2_2IsPR with
        (f := fun t recs : nat => car t)
        (g := fun t recs : nat => cdr (codeNth (t - S (cdr t)) recs)).
      * apply filter10IsPR with (g := cPairPi1).
        apply cPairPi1IsPR.
      * apply compose2_1IsPR with 
          (f := fun t recs : nat => codeNth (t - S (cdr t)) recs).
        -- apply compose2_2IsPR with
             (f := fun t recs : nat => t - S (cdr t))
             (g := fun t recs : nat => recs).
           ++ apply filter10IsPR with (g := fun t : nat => t - S (cdr t)).
              apply compose1_2IsPR with
                (f := fun t : nat => t) (f' := fun t : nat => S (cdr t)).
              ** apply idIsPR.
              ** apply compose1_1IsPR.
                 apply cPairPi2IsPR.
                 apply succIsPR.
              ** apply minusIsPR.
           ++ apply pi2_2IsPR.
           ++ apply codeNthIsPR.
        -- apply cPairPi2IsPR.
      * apply cPairIsPR.
    + apply filter1011IsPR with
        (g := fun t v s : nat =>
                switchPR (charFunction 2 Nat.eqb (cdr t) v) s t).
      apply compose3_3IsPR with
        (f1 := fun t v s : nat => charFunction 2 Nat.eqb (cdr t) v)
        (f2 := fun t v s : nat => s)
        (f3 := fun t v s : nat => t).
      * apply filter110IsPR with 
          (g := fun t v : nat => charFunction 2 Nat.eqb (cdr t) v).
        apply compose2_2IsPR with 
          (f := fun t v : nat => cdr t) (g := fun t v : nat => v).
        -- apply filter10IsPR.
           apply cPairPi2IsPR.
        -- apply pi2_2IsPR.
        -- apply eqIsPR.
      * apply pi3_3IsPR.
      * apply pi1_3IsPR.
      * apply switchIsPR.
    + apply switchIsPR.
  - apply filter1100IsPR with
      (g := fun t recs : nat =>
              switchPR t
                (S
                   (cPair (car (codeNth (t - S (car (pred t))) recs))
                      (cdr (codeNth (t - S (cdr (pred t))) recs)))) 0).
    apply compose2_3IsPR with
      (f1 := fun t recs : nat => t)
      (f2 := fun t recs : nat =>
               S
                 (cPair (car (codeNth (t - S (car (pred t))) recs))
                    (cdr (codeNth (t - S (cdr (pred t))) recs))))
      (f3 := fun t recs : nat => 0).
    + apply pi1_2IsPR.
    + apply compose2_1IsPR with
        (f := fun t recs : nat =>
                cPair (car (codeNth (t - S (car (pred t))) recs))
                  (cdr (codeNth (t - S (cdr (pred t))) recs))).
      * assert
          (H: forall g : nat -> nat,
              isPR 1 g ->
              isPR 2 (fun t recs : nat => 
                        g (codeNth (t - S (g (pred t))) recs))).
        { intros g H;
            apply compose2_1IsPR with 
            (f := fun t recs : nat => codeNth (t - S (g (pred t))) recs).
          - apply compose2_2IsPR with
              (f := fun t recs : nat => t - S (g (pred t)))
              (g := fun t recs : nat => recs).
            + apply filter10IsPR with 
                (g := fun t : nat => t - S (g (pred t))).
              apply compose1_2IsPR with 
                (f := fun t : nat => t) (f' := fun t : nat => S (g (pred t))).
              * apply idIsPR.
              * apply compose1_1IsPR with (f := fun t : nat => g (pred t)).
                -- apply compose1_1IsPR.
                   ++ apply predIsPR.
                   ++ auto.
                -- apply succIsPR.
              * apply minusIsPR.
            + apply pi2_2IsPR.
            + apply codeNthIsPR.
          - auto.
        } 
        apply compose2_2IsPR with
          (f := fun t recs : nat =>
                  car (codeNth (t - S (car (pred t))) recs))
          (g := fun t recs : nat =>
                  cdr (codeNth (t - S (cdr (pred t))) recs)).
        -- apply H.
           apply cPairPi1IsPR.
        -- apply H.
           apply cPairPi2IsPR.
        -- apply cPairIsPR.
      * apply succIsPR.
    + exists (PRcomp zeroFunc (PRnil _))%pr.
      simpl; auto.
    + apply switchIsPR.
  - apply cPairIsPR.
Qed.

#[export] Instance codeSubTermIsPR : isPR 3 codeSubTerm.
Proof.
  unfold codeSubTerm; apply compose3_1IsPR.
  - apply codeSubTermTermsIsPR.
  - apply cPairPi1IsPR.
Qed.

Lemma codeSubTermsIsPR : isPR 3 codeSubTerms.
Proof.
  unfold codeSubTerms; apply compose3_1IsPR.
  - apply codeSubTermTermsIsPR.
  - apply cPairPi2IsPR.
Qed.

End Code_Substitute_Term.

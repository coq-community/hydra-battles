(**  codeList.v

     Original script by Russel O'Connor 
*)

From hydras.Ackermann Require Import primRec  cPair.
From Coq Require Export Lists.List.
From hydras.Ackermann Require Import ListExt.
From Coq Require Import Arith.
From Coq Require Vector.
From hydras Require Import extEqualNat Compat815.

Definition codeLength : nat -> nat :=
  evalStrongRec 0
    (fun n Hrecs : nat =>
     switchPR n (S (codeNth (n - S (cPairPi2 (pred n))) Hrecs)) 0).

Lemma codeLengthCorrect :
 forall l : list nat, codeLength (codeList l) = length l.
Proof.
  induction l as [| a l Hrecl].
  - reflexivity.
  - simpl; unfold codeLength.
    set (f :=
           fun n Hrecs : nat =>
             switchPR n (S (codeNth (n - S (cPairPi2 (pred n))) Hrecs)) 0) 
      in *.
    unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
    rewrite computeEvalStrongRecHelp.
    unfold compose2, evalComposeFunc, evalList, f.
    rewrite evalStrongRecHelp1; simpl. 
    + rewrite cPairProjections1.
      apply eq_S.
      rewrite cPairProjections2; apply Hrecl; simpl.
    + apply Compat815.le_lt_n_Sm.
      generalize (cPair a (codeList l)); intro n.
      apply Nat.le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
      * apply cPairLe2.
      * rewrite cPairProjections; apply le_n.
Qed.

#[export] Instance codeLengthIsPR : isPR 1 codeLength.
Proof.
  unfold codeLength in |- *.
  apply evalStrongRecIsPR.
  apply
    compose2_3IsPR
    with
    (f1 := fun n Hrecs : nat => n)
    (f2 := fun n Hrecs : nat => 
             S (codeNth (n - S (cPairPi2 (pred n))) Hrecs))
    (f3 := fun n Hrecs : nat => 0).
  - apply pi1_2IsPR.
  - apply compose2_1IsPR with 
      (f := fun n Hrecs : nat => 
              codeNth (n - S (cPairPi2 (pred n))) Hrecs).
    + apply compose2_2IsPR with
        (f := fun n Hrecs : nat => n - S (cPairPi2 (pred n)))
        (g := fun n Hrecs : nat => Hrecs).
      * apply filter10IsPR with 
          (g := fun n : nat => n - S (cPairPi2 (pred n))).
        apply compose1_2IsPR
          with (f := fun n : nat => n) 
               (f' := fun n : nat => S (cPairPi2 (pred n))).
        -- apply idIsPR.
        -- apply compose1_1IsPR with 
             (f := fun n : nat => cPairPi2 (pred n)).
           ++ apply compose1_1IsPR.
              apply predIsPR.
              apply cPairPi2IsPR.
           ++ apply succIsPR.
        -- apply minusIsPR.
      * apply pi2_2IsPR.
      * apply codeNthIsPR.
    + apply succIsPR.
  - apply filter10IsPR with (g := fun _ : nat => 0).
    apply const1_NIsPR.
  - apply switchIsPR.
Qed.

Definition codeApp : nat -> nat -> nat :=
  evalStrongRec 1
    (fun n Hrecs p1 : nat =>
       switchPR n
         (S
            (cPair (cPairPi1 (pred n))
               (codeNth (n - S (cPairPi2 (pred n))) Hrecs))) p1).

Lemma codeAppCorrect (l1 l2 : list nat):
 codeApp (codeList l1) (codeList l2) = codeList (l1 ++ l2).
Proof.
   unfold codeApp;
     set
       (f :=
          fun n Hrecs p1 : nat =>
            switchPR n
              (S
                 (cPair (cPairPi1 (pred n))
                    (codeNth (n - S (cPairPi2 (pred n))) Hrecs))) p1).
   induction l1 as [| a l1 Hrecl1].
   - unfold evalStrongRec; simpl. 
     now rewrite cPairProjections1.
   - simpl; unfold evalStrongRec; unfold evalComposeFunc.  
     unfold evalOneParamList; rewrite computeEvalStrongRecHelp.
     unfold f at 2 ; unfold pred.
     set (n := S (cPair a (codeList l1))) in *; simpl. 
     repeat rewrite cPairProjections1 || rewrite cPairProjections2.
     replace (codeList (l1 ++ l2)) with
       (codeNth (cPair a (codeList l1) - codeList l1)
          (evalStrongRecHelp 1 f n (codeList l2))).
     + reflexivity.
     + assert
      (H: extEqual 1
         (evalComposeFunc 1 1 
            (Vector.cons _ (evalStrongRecHelp 1 f n) 0 (Vector.nil _))
            (fun b : nat => codeNth (n - S (codeList l1)) b))
         (evalStrongRec 1 f (codeList l1))).
       { apply (evalStrongRecHelp2 1).
         unfold n in |- *.
         apply Compat815.le_lt_n_Sm.
         apply cPairLe2.
       }     
       simpl in H; rewrite H; auto.
Qed.

#[export] Instance codeAppIsPR : isPR 2 codeApp.
Proof.
  unfold codeApp; apply evalStrongRecIsPR.
  apply compose3_3IsPR   with
    (f1 := fun n Hrecs p1 : nat => n)
    (f2 := fun n Hrecs p1 : nat =>
             S
               (cPair (cPairPi1 (pred n))
                  (codeNth (n - S (cPairPi2 (pred n))) Hrecs)))
    (f3 := fun n Hrecs p1 : nat => p1).
  - apply pi1_3IsPR.
  - apply filter110IsPR with
      (g := fun n Hrecs : nat =>
              S
                (cPair (cPairPi1 (pred n))
                   (codeNth (n - S (cPairPi2 (pred n))) Hrecs))).
    apply compose2_1IsPR with
      (g := S)
      (f := fun n Hrecs : nat =>
              cPair (cPairPi1 (pred n))
                (codeNth (n - S (cPairPi2 (pred n))) Hrecs)).
    +  apply compose2_2IsPR with
         (h := cPair)
         (f := fun n Hrecs : nat => cPairPi1 (pred n))
         (g := fun n Hrecs : nat => 
                 codeNth (n - S (cPairPi2 (pred n))) Hrecs).
       * apply filter10IsPR with (g := fun n : nat => cPairPi1 (pred n)).
         apply compose1_1IsPR.
         -- apply predIsPR.
         -- apply cPairPi1IsPR.
       * apply compose2_2IsPR with
           (h := codeNth)
           (f := fun n Hrecs : nat => n - S (cPairPi2 (pred n)))
           (g := fun n Hrecs : nat => Hrecs).
         -- apply filter10IsPR with
              (g := fun n : nat => n - S (cPairPi2 (pred n))).
            apply compose1_2IsPR with
              (g := minus)
              (f := fun n : nat => n)
              (f' := fun n : nat => S (cPairPi2 (pred n))).
            ++ apply idIsPR.
            ++ apply compose1_1IsPR with 
                 (g := S) (f := fun n : nat => cPairPi2 (pred n)).
               apply compose1_1IsPR.
               ** apply predIsPR.
               ** apply cPairPi2IsPR.
               ** apply succIsPR.
            ++ apply minusIsPR.
         -- apply pi2_2IsPR.
         -- apply codeNthIsPR.
       * apply cPairIsPR.
    + apply succIsPR.
  - apply pi3_3IsPR.
  - apply switchIsPR.
Qed.

Definition codeListRemove (a l : nat) : nat :=
  evalStrongRec 1
    (fun n Hrecs p1 : nat =>
     switchPR n
       (switchPR (charFunction 2 Nat.eqb (cPairPi1 (pred n)) p1)
          (codeNth (n - S (cPairPi2 (pred n))) Hrecs)
          (S
             (cPair (cPairPi1 (pred n))
                (codeNth (n - S (cPairPi2 (pred n))) Hrecs)))) 
       (codeList nil)) l a.

Lemma codeListRemoveCorrect (a : nat) (l : list nat):
 codeListRemove a (codeList l) = 
   codeList (List.remove  eq_nat_dec a l).
Proof.
  unfold codeListRemove;
    set
      (f :=
         fun n Hrecs p1 : nat =>
           switchPR n
             (switchPR (charFunction 2 Nat.eqb (cPairPi1 (pred n)) p1)
                (codeNth (n - S (cPairPi2 (pred n))) Hrecs)
                (S
                   (cPair (cPairPi1 (pred n))
                      (codeNth (n - S (cPairPi2 (pred n))) Hrecs)))) 
             (codeList nil)) in *.
  induction l as [| a0 l Hrecl].
  - simpl; unfold evalStrongRec; simpl; reflexivity.
  - unfold evalStrongRec, evalComposeFunc, evalOneParamList. 
    rewrite computeEvalStrongRecHelp.
    unfold f at 2 in |- *.
    unfold compose2 in |- *.
    set (n := codeList (a0 :: l)).
    set (A := n - S (cPairPi2 (pred n))).
    simpl;
      repeat rewrite cPairProjections1 || rewrite cPairProjections2.
    assert
      (H: extEqual 1
            (evalComposeFunc 1 1 (Vector.cons _ 
                                    (evalStrongRecHelp 1 f n) 0
                                    (Vector.nil _))
               (fun b : nat => codeNth (n - S (cPairPi2 (pred n))) b))
            (evalStrongRec 1 f (cPairPi2 (pred n)))).
    { apply (evalStrongRecHelp2 1); simpl; unfold n.
      rewrite cPairProjections2.
      simpl; apply Compat815.le_lt_n_Sm.
      apply cPairLe2.
    } 
    simpl in H.
    induction (Nat.eq_dec a0 a) as [a1 | b].
    + rewrite a1, Nat.eqb_refl; simpl; unfold A.
      rewrite H; rewrite cPairProjections2; auto. 
      destruct (Nat.eq_dec a a). 
        * auto. 
        * congruence.
    + rewrite nat_eqb_false; simpl. 
      replace (codeList (List.remove eq_nat_dec a l)) with
        (codeNth A (evalStrongRecHelp 1 f n a)).
      * destruct  (Nat.eq_dec a a0). 
        -- congruence. 
        -- simpl. f_equal. f_equal.  rewrite <- Hrecl. 
           rewrite cPairProjections2 in H. 
           rewrite <- H. unfold A. 
           simpl. now rewrite cPairProjections2. 
      * unfold A; rewrite H; simpl; rewrite cPairProjections2; auto.
      * auto.
Qed.

#[export] Instance codeListRemoveIsPR : isPR 2 codeListRemove.
Proof.
  unfold codeListRemove; apply swapIsPR; apply evalStrongRecIsPR.
  apply
    compose3_3IsPR
    with
    (g := switchPR)
    (f1 := fun n Hrecs p1 : nat => n)
    (f2 := fun n Hrecs p1 : nat =>
             switchPR (charFunction 2 Nat.eqb (cPairPi1 (pred n)) p1)
               (codeNth (n - S (cPairPi2 (pred n))) Hrecs)
               (S
                  (cPair (cPairPi1 (pred n))
                     (codeNth (n - S (cPairPi2 (pred n))) Hrecs))))
    (f3 := fun n Hrecs p1 : nat => codeList nil).
  - apply pi1_3IsPR.
  - assert
      (H: isPR 3 
            (fun n Hrecs p1 : nat => 
               codeNth (n - S (cPairPi2 (pred n))) Hrecs)).
    + apply filter110IsPR with 
        (g := fun n Hrecs : nat => 
                codeNth (n - S (cPairPi2 (pred n))) Hrecs).
      apply compose2_2IsPR with
        (h := codeNth)
        (f := fun n Hrecs : nat => n - S (cPairPi2 (pred n)))
        (g := fun n Hrecs : nat => Hrecs).
      * apply filter10IsPR with 
          (g := fun n : nat => n - S (cPairPi2 (pred n))).
        apply compose1_2IsPR with
          (g := minus)
          (f := fun n : nat => n)
          (f' := fun n : nat => S (cPairPi2 (pred n))).
        -- apply idIsPR.
        -- apply compose1_1IsPR with 
             (f := fun n : nat => cPairPi2 (pred n)).
           ++ apply compose1_1IsPR.
              ** apply predIsPR.
              ** apply cPairPi2IsPR.
           ++ apply succIsPR.
        -- apply minusIsPR.
      * apply pi2_2IsPR.
      * apply codeNthIsPR.
    + apply compose3_3IsPR with
        (g := switchPR)
        (f1 := fun n Hrecs p1 : nat =>
                 charFunction 2 Nat.eqb (cPairPi1 (pred n)) p1)
        (f2 := fun n Hrecs p1 : nat => 
                 codeNth (n - S (cPairPi2 (pred n))) Hrecs)
        (f3 := fun n Hrecs p1 : nat =>
                 S
                   (cPair (cPairPi1 (pred n))
                      (codeNth (n - S (cPairPi2 (pred n))) Hrecs))).
      * apply  filter101IsPR with 
          (g := fun n p1 : nat => 
                  charFunction 2 Nat.eqb (cPairPi1 (pred n)) p1).
        apply compose2_2IsPR with 
          (f := fun n p1 : nat => cPairPi1 (pred n))
          (g := fun n p1 : nat => p1).
        -- apply filter10IsPR with (g := fun n : nat => cPairPi1 (pred n)).
           apply compose1_1IsPR.
           ++ apply predIsPR.
           ++ apply cPairPi1IsPR.
        -- apply pi2_2IsPR.
        -- apply eqIsPR.
      * apply H.
      * apply compose3_1IsPR with
          (g := S)
          (f := fun n Hrecs _ : nat =>
                  cPair (cPairPi1 (pred n))
                    (codeNth (n - S (cPairPi2 (pred n))) Hrecs)).
        -- apply compose3_2IsPR with
             (g := cPair)
             (f1 := fun n Hrecs _ : nat => cPairPi1 (pred n))
             (f2 := fun n Hrecs _ : nat => 
                      codeNth (n - S (cPairPi2 (pred n))) Hrecs).
           ++ apply filter100IsPR with (g := fun n : nat => cPairPi1 (pred n)).
              apply compose1_1IsPR.
              apply predIsPR.
              apply cPairPi1IsPR.
           ++ apply H.
           ++ apply cPairIsPR.
        -- apply succIsPR.
      * apply switchIsPR.
  - exists (composeFunc 3 0 (PRnil _) zeroFunc).
    simpl; auto.
- apply switchIsPR.
Qed.

Definition codeIn (a l : nat) : nat :=
  evalStrongRec 1
    (fun n Hrecs p1 : nat =>
     switchPR n
       (switchPR (charFunction 2 Nat.eqb (cPairPi1 (pred n)) p1) 1
          (codeNth (n - S (cPairPi2 (pred n))) Hrecs)) 0) l a.

Lemma codeInCorrect (a : nat) (l : list nat) :
 codeIn a (codeList l) =
 match In_dec eq_nat_dec a l with
 | left _ => 1
 | right _ => 0
 end.
Proof.
  induction l as [| a0 l Hrecl]; simpl in |- *.
  - unfold codeIn, evalStrongRec; simpl; now rewrite cPairProjections1.
  - unfold codeIn, evalStrongRec; unfold evalComposeFunc, evalOneParamList.
    rewrite computeEvalStrongRecHelp.
    unfold evalList in |- *.
    set
      (f :=
         fun n Hrecs p1 : nat =>
           switchPR n
             (switchPR (charFunction 2 Nat.eqb (cPairPi1 (pred n)) p1) 1
                (codeNth (n - S (cPairPi2 (pred n))) Hrecs)) 0) 
      in *.
    set (m := cPairPi2 (pred (S (cPair a0 (codeList l))))) in *.
    set (n := S (cPair a0 (codeList l))) in *.
    simpl in |- *.
    repeat rewrite cPairProjections1.
    destruct (eq_nat_dec a0 a) as [a1 | b].
    + rewrite a1, Nat.eqb_refl; reflexivity. 
    + rewrite nat_eqb_false; simpl. 
      assert
        (H: extEqual _
              (evalComposeFunc 1 1 
                 (Vector.cons _ (evalStrongRecHelp 1 f n) 0 (Vector.nil _))
                 (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 f m)).
      { apply (evalStrongRecHelp2 1).
        unfold m, n; simpl. rewrite cPairProjections2.
        apply Compat815.le_lt_n_Sm.
        apply cPairLe2.
        } 
        simpl in H; rewrite H.
      unfold codeIn in Hrecl.
      move f after Hrecl;  fold f in Hrecl.
      unfold m, n in |- *.
      simpl in |- *.
      rewrite cPairProjections2.
      rewrite Hrecl.
      clear H f Hrecl.
      induction (In_dec eq_nat_dec a l) as [a1 | ?]; try reflexivity.
      assumption. 
Qed.

#[export] Instance codeInIsPR : isPR 2 codeIn.
Proof.
  unfold codeIn; apply swapIsPR.
  apply evalStrongRecIsPR.
  apply compose3_3IsPR with
    (g := switchPR)
    (f1 := fun n Hrecs p1 : nat => n)
    (f2 := fun n Hrecs p1 : nat =>
             switchPR (charFunction 2 Nat.eqb (cPairPi1 (pred n)) p1) 1
               (codeNth (n - S (cPairPi2 (pred n))) Hrecs))
    (f3 := fun n Hrecs p1 : nat => 0).
  - apply pi1_3IsPR.
  - apply compose3_3IsPR with
      (g := switchPR)
      (f1 := fun n Hrecs p1 : nat =>
               charFunction 2 Nat.eqb (cPairPi1 (pred n)) p1)
      (f2 := fun n Hrecs p1 : nat => 1)
      (f3 := fun n Hrecs p1 : nat => codeNth (n - S (cPairPi2 (pred n))) Hrecs).
    + apply filter101IsPR with 
        (g := fun n p1 : nat => charFunction 2 Nat.eqb (cPairPi1 (pred n)) p1).
      apply compose2_2IsPR with
        (h := charFunction 2 Nat.eqb)
        (f := fun n p1 : nat => cPairPi1 (pred n))
        (g := fun n p1 : nat => p1).
      * apply filter10IsPR with (g := fun n : nat => cPairPi1 (pred n)).
        apply compose1_1IsPR.
        -- apply predIsPR.
        -- apply cPairPi1IsPR.
      * apply pi2_2IsPR.
      * apply eqIsPR.
    + apply filter100IsPR with (g := fun _ : nat => 1).
      apply const1_NIsPR.
    + apply filter110IsPR with 
        (g := fun n Hrecs : nat => codeNth (n - S (cPairPi2 (pred n))) Hrecs).
      apply compose2_2IsPR with
        (h := codeNth)
        (f := fun n Hrecs : nat => n - S (cPairPi2 (pred n)))
        (g := fun n Hrecs : nat => Hrecs).
      apply filter10IsPR with
        (g := fun n : nat => n - S (cPairPi2 (pred n))).
      * apply compose1_2IsPR with
          (g := minus)
          (f := fun n : nat => n)
          (f' := fun n : nat => S (cPairPi2 (pred n))).
        apply idIsPR.
        apply compose1_1IsPR with 
          (g := S) (f := fun n : nat => cPairPi2 (pred n)).
        apply compose1_1IsPR.
        apply predIsPR.
        apply cPairPi2IsPR.
        apply succIsPR.
        apply minusIsPR.
      * apply pi2_2IsPR.
      * apply codeNthIsPR.
    + apply switchIsPR.
  - apply filter100IsPR with (g := fun _ : nat => 0).
    apply const1_NIsPR.
  - apply switchIsPR.
Qed.

Definition codeNoDup : nat -> nat :=
  evalStrongRec 0
    (fun l recs : nat =>
       switchPR l
         (switchPR
            (codeIn (cPairPi1 (pred l))
               (codeNth (l - S (cPairPi2 (pred l))) recs))
            (codeNth (l - S (cPairPi2 (pred l))) recs)
            (S
               (cPair (cPairPi1 (pred l))
                  (codeNth (l - S (cPairPi2 (pred l))) recs)))) 0).

Lemma codeNoDupCorrect (l : list nat) :
 codeNoDup (codeList l) = codeList (List.nodup eq_nat_dec l).
Proof.
  unfold codeNoDup;
    set
      (g :=
         fun l0 recs : nat =>
           switchPR l0
             (switchPR
                (codeIn (cPairPi1 (pred l0))
                   (codeNth (l0 - S (cPairPi2 (pred l0))) recs))
                (codeNth (l0 - S (cPairPi2 (pred l0))) recs)
                (S
                   (cPair (cPairPi1 (pred l0))
                      (codeNth (l0 - S (cPairPi2 (pred l0))) recs)))) 0) 
    in *.
  induction l as [| a l Hrecl].
  - simpl in |- *.
    unfold evalStrongRec; simpl; now rewrite cPairProjections1.
  - simpl; unfold evalStrongRec;
      unfold evalComposeFunc, evalOneParamList, evalList.
    rewrite computeEvalStrongRecHelp.
    unfold compose2, evalComposeFunc, evalOneParamList, evalList in |- *.
    unfold g at 1 in |- *.
    repeat rewrite evalStrongRecHelp1; unfold pred in |- *.
    repeat rewrite cPairProjections1 || rewrite cPairProjections2.
    + rewrite Hrecl; rewrite codeInCorrect.
      destruct (In_dec Nat.eq_dec a (List.nodup Nat.eq_dec l)). 
      destruct (in_dec Nat.eq_dec a l). 
      * reflexivity.
      *     rewrite nodup_In in i; contradiction.
      * destruct (in_dec Nat.eq_dec a l). 
     -- rewrite  nodup_In in n. contradiction.
     -- reflexivity.
    + simpl; apply Compat815.le_lt_n_Sm.
      apply cPairLe2A.
Qed.

#[export] Instance codeNoDupIsPR : isPR 1 codeNoDup.
Proof.
  unfold codeNoDup; apply evalStrongRecIsPR.
  apply compose2_3IsPR with
    (f1 := fun l recs : nat => l)
    (f2 := fun l recs : nat =>
             switchPR
               (codeIn (cPairPi1 (pred l))
                  (codeNth (l - S (cPairPi2 (pred l))) recs))
               (codeNth (l - S (cPairPi2 (pred l))) recs)
               (S
                  (cPair (cPairPi1 (pred l))
                     (codeNth (l - S (cPairPi2 (pred l))) recs))))
    (f3 := fun l recs : nat => 0).
  - apply pi1_2IsPR.
  - assert (H: isPR 2 
                 (fun l recs : nat => 
                    codeNth (l - S (cPairPi2 (pred l))) recs)).
    { apply callIsPR with (g := fun l : nat => cPairPi2 (pred l)).
      apply compose1_1IsPR.
      - apply predIsPR.
      - apply cPairPi2IsPR.
    } 
    apply compose2_3IsPR with
      (f1 := fun l recs : nat =>
               codeIn (cPairPi1 (pred l))
                 (codeNth (l - S (cPairPi2 (pred l))) recs))
      (f2 := fun l recs : nat => codeNth (l - S (cPairPi2 (pred l))) recs)
      (f3 := fun l recs : nat =>
               S
                 (cPair (cPairPi1 (pred l))
                    (codeNth (l - S (cPairPi2 (pred l))) recs))).
    + apply compose2_2IsPR with
        (f := fun l recs : nat => cPairPi1 (pred l))
        (g := fun l recs : nat => codeNth (l - S (cPairPi2 (pred l))) recs).
      * apply filter10IsPR with (g := fun l : nat => cPairPi1 (pred l)).
        apply compose1_1IsPR.
        -- apply predIsPR.
        -- apply cPairPi1IsPR.
      * assumption.
      * apply codeInIsPR.
    + assumption.
    + apply compose2_1IsPR with
        (f := fun l recs : nat =>
                cPair (cPairPi1 (pred l))
                  (codeNth (l - S (cPairPi2 (pred l))) recs)).
      * apply compose2_2IsPR with
          (f := fun l recs : nat => cPairPi1 (pred l))
          (g := fun l recs : nat => codeNth (l - S (cPairPi2 (pred l))) recs).
        -- apply filter10IsPR with (g := fun l : nat => cPairPi1 (pred l)).
           apply compose1_1IsPR.
           ++ apply predIsPR.
           ++ apply cPairPi1IsPR.
        -- assumption.
        -- apply cPairIsPR.
      * apply succIsPR.
    + apply switchIsPR.
  - apply filter10IsPR with (g := fun _ : nat => 0).
    apply const1_NIsPR.
  - apply switchIsPR.
Qed.


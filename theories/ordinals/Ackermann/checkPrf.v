Require Import primRec.
Require Import codeFreeVar.
Require Import codeSubFormula.
Require Import cPair.
From Coq Require Import Arith.
Require Import code.
Require Import folProp.
Require Import extEqualNat.
Require Import wellFormed.
Require Import folProof.
Require Import prLogic.
Require Import Compat815.
From Coq Require Import Lia.

Import LispAbbreviations. 

(* begin snippet context1 *)
Section Check_Proof.

Variable L : Language.
Variable codeF : Functions L -> nat.
Variable codeR : Relations L -> nat.
Variable codeArityF : nat -> nat.
Variable codeArityR : nat -> nat.

(* end snippet context1 *)

(* begin snippet context2 *)

Hypothesis codeArityFIsPR : isPR 1 codeArityF.

Hypothesis codeArityFIsCorrect1 :
  forall f : Functions L, codeArityF (codeF f) = S (arityF L f).

Hypothesis codeArityFIsCorrect2 :
    forall n : nat, codeArityF n <> 0 -> 
                    exists f : Functions L, codeF f = n.

Hypothesis codeArityRIsPR : isPR 1 codeArityR.

Hypothesis
  codeArityRIsCorrect1 :
    forall r : Relations L, codeArityR (codeR r) = S (arityR L r).

Hypothesis
  codeArityRIsCorrect2 :
    forall n : nat, codeArityR n <> 0 -> 
                    exists r : Relations L, codeR r = n.

Hypothesis codeFInj : forall f g : Functions L, 
    codeF f = codeF g -> f = g.

Hypothesis codeRInj : 
  forall R S : Relations L, codeR R = codeR S -> R = S.

(* end snippet context2 *)

Let Term := Term L.
Let Terms := Terms L.
Let Formula := Formula L.
Let wellFormedTerm := wellFormedTerm codeArityF.
Let wellFormedFormula := wellFormedFormula codeArityF codeArityR.
Let Prf := Prf L.

(*The wellFormedness requirement isn't really neccesary,
because and proof that used ``extra symbols'' could be
turned into a proof that only used symbols from the
axioms and the conclusion.

However making this assumption makes the proof easier *)

(* p is (cPair (formula) (proof of the Formula)) *)

Definition checkPrfAXM (p recs : nat) :=
  switchPR (charFunction 2 Nat.eqb (cddr p) (car p))
    (S (S (cPair (car p) 0))) 0.

Lemma checkPrfAXMIsPR : isPR 2 checkPrfAXM.
Proof.
  unfold checkPrfAXM.
  apply
    filter10IsPR
    with
    (g := fun p : nat =>
            switchPR
              (charFunction 2 Nat.eqb (cddr p) (car p))
              (S (S (cPair (car p) 0))) 0).
  apply
    compose1_3IsPR
    with
    (f1 := fun p : nat =>
             charFunction 2 Nat.eqb (cddr p) (car p))
    (f2 := fun p : nat => S (S (cPair (car p) 0)))
    (f3 := fun p : nat => 0).
  - apply compose1_2IsPR with (f := fun p : nat => cddr p).
    + apply compose1_1IsPR.
      * apply cPairPi2IsPR.
      * apply cPairPi2IsPR.
    + apply cPairPi1IsPR.
    + apply eqIsPR.
  - apply compose1_1IsPR with 
      (f := fun p : nat => S (cPair (car p) 0)).
    + apply compose1_1IsPR with (f := fun p : nat => cPair (car p) 0).
      * apply compose1_2IsPR with (f' := fun p : nat => 0).
        -- apply cPairPi1IsPR.
        -- apply const1_NIsPR.
        -- apply cPairIsPR.
      * apply succIsPR.
    + apply succIsPR.
  - apply const1_NIsPR.
  - apply switchIsPR.
Qed.

Definition checkPrfMP (p recs : nat) :=
  switchPR
    (wellFormedFormula (car (cdr (cdr (cdr p)))) *
     (charFunction 2 Nat.eqb (car (car (cdr (cdr p))))
        (codeImp (car (cdr (cdr (cdr p)))) (car p)) *
      (codeNth (p - S (car (cdr (cdr p)))) recs *
       codeNth (p - S (cdddr p)) recs)))
    (S
       (codeApp
          (pred (codeNth (p - S (car (cdr (cdr p)))) recs))
          (pred (codeNth (p - S (cdr (cdr (cdr p)))) recs))))
    0.

Lemma checkPrfMPIsPR : isPR 2 checkPrfMP.
Proof.
  unfold checkPrfMP in |- *.
  apply compose2_3IsPR with
    (f1 := fun p recs : nat =>
             wellFormedFormula (car (cdr (cdr (cdr p)))) *
               (charFunction 2 Nat.eqb
                  (car (car (cdr (cdr p))))
                  (codeImp (car (cdr (cdr (cdr p))))
                     (car p)) *
                  (codeNth (p - S (car (cdr (cdr p)))) recs *
                     codeNth (p - S (cdr (cdr (cdr p)))) recs)))
    (f2 := fun p recs : nat =>
          S
            (codeApp
               (pred
                  (codeNth (p - S (car (cdr (cdr p)))) recs))
               (pred
                  (codeNth (p - S (cdr (cdr (cdr p)))) recs))))
    (f3 := fun p recs : nat => 0).
  - apply compose2_2IsPR with
    (f := fun p recs : nat =>
          wellFormedFormula (car (cdddr p)))
    (g := fun p recs : nat =>
          charFunction 2 Nat.eqb
            (car (car (cdr (cdr p))))
            (codeImp (car (cdr (cdr (cdr p))))
               (car p)) *
          (codeNth (p - S (car (cdr (cdr p)))) recs *
           codeNth (p - S (cdr (cdr (cdr p)))) recs)).
    + apply filter10IsPR with
        (g := 
           fun p : nat =>
             wellFormedFormula (car (cdddr p))).
      apply
        compose1_1IsPR
        with (f := fun p : nat => car (cdr (cdr (cdr p)))).
      * apply compose1_1IsPR with
          (f := fun p : nat => cdddr p).
        -- apply compose1_1IsPR with 
             (f := fun p : nat => cddr p).
           ++ apply compose1_1IsPR; apply cPairPi2IsPR.
           ++ apply cPairPi2IsPR.
        -- apply cPairPi1IsPR.
      * unfold wellFormedFormula in |- *.
        apply wellFormedFormulaIsPR.
        apply codeArityFIsPR.
        apply codeArityRIsPR.
    + apply compose2_2IsPR with
        (f := fun p recs : nat =>
                charFunction 2 Nat.eqb
                  (car (car (cdr (cdr p))))
                  (codeImp (car (cdr (cdr (cdr p))))
                     (car p)))
        (g := fun p recs : nat =>
                codeNth (p - S (car (cdr (cdr p)))) recs *
                  codeNth (p - S (cdr (cdr (cdr p)))) recs).
      apply
        filter10IsPR
        with
        (g := fun p : nat =>
                charFunction 2 Nat.eqb
                  (car (car (cdr (cdr p))))
                  (codeImp (car (cdr (cdr (cdr p))))
                     (car p))).
      * apply compose1_2IsPR with
          (f := fun p : nat => car (car (cdr (cdr p))))
          (f' := fun p : nat =>
                   codeImp (car (cdr (cdr (cdr p)))) 
                     (car p)).
        -- apply compose1_1IsPR with
             (f := fun p : nat => car (cdr (cdr p))).
           ++ apply compose1_1IsPR with 
                (f := fun p : nat => cdr (cdr p)).
              ** apply compose1_1IsPR; apply cPairPi2IsPR.
              ** apply cPairPi1IsPR.
           ++ apply cPairPi1IsPR.
        -- apply compose1_2IsPR with 
             (f := fun p : nat => car (cdr (cdr (cdr p)))).
           ++ apply compose1_1IsPR with 
                (f := fun p : nat => cdr (cdr (cdr p))).
              ** apply compose1_1IsPR with
                   (f := fun p : nat => cdr (cdr p)).
                 apply compose1_1IsPR; apply cPairPi2IsPR.
                 apply cPairPi2IsPR.
              ** apply cPairPi1IsPR.
           ++ apply cPairPi1IsPR.
           ++ apply codeImpIsPR.
        -- apply eqIsPR.
      * apply compose2_2IsPR with
          (f := fun p recs : nat =>
                  codeNth (p - S (car (cdr (cdr p)))) recs)
          (g := fun p recs : nat =>
                  codeNth (p - S (cdr (cdr (cdr p)))) recs).
        -- apply callIsPR with 
             (g := fun p : nat => car (cdr (cdr p))).
           apply compose1_1IsPR with 
             (f := fun p : nat => cdr (cdr p)).
           ++ apply compose1_1IsPR; apply cPairPi2IsPR.
           ++ apply cPairPi1IsPR.
        -- apply callIsPR with 
             (g := fun p : nat => cdr (cdr (cdr p))).
           apply compose1_1IsPR with 
             (f := fun p : nat => cdr (cdr p)).
           ++ apply compose1_1IsPR; apply cPairPi2IsPR.
           ++ apply cPairPi2IsPR.
        -- apply multIsPR.
      * apply multIsPR.
    + apply multIsPR.
  - apply compose2_1IsPR with
      (f := fun p recs : nat =>
            codeApp
              (pred (codeNth (p - S (car (cdr (cdr p)))) recs))
              (pred (codeNth (p - S (cdr (cdr (cdr p)))) recs))).
    apply
      compose2_2IsPR
      with
      (f := fun p recs : nat =>
              pred (codeNth (p - S (car (cdr (cdr p)))) recs))
      (g := fun p recs : nat =>
          pred (codeNth (p - S (cdr (cdr (cdr p)))) recs)).
    + apply
      compose2_1IsPR
      with
      (f := fun p recs : nat =>
              codeNth (p - S (car (cdr (cdr p)))) recs).
      * apply callIsPR with
          (g := fun p : nat => car (cdr (cdr p))).
        apply compose1_1IsPR with (f := fun p : nat => cdr (cdr p)).
        -- apply compose1_1IsPR; apply cPairPi2IsPR.
        -- apply cPairPi1IsPR.
      * apply predIsPR.
    + apply compose2_1IsPR with
        (f := fun p recs : nat =>
                codeNth (p - S (cdr (cdr (cdr p)))) recs).
      * apply callIsPR with 
          (g := fun p : nat => cdr (cdr (cdr p))).
        apply compose1_1IsPR with (f := fun p : nat => cdr (cdr p)).
        -- apply compose1_1IsPR; apply cPairPi2IsPR.
        -- apply cPairPi2IsPR.
      * apply predIsPR.
    + apply codeAppIsPR.
    + apply succIsPR.
  - apply filter10IsPR with (g := fun _ : nat => 0).
    apply const1_NIsPR.
  - apply switchIsPR.
Qed.

Definition checkPrfGEN (p recs : nat) :=
  switchPR
    (charFunction 2 Nat.eqb
       (cPair 3
          (cPair (car (cdr (cdr p)))
             (car (cdr (cdr (cdr p)))))) 
       (car p) *
     (codeNth (p - S (cdr (cdr (cdr p)))) recs *
      (1 -
       codeIn (car (cdr (cdr p)))
         (codeFreeVarListFormula
            (pred (codeNth (p - S (cdr (cdr (cdr p)))) recs))))))
    (codeNth (p - S (cdr (cdr (cdr p)))) recs) 0.

Lemma checkPrfGENIsPR : isPR 2 checkPrfGEN.
Proof.
  unfold checkPrfGEN;
    apply compose2_3IsPR with
    (f1 := fun p recs : nat =>
             charFunction 2 Nat.eqb
               (cPair 3
                  (cPair (car (cdr (cdr p)))
                     (car (cdr (cdr (cdr p))))))
               (car p) *
               (codeNth (p - S (cdr (cdr (cdr p)))) recs *
                  (1 -
                     codeIn (car (cdr (cdr p)))
                       (codeFreeVarListFormula
                          (pred
                             (codeNth (p - S (cdr 
                                                (cdr (cdr p))))
                                recs))))))
    (f2 := fun p recs : nat =>
             codeNth (p - S (cdr (cdr (cdr p)))) recs)
    (f3 := fun p recs : nat => 0).
  - apply compose2_2IsPR with
      (f := fun p recs : nat =>
              charFunction 2 Nat.eqb
                (cPair 3
                   (cPair (car (cdr (cdr p)))
                      (car (cdr (cdr (cdr p))))))
                (car p))
      (g := fun p recs : nat =>
              codeNth (p - S (cdr (cdr (cdr p)))) recs *
                (1 -
                   codeIn (car (cdr (cdr p)))
                     (codeFreeVarListFormula
                        (pred
                           (codeNth (p - S (cdr (cdr (cdr p)))) 
                              recs))))).
    + apply filter10IsPR with
        (g := fun p : nat =>
                charFunction 2 Nat.eqb
                  (cPair 3
                     (cPair (car (cdr (cdr p)))
                        (car (cdr (cdr (cdr p))))))
                  (car p)).
      apply
        compose1_2IsPR
        with
        (f := fun p : nat =>
                cPair 3
                  (cPair (car (cdr (cdr p)))
                     (car (cdr (cdr (cdr p))))))
        (f' := fun p : nat => car p).
      * apply compose1_2IsPR with
          (f := fun p : nat => 3)
          (f' := fun p : nat =>
                   cPair (car (cdr (cdr p)))
                     (car (cdr (cdr (cdr p))))).
        -- apply const1_NIsPR.
        -- apply compose1_2IsPR with
             (f := fun p : nat => car (cdr (cdr p)))
             (f' := fun p : nat => car (cdr (cdr (cdr p)))).
           ++ apply compose1_1IsPR with 
                (f := fun p : nat => cdr (cdr p)).
              apply compose1_1IsPR; apply cPairPi2IsPR.
              apply cPairPi1IsPR.
           ++ apply compose1_1IsPR with 
                (f := fun p : nat => cdr (cdr (cdr p))).
              apply compose1_1IsPR with 
                (f := fun p : nat => cdr (cdr p)).
              apply compose1_1IsPR; apply cPairPi2IsPR.
              apply cPairPi2IsPR.
              apply cPairPi1IsPR.
           ++ apply cPairIsPR.
        -- apply cPairIsPR.
      * apply cPairPi1IsPR.
      * apply eqIsPR.
    + apply compose2_2IsPR with
        (f := fun p recs : nat =>
                codeNth (p - S (cdr (cdr (cdr p)))) recs)
        (g := fun p recs : nat =>
                1 -
                  codeIn (car (cdr (cdr p)))
                    (codeFreeVarListFormula
                       (pred
                          (codeNth (p - S (cdr (cdr (cdr p)))) 
                             recs)))).
      * apply callIsPR with 
          (g := fun p : nat => cdr (cdr (cdr p))).
        apply compose1_1IsPR with (f := fun p : nat => cdr (cdr p)).
        -- apply compose1_1IsPR; apply cPairPi2IsPR.
        -- apply cPairPi2IsPR.
      * apply compose2_2IsPR with
          (f := fun p recs : nat => 1)
          (g := fun p recs : nat =>
                  codeIn (car (cdr (cdr p)))
                    (codeFreeVarListFormula
                       (pred
                          (codeNth (p - S (cdr 
                                             (cdr (cdr p)))) 
                             recs)))).
        -- apply filter10IsPR with (g := fun _ : nat => 1).
           apply const1_NIsPR.
        -- apply compose2_2IsPR with
             (f := fun p recs : nat => car (cdr (cdr p)))
             (g := fun p recs : nat =>
                     codeFreeVarListFormula
                       (pred (codeNth 
                                (p - S (cdr 
                                          (cdr (cdr p)))) recs))).
           apply filter10IsPR with
             (g := fun p : nat => car (cdr (cdr p))).
           ++ apply compose1_1IsPR with 
                (f := fun p : nat => cdr (cdr p)).
              ** apply compose1_1IsPR; apply cPairPi2IsPR.
              ** apply cPairPi1IsPR.
           ++ apply compose2_1IsPR with
                (f := fun p recs : nat =>
                        pred (codeNth (p - S (cdr 
                                                (cdr (cdr p)))) 
                                recs)).
              ** apply compose2_1IsPR with
                   (f := fun p recs : nat =>
                           codeNth (p - S (cdr (cdr (cdr p)))) 
                             recs).
                 apply callIsPR with 
                   (g := fun p : nat => cdr (cdr (cdr p))).
                 apply compose1_1IsPR with
                   (f := fun p : nat => cdr (cdr p)).
                 apply compose1_1IsPR; apply cPairPi2IsPR.
                 apply cPairPi2IsPR.
                 apply predIsPR.
              ** apply codeFreeVarListFormulaIsPR.
           ++ apply codeInIsPR.
        -- apply minusIsPR.
      * apply multIsPR.
    + apply multIsPR.
  - apply callIsPR with 
      (g := fun p : nat => cdr (cdr (cdr p))).
    apply compose1_1IsPR with (f := fun p : nat => cdr (cdr p)).
    + apply compose1_1IsPR; apply cPairPi2IsPR.
    + apply cPairPi2IsPR.
  - apply filter10IsPR with (g := fun _ : nat => 0).
    apply const1_NIsPR.
  - apply switchIsPR.
Qed.

Definition checkPrfIMP1 (p recs : nat) :=
  let A := car (cdr (cdr p)) in
  let B := cdr (cdr (cdr p)) in
  charFunction 2 Nat.eqb (cPair 1 (cPair A (cPair 1 (cPair B A))))
    (car p).

Lemma checkPrfIMP1IsPR : isPR 2 checkPrfIMP1.
Proof.
  unfold checkPrfIMP1; apply filter10IsPR with
    (g := fun p : nat =>
          charFunction 2 Nat.eqb
            (cPair 1
               (cPair (car (cdr (cdr p)))
                  (cPair 1
                     (cPair (cdr (cdr (cdr p)))
                        (car (cdr (cdr p))))))) 
            (car p)).
  assert (H: isPR 1 (fun p : nat => car (cdr (cdr p)))).
  { apply compose1_1IsPR with (f := fun p : nat => cdr (cdr p)).
    - apply compose1_1IsPR; apply cPairPi2IsPR.
    - apply cPairPi1IsPR.
  } 
  assert (H0: isPR 1 (fun p : nat => cdr (cdr (cdr p)))).
  { apply compose1_1IsPR with (f := fun p : nat => cdr (cdr p)).
    - apply compose1_1IsPR; apply cPairPi2IsPR.
    - apply cPairPi2IsPR.
  }
  apply compose1_2IsPR with
    (f := fun p : nat =>
            cPair 1
              (cPair (car (cdr (cdr p)))
                 (cPair 1
                    (cPair (cdr (cdr (cdr p)))
                       (car (cdr (cdr p))))))).
  apply compose1_2IsPR with
    (f := fun p : nat => 1)
    (f' := fun p : nat =>
             cPair (car (cdr (cdr p)))
               (cPair 1
                  (cPair (cdr (cdr (cdr p)))
                     (car (cdr (cdr p)))))).
  - apply const1_NIsPR.
  - apply compose1_2IsPR
      with
      (f := fun p : nat => car (cdr (cdr p)))
      (f' := fun p : nat =>
               cPair 1
                 (cPair (cdr (cdr (cdr p)))
                    (car (cdr (cdr p))))); [assumption | |].
    + apply compose1_2IsPR with
    (f := fun p : nat => 1)
    (f' := fun p : nat =>
           cPair (cdr (cdr (cdr p)))
             (car (cdr (cdr p)))).
      * apply const1_NIsPR.
      * apply compose1_2IsPR with
          (f := fun p : nat => cdr (cdr (cdr p)))
          (f' := fun p : nat => car (cdr (cdr p))).
        -- assumption.
        -- assumption.
        -- apply cPairIsPR.
      * apply cPairIsPR.
    + apply cPairIsPR.
  - apply cPairIsPR.
  - apply cPairPi1IsPR.
- apply eqIsPR.
Qed.

Definition checkPrfIMP2 (p recs : nat) :=
  let A := car (cdr (cdr p)) in
  let B := car (cdr (cdr (cdr p))) in
  let C := cdr (cdr (cdr (cdr p))) in
  charFunction 2 Nat.eqb
    (cPair 1
       (cPair (cPair 1 (cPair A (cPair 1 (cPair B C))))
          (cPair 1 (cPair (cPair 1 (cPair A B)) (cPair 1 (cPair A C))))))
    (car p).


Lemma checkPrfIMP2IsPR : isPR 2 checkPrfIMP2.
Proof.
  unfold checkPrfIMP2; apply filter10IsPR with
    (g := fun p : nat =>
            charFunction 2 Nat.eqb
              (cPair 1
                 (cPair
                    (cPair 1
                       (cPair (car (cdr (cdr p)))
                          (cPair 1
                             (cPair
                                (car (cdr (cdr (cdr p))))
                                (cdr (cdr (cdr 
                                                       (cdr p))))))))
                    (cPair 1
                       (cPair
                          (cPair 1
                             (cPair (car (cdr (cdr p)))
                                (car (cdr (cdr (cdr p))))))
                          (cPair 1
                             (cPair (car (cdr (cdr p)))
                                (cdr
                                   (cdr (cdr (cdr p))))))))))
              (car p)).
  assert (H: isPR 1 (fun p : nat => car (cdr (cdr p)))).
  { apply compose1_1IsPR with (f := fun p : nat => cdr (cdr p)).
    apply compose1_1IsPR; apply cPairPi2IsPR.
    apply cPairPi1IsPR.
  } 
  assert (H0: isPR 1 (fun p : nat => 
                        car (cdr (cdr (cdr p))))).
  { apply compose1_1IsPR with
      (f := fun p : nat => cdr (cdr (cdr p))).
    apply compose1_1IsPR with (f := fun p : nat => cdr (cdr p)).
    apply compose1_1IsPR; apply cPairPi2IsPR.
    apply cPairPi2IsPR.
    apply cPairPi1IsPR.
  } 
  assert (H1: isPR 1 (fun p : nat => 
                        cdr (cdr (cdr (cdr p))))).
  { apply compose1_1IsPR with 
      (f := fun p : nat => cdr (cdr (cdr p))).
    apply compose1_1IsPR with (f := fun p : nat => cdr (cdr p)).
    apply compose1_1IsPR; apply cPairPi2IsPR.
    apply cPairPi2IsPR.
    apply cPairPi2IsPR.
  } 
  apply compose1_2IsPR with
    (f := fun p : nat =>
            cPair 1
              (cPair
                 (cPair 1
                    (cPair (car (cdr (cdr p)))
                       (cPair 1
                          (cPair (car (cdr (cdr (cdr p))))
                             (cdr (cdr (cdr (cdr p))))))))
                 (cPair 1
                    (cPair
                       (cPair 1
                          (cPair (car (cdr (cdr p)))
                             (car (cdr (cdr (cdr p))))))
                       (cPair 1
                          (cPair (car (cdr (cdr p)))
                             (cdr (cdr (cdr 
                                                    (cdr p)))))))))).
  replace
    (fun p : nat =>
       cPair 1
         (cPair
            (cPair 1
               (cPair (car (cdr (cdr p)))
                  (cPair 1
                     (cPair (car (cdr (cdr (cdr p))))
                        (cdr (cdr (cdr (cdr p))))))))
            (cPair 1
               (cPair
                  (cPair 1
                     (cPair (car (cdr (cdr p)))
                        (car (cdr (cdr (cdr p))))))
                  (cPair 1
                     (cPair (car (cdr (cdr p)))
                        (cdr (cdr (cdr (cdr p)))))))))) 
    with
    (fun p : nat =>
       codeImp
         (codeImp (car (cdr (cdr p)))
            (codeImp (car (cdr (cdr (cdr p))))
               (cdr (cdr (cdr (cdr p))))))
         (codeImp
            (codeImp (car (cdr (cdr p)))
               (car (cdr (cdr (cdr p)))))
            (codeImp (car (cdr (cdr p)))
               (cdr (cdr (cdr (cdr p)))))));
    [ idtac | reflexivity ].
  - apply
      compose1_2IsPR
      with
      (f := fun p : nat =>
              codeImp (car (cdr (cdr p)))
                (codeImp (car (cdr (cdr (cdr p))))
                   (cdr (cdr (cdr (cdr p))))))
      (f' := fun p : nat =>
               codeImp
                 (codeImp (car (cdr (cdr p)))
                    (car (cdr (cdr (cdr p)))))
                 (codeImp (car (cdr (cdr p)))
                    (cdr (cdr (cdr (cdr p)))))).
    + apply compose1_2IsPR with
        (f := fun p : nat => car (cdr (cdr p)))
        (f' := fun p : nat =>
                 codeImp (car (cdr (cdr (cdr p))))
                   (cdr (cdr (cdr (cdr p))))).
      * assumption.
      * apply
          compose1_2IsPR
          with
          (f := fun p : nat => car (cdr (cdr (cdr p))))
          (f' := fun p : nat => cdr (cdr (cdr (cdr p)))).
        assumption.
        assumption.
        apply codeImpIsPR.
      * apply codeImpIsPR.
    + apply
        compose1_2IsPR
        with
        (f := fun p : nat =>
                codeImp (car (cdr (cdr p)))
                  (car (cdr (cdr (cdr p)))))
        (f' := fun p : nat =>
                 codeImp (car (cdr (cdr p)))
                   (cdr (cdr (cdr (cdr p))))).
      apply
        compose1_2IsPR
        with
        (f := fun p : nat => car (cdr (cdr p)))
        (f' := fun p : nat => car (cdr (cdr (cdr p)))).
      assumption.
      assumption.
      apply codeImpIsPR.
      apply
        compose1_2IsPR
        with
        (f := fun p : nat => car (cdr (cdr p)))
        (f' := fun p : nat => cdr (cdr (cdr (cdr p)))).
      assumption.
      assumption.
      apply codeImpIsPR.
      apply codeImpIsPR.
    + apply codeImpIsPR.
  - apply cPairPi1IsPR.
  - apply eqIsPR.
Qed.

Definition checkPrfCP (p recs : nat) :=
  let A := car (cdr (cdr p)) in
  let B := cdr (cdr (cdr p)) in
  charFunction 2 Nat.eqb
    (cPair 1
       (cPair (cPair 1 (cPair (cPair 2 A) (cPair 2 B))) (cPair 1 (cPair B A))))
    (car p).

Lemma checkPrfCPIsPR : isPR 2 checkPrfCP.
Proof.
  unfold checkPrfCP; apply filter10IsPR with
    (g := fun p : nat =>
            charFunction 2 Nat.eqb
              (cPair 1
                 (cPair
                    (cPair 1
                       (cPair (cPair 2 (car (cdr (cdr p))))
                          (cPair 2 (cdr (cdr (cdr p))))))
                    (cPair 1
                       (cPair (cdr (cdr (cdr p)))
                          (car (cdr (cdr p))))))) 
              (car p)).
  assert (H: isPR 1 (fun p : nat => car (cdr (cdr p)))).
  { apply compose1_1IsPR with (f := fun p : nat => cdr (cdr p)).
    apply compose1_1IsPR; apply cPairPi2IsPR.
    apply cPairPi1IsPR.
  } 
  assert (H0: isPR 1 (fun p : nat => cdr (cdr (cdr p)))).
  { apply compose1_1IsPR with (f := fun p : nat => cdr (cdr p)).
    apply compose1_1IsPR; apply cPairPi2IsPR.
    apply cPairPi2IsPR.
  } 
  apply compose1_2IsPR with
    (f := fun p : nat =>
            cPair 1
              (cPair
                 (cPair 1
                    (cPair (cPair 2 (car (cdr (cdr p))))
                       (cPair 2 (cdr (cdr (cdr p))))))
                 (cPair 1
                    (cPair (cdr (cdr (cdr p)))
                       (car (cdr (cdr p))))))).
  replace
    (fun p : nat =>
       cPair 1
         (cPair
            (cPair 1
               (cPair (cPair 2 (car (cdr (cdr p))))
                  (cPair 2 (cdr (cdr (cdr p))))))
            (cPair 1
               (cPair (cdr (cdr (cdr p)))
                  (car (cdr (cdr p))))))) 
    with
    (fun p : nat =>
       codeImp
         (codeImp (codeNot (car (cdr (cdr p))))
            (codeNot (cdr (cdr (cdr p)))))
         (codeImp (cdr (cdr (cdr p)))
            (car (cdr (cdr p))))); [ idtac | reflexivity ].
  - apply compose1_2IsPR with
      (f := fun p : nat =>
              codeImp (codeNot (car (cdr (cdr p))))
                (codeNot (cdr (cdr (cdr p)))))
      (f' := fun p : nat =>
               codeImp (cdr (cdr (cdr p)))
                 (car (cdr (cdr p)))).
    + apply compose1_2IsPR with
        (f := fun p : nat => codeNot (car (cdr (cdr p))))
        (f' := fun p : nat => codeNot (cdr (cdr (cdr p)))).
      * apply compose1_1IsPR with 
          (f := fun p : nat => car (cdr (cdr p))).
        -- assumption.
        -- apply codeNotIsPR.
      * apply compose1_1IsPR with
          (f := fun p : nat => cdr (cdr (cdr p))).
        -- assumption.
        -- apply codeNotIsPR.
      * apply codeImpIsPR.
    + apply compose1_2IsPR with
        (f := fun p : nat => cdr (cdr (cdr p)))
        (f' := fun p : nat => car (cdr (cdr p))).
      * assumption.
      * assumption.
      * apply codeImpIsPR.
    + apply codeImpIsPR.
- apply cPairPi1IsPR.
- apply eqIsPR.
Qed.

Definition checkPrfFA1 (p recs : nat) :=
  let A := car (cdr (cdr p)) in
  let v := car (cdr (cdr (cdr p))) in
  let t := cdr (cdr (cdr (cdr p))) in
  wellFormedTerm t *
  charFunction 2 Nat.eqb
    (cPair 1 (cPair (cPair 3 (cPair v A)) (codeSubFormula A v t)))
    (car p).

Lemma checkPrfFA1IsPR : isPR 2 checkPrfFA1.
Proof.
  unfold checkPrfFA1; apply filter10IsPR with
    (g := fun p : nat =>
            wellFormedTerm (cdr (cdr (cdr (cdr p)))) *
              charFunction 2 Nat.eqb
                (cPair 1
                   (cPair
                      (cPair 3
                         (cPair (car (cdr (cdr (cdr p))))
                            (car (cdr (cdr p)))))
                      (codeSubFormula (car (cdr (cdr p)))
                         (car (cdr (cdr (cdr p))))
                         (cdr (cdr (cdr (cdr p)))))))
                (car p)).
  assert (H: isPR 1 (fun p : nat => car (cdr (cdr p)))).
  { apply compose1_1IsPR with (f := fun p : nat => cdr (cdr p)).
    apply compose1_1IsPR; apply cPairPi2IsPR.
    apply cPairPi1IsPR.
  }
  assert (H0: isPR 1 
                (fun p : nat => car (cdr (cdr (cdr p))))).
  { apply
      compose1_1IsPR with 
      (f := fun p : nat => cdr (cdr (cdr p))).
    apply compose1_1IsPR with (f := fun p : nat => cdr (cdr p)).
    apply compose1_1IsPR; apply cPairPi2IsPR.
    apply cPairPi2IsPR.
    apply cPairPi1IsPR.
  } 
  assert (H1: isPR 1 (fun p : nat => 
                        cdr (cdr (cdr (cdr p))))).
  { apply compose1_1IsPR with 
      (f := fun p : nat => cdr (cdr (cdr p))).
    apply compose1_1IsPR with (f := fun p : nat => cdr (cdr p)).
    apply compose1_1IsPR; apply cPairPi2IsPR.
    apply cPairPi2IsPR.
    apply cPairPi2IsPR.
  } 
  apply compose1_2IsPR with
    (f := fun p : nat =>
            wellFormedTerm (cdr (cdr (cdr (cdr p)))))
    (f' := fun p : nat =>
             charFunction 2 Nat.eqb
               (cPair 1
                  (cPair
                     (cPair 3
                        (cPair (car (cdr (cdr (cdr p))))
                           (car (cdr (cdr p)))))
                     (codeSubFormula (car (cdr (cdr p)))
                        (car (cdr (cdr (cdr p))))
                        (cdr (cdr (cdr (cdr p)))))))
               (car p)).
  - apply  compose1_1IsPR with 
      (f := fun p : nat => cdr (cdr (cdr (cdr p)))).
    + assumption.
    + unfold wellFormedTerm; apply wellFormedTermIsPR.
      apply codeArityFIsPR.
  - apply compose1_2IsPR with
      (f := fun p : nat =>
              cPair 1
                (cPair
                   (cPair 3
                      (cPair (car (cdr (cdr (cdr p))))
                         (car (cdr (cdr p)))))
                   (codeSubFormula (car (cdr (cdr p)))
                      (car (cdr (cdr (cdr p))))
                      (cdr (cdr (cdr (cdr p))))))).
    replace
      (fun p : nat =>
         cPair 1
           (cPair
              (cPair 3
                 (cPair (car (cdr (cdr (cdr p))))
                    (car (cdr (cdr p)))))
              (codeSubFormula (car (cdr (cdr p)))
                 (car (cdr (cdr (cdr p))))
                 (cdr (cdr (cdr (cdr p))))))) with
      (fun p : nat =>
         codeImp
           (cPair 3
              (cPair (car (cdr (cdr (cdr p))))
                 (car (cdr (cdr p)))))
           (codeSubFormula (car (cdr (cdr p)))
              (car (cdr (cdr (cdr p))))
              (cdr (cdr (cdr (cdr p))))));
      [ idtac | reflexivity ].
    apply compose1_2IsPR with
      (f := fun p : nat =>
              cPair 3
                (cPair (car (cdr (cdr (cdr p))))
                   (car (cdr (cdr p)))))
      (f' := fun p : nat =>
               codeSubFormula (car (cdr (cdr p)))
                 (car (cdr (cdr (cdr p))))
                 (cdr (cdr (cdr (cdr p))))).
    apply
      compose1_2IsPR
      with
      (f := fun p : nat => car (cdr (cdr (cdr p))))
      (f' := fun p : nat => car (cdr (cdr p)))
      (g := fun a b : nat => cPair 3 (cPair a b)).
    assumption.
    assumption.
    apply codeForallIsPR.
    apply compose1_3IsPR with
      (f1 := fun p : nat => car (cdr (cdr p)))
      (f2 := fun p : nat => car (cdr (cdr (cdr p))))
      (f3 := fun p : nat => cdr (cdr (cdr (cdr p))));
      try assumption.
    apply codeSubFormulaIsPR.
    apply codeImpIsPR.
    apply cPairPi1IsPR.
    apply eqIsPR.
  - apply multIsPR.
Qed.

Definition checkPrfFA2 (p recs : nat) :=
  let A := car (cdr (cdr p)) in
  let v := cdr (cdr (cdr p)) in
  (1 - codeIn v (codeFreeVarFormula A)) *
  charFunction 2 Nat.eqb (cPair 1 (cPair A (cPair 3 (cPair v A))))
    (car p).


Lemma checkPrfFA2IsPR : isPR 2 checkPrfFA2.
Proof.
  unfold checkPrfFA2; apply filter10IsPR with
    (g := fun p : nat =>
            (1 -
               codeIn (cdr (cdr (cdr p)))
                 (codeFreeVarFormula (car (cdr (cdr p))))) *
              charFunction 2 Nat.eqb
                (cPair 1
                   (cPair (car (cdr (cdr p)))
                      (cPair 3
                         (cPair (cdr (cdr (cdr p)))
                            (car (cdr (cdr p))))))) 
                (car p)).
  assert (H: isPR 1 (fun p : nat => car (cdr (cdr p)))).
  { apply compose1_1IsPR with (f := fun p : nat => cdr (cdr p)).
    apply compose1_1IsPR; apply cPairPi2IsPR.
    apply cPairPi1IsPR.
  } 
  assert (H0: isPR 1 (fun p : nat => cdr (cdr (cdr p)))).
  { apply compose1_1IsPR with (f := fun p : nat => cdr (cdr p)).
    apply compose1_1IsPR; apply cPairPi2IsPR.
    apply cPairPi2IsPR.
  } 
  apply compose1_2IsPR with
    (f := fun p : nat =>
            1 -
              codeIn (cdr (cdr (cdr p)))
                (codeFreeVarFormula (car (cdr (cdr p)))))
    (f' := fun p : nat =>
             charFunction 2 Nat.eqb
               (cPair 1
                  (cPair (car (cdr (cdr p)))
                     (cPair 3
                        (cPair (cdr (cdr (cdr p)))
                           (car (cdr (cdr p))))))) 
               (car p)).
  - apply compose1_2IsPR with
      (f := fun p : nat => 1)
      (f' := fun p : nat =>
               codeIn (cdr (cdr (cdr p)))
                 (codeFreeVarFormula (car (cdr (cdr p))))).
    + apply const1_NIsPR.
    + apply compose1_2IsPR with
        (f := fun p : nat => cdr (cdr (cdr p)))
        (f' := fun p : nat =>
                 codeFreeVarFormula (car (cdr (cdr p)))).
      * assumption.
      * apply compose1_1IsPR with
          (f := fun p : nat => car (cdr (cdr p))).
        -- assumption.
        -- apply codeFreeVarFormulaIsPR.
      * apply codeInIsPR.
    + apply minusIsPR.
  - apply compose1_2IsPR with
      (f := fun p : nat =>
              cPair 1
                (cPair (car (cdr (cdr p)))
                   (cPair 3
                      (cPair (cdr (cdr (cdr p)))
                         (car (cdr (cdr p))))))).
    + replace
        (fun p : nat =>
           cPair 1
             (cPair (car (cdr (cdr p)))
                (cPair 3
                   (cPair (cdr (cdr (cdr p)))
                      (car (cdr (cdr p))))))) 
        with
        (fun p : nat =>
           codeImp (car (cdr (cdr p)))
             (cPair 3
                (cPair (cdr (cdr (cdr p)))
                   (car (cdr (cdr p)))))); 
        [ idtac | reflexivity ].
      apply compose1_2IsPR with
        (f := fun p : nat => car (cdr (cdr p)))
        (f' := fun p : nat =>
                 cPair 3
                   (cPair (cdr (cdr (cdr p)))
                      (car (cdr (cdr p))))).
      * assumption.
      * apply compose1_2IsPR with
          (f := fun p : nat => cdr (cdr (cdr p)))
          (f' := fun p : nat => car (cdr (cdr p)))
          (g := fun a b : nat => cPair 3 (cPair a b)).
        -- assumption.
        -- assumption.
        -- apply codeForallIsPR.
      * apply codeImpIsPR.
    + apply cPairPi1IsPR.
    + apply eqIsPR.
  - apply multIsPR.
Qed.

Definition checkPrfFA3 (p recs : nat) :=
  let A := car (cdr (cdr p)) in
  let B := car (cdr (cdr (cdr p))) in
  let v := cdr (cdr (cdr (cdr p))) in
  charFunction 2 Nat.eqb
    (cPair 1
       (cPair (cPair 3 (cPair v (cPair 1 (cPair A B))))
          (cPair 1 (cPair (cPair 3 (cPair v A)) (cPair 3 (cPair v B))))))
    (car p).

Lemma checkPrfFA3IsPR : isPR 2 checkPrfFA3.
Proof.
  unfold checkPrfFA3; apply filter10IsPR with
    (g := fun p : nat =>
            charFunction 2 Nat.eqb
              (cPair 1
                 (cPair
                    (cPair 3
                       (cPair (cdr (cdr (cdr (cdr p))))
                          (cPair 1
                             (cPair (car (cdr (cdr p)))
                                (car (cdr 
                                        (cdr (cdr p))))))))
                    (cPair 1
                       (cPair
                          (cPair 3
                             (cPair
                                (cdr (cdr (cdr (cdr p))))
                                (car (cdr (cdr p)))))
                          (cPair 3
                             (cPair
                                (cdr (cdr (cdr (cdr p))))
                                (car (cdr (cdr 
                                             (cdr p))))))))))
              (car p)).
  assert (H: isPR 1 (fun p : nat => car (cdr (cdr p)))).
  { 
    apply compose1_1IsPR with (f := fun p : nat => cdr (cdr p)).
    apply compose1_1IsPR; apply cPairPi2IsPR.
    apply cPairPi1IsPR.
  } 
  assert (H0: isPR 1 (fun p : nat => 
                        car (cdr (cdr (cdr p))))).
  { 
    apply compose1_1IsPR with 
      (f := fun p : nat => cdr (cdr (cdr p))).
    apply compose1_1IsPR with (f := fun p : nat => cdr (cdr p)).
    apply compose1_1IsPR; apply cPairPi2IsPR.
    apply cPairPi2IsPR.
    apply cPairPi1IsPR.
  } 
  assert (H1: isPR 1 (fun p : nat => 
                       cdr (cdr (cdr (cdr p))))).
  { 
    apply compose1_1IsPR with 
      (f := fun p : nat => cdr (cdr (cdr p))).
    apply compose1_1IsPR with (f := fun p : nat => cdr (cdr p)).
    apply compose1_1IsPR; apply cPairPi2IsPR.
    apply cPairPi2IsPR.
    apply cPairPi2IsPR.
  } 
  apply compose1_2IsPR with
    (f := fun p : nat =>
          cPair 1
            (cPair
               (cPair 3
                  (cPair (cdr (cdr (cdr (cdr p))))
                     (cPair 1
                        (cPair (car (cdr (cdr p)))
                           (car (cdr (cdr (cdr p))))))))
               (cPair 1
                  (cPair
                     (cPair 3
                        (cPair (cdr (cdr (cdr (cdr p))))
                           (car (cdr (cdr p)))))
                     (cPair 3
                        (cPair (cdr (cdr (cdr (cdr p))))
                           (car (cdr (cdr (cdr p)))))))))).
  - replace
      (fun p : nat =>
         cPair 1
           (cPair
              (cPair 3
                 (cPair (cdr (cdr (cdr (cdr p))))
                    (cPair 1
                       (cPair (car (cdr (cdr p)))
                          (car (cdr (cdr (cdr p))))))))
              (cPair 1
                 (cPair
                    (cPair 3
                       (cPair (cdr (cdr (cdr (cdr p))))
                          (car (cdr (cdr p)))))
                    (cPair 3
                       (cPair (cdr (cdr (cdr (cdr p))))
                          (car (cdr (cdr (cdr p)))))))))) 
      with
      (fun p : nat =>
         codeImp
           (cPair 3
              (cPair (cdr (cdr (cdr (cdr p))))
                 (codeImp (car (cdr (cdr p)))
                    (car (cdr (cdr (cdr p)))))))
           (codeImp
              (cPair 3
                 (cPair (cdr (cdr (cdr (cdr p))))
                    (car (cdr (cdr p)))))
              (cPair 3
                 (cPair (cdr (cdr (cdr (cdr p))))
                    (car (cdr (cdr (cdr p))))))));
      [ idtac | reflexivity ].
    apply compose1_2IsPR with
      (f := fun p : nat =>
              cPair 3
                (cPair (cdr (cdr (cdr (cdr p))))
                   (codeImp (car (cdr (cdr p)))
                      (car (cdr (cdr (cdr p)))))))
      (f' := fun p : nat =>
               codeImp
                 (cPair 3
                    (cPair (cdr (cdr (cdr (cdr p))))
                       (car (cdr (cdr p)))))
                 (cPair 3
                    (cPair (cdr (cdr (cdr (cdr p))))
                       (car (cdr (cdr (cdr p))))))).
    + apply compose1_2IsPR with
        (f := fun p : nat => cdr (cdr (cdr (cdr p))))
        (f' := fun p : nat =>
                 codeImp (car (cdr (cdr p)))
                   (car (cdr (cdr (cdr p)))))
        (g := fun a b : nat => cPair 3 (cPair a b)).
      * assumption.
      * apply  compose1_2IsPR with
          (f := fun p : nat => car (cdr (cdr p)))
          (f' := fun p : nat => car (cdr (cdr (cdr p)))).
        -- assumption.
        -- assumption.
        -- apply codeImpIsPR.
      * apply codeForallIsPR.
    + apply compose1_2IsPR with
        (f := fun p : nat =>
                cPair 3
                  (cPair (cdr (cdr (cdr (cdr p))))
                     (car (cdr (cdr p)))))
        (f' := fun p : nat =>
                 cPair 3
                   (cPair (cdr (cdr (cdr (cdr p))))
                      (car (cdr (cdr (cdr p)))))).
      * apply compose1_2IsPR with
          (f := fun p : nat => cdr (cdr (cdr (cdr p))))
          (f' := fun p : nat => car (cdr (cdr p)))
          (g := fun a b : nat => cPair 3 (cPair a b)).
        -- assumption.
        -- assumption.
        -- apply codeForallIsPR.
      * apply compose1_2IsPR with
          (f := fun p : nat => cdr (cdr (cdr (cdr p))))
          (f' := fun p : nat => car (cdr (cdr (cdr p))))
          (g := fun a b : nat => cPair 3 (cPair a b)).
        -- assumption.
        -- assumption.
        -- apply codeForallIsPR.
      * apply codeImpIsPR.
    + apply codeImpIsPR.
  - apply cPairPi1IsPR.
- apply eqIsPR.
Qed.

Definition checkPrfEQ1 (p recs : nat) :=
  charFunction 2 Nat.eqb (cdr (cdr p)) 0 *
  charFunction 2 Nat.eqb
    (codeFormula L codeF codeR (equal (var 0) (var 0)))
    (car p).

Lemma checkPrfEQnIsPR (n: nat):
  isPR 2
    (fun p recs : nat =>
       charFunction 2 Nat.eqb (cdr (cdr p)) 0 *
         charFunction 2 Nat.eqb n (car p)).
Proof.
  unfold checkPrfEQ1; apply filter10IsPR with
    (g := fun p : nat =>
            charFunction 2 Nat.eqb (cdr (cdr p)) 0 *
              charFunction 2 Nat.eqb n (car p)).
  apply compose1_2IsPR with
    (f := fun p : nat => charFunction 2 Nat.eqb (cdr (cdr p)) 0)
    (f' := fun p : nat => charFunction 2 Nat.eqb n (car p)).
  - apply compose1_2IsPR with 
      (f := fun p : nat => cdr (cdr p)) 
      (f' := fun p : nat => 0).
    + apply compose1_1IsPR; apply cPairPi2IsPR. 
    + apply const1_NIsPR.
    + apply eqIsPR.
  - apply compose1_2IsPR with (f := fun p : nat => n).
    + apply const1_NIsPR.
    + apply cPairPi1IsPR.
    + apply eqIsPR.
  - apply multIsPR.
Qed.

Lemma checkPrfEQ1IsPR : isPR 2 checkPrfEQ1.
Proof.
  unfold checkPrfEQ1; apply checkPrfEQnIsPR.
Qed.

Definition checkPrfEQ2 (p recs : nat) :=
  charFunction 2 Nat.eqb (cdr (cdr p)) 0 *
    charFunction 2 Nat.eqb
      (codeFormula L codeF codeR
         (impH (equal (var 0) (var 1))
            (equal (var 1) (var 0)))) 
      (car p).

Lemma checkPrfEQ2IsPR : isPR 2 checkPrfEQ2.
Proof.
  unfold checkPrfEQ2; apply checkPrfEQnIsPR.
Qed.

Definition checkPrfEQ3 (p recs : nat) :=
  charFunction 2 Nat.eqb (cdr (cdr p)) 0 *
    charFunction 2 Nat.eqb
      (codeFormula L codeF codeR
         (impH (equal (var 0) (var 1))
            (impH (equal (var 1) (var 2))
               (equal (var 0) (var 2))))) 
      (car p).

Lemma checkPrfEQ3IsPR : isPR 2 checkPrfEQ3.
Proof.
  unfold checkPrfEQ3; apply checkPrfEQnIsPR.
Qed.

Definition codeAxmEqHelp (n f : nat) : nat :=
  nat_rec (fun _ => nat) f
    (fun m rec : nat =>
       cPair 1
         (cPair (cPair 0 (cPair (cPair 0 (m + m)) (cPair 0 (S (m + m))))) rec))
    n.

Lemma codeAxmEqHelpIsPR : isPR 2 codeAxmEqHelp.
Proof.
  unfold codeAxmEqHelp; apply  ind1ParamIsPR with
    (g := fun f : nat => f)
    (f := fun m rec f : nat =>
            cPair 1
              (cPair (cPair 0 (cPair (cPair 0 (m + m)) (cPair 0 (S (m + m)))))
                 rec)).
  - apply filter110IsPR with
      (g := fun m rec : nat =>
              codeImp (cPair 0 (cPair (cPair 0 (m + m)) (cPair 0 (S (m + m)))))
                rec).
    apply compose2_2IsPR with
      (f := fun m rec : nat =>
              cPair 0 (cPair (cPair 0 (m + m)) (cPair 0 (S (m + m)))))
      (g := fun m rec : nat => rec).
    + apply filter10IsPR with
        (g := fun m : nat =>
                cPair 0 (cPair (cPair 0 (m + m)) (cPair 0 (S (m + m))))).
      assert
        (H: forall g : nat -> nat, isPR 1 g -> 
                                   isPR 1 (fun a : nat => cPair 0 (g a))).
      { intros g H; apply compose1_2IsPR with (f := fun a : nat => 0).
        - apply const1_NIsPR.
        - assumption.
        - apply cPairIsPR.
      } 
      apply H with 
        (g := fun m : nat => cPair (cPair 0 (m + m)) (cPair 0 (S (m + m)))).
      apply compose1_2IsPR with
        (f := fun m : nat => cPair 0 (m + m))
        (f' := fun m : nat => cPair 0 (S (m + m))).
      * apply H with (g := fun m : nat => m + m).
        apply compose1_2IsPR with 
          (f := fun m : nat => m) (f' := fun m : nat => m).
        -- apply idIsPR.
        -- apply idIsPR.
        -- apply plusIsPR.
      * apply H with (g := fun m : nat => S (m + m)).
        apply compose1_1IsPR with (f := fun m : nat => m + m).
        -- apply compose1_2IsPR with 
             (f := fun m : nat => m) (f' := fun m : nat => m).
           ++ apply idIsPR.
           ++ apply idIsPR.
           ++ apply plusIsPR.
        -- apply succIsPR.
      * apply cPairIsPR.
    + apply pi2_2IsPR.
    + apply codeImpIsPR.
  - apply idIsPR.
Qed.

Definition codeNVars1 (n : nat) : nat :=
  nat_rec (fun _ => nat) 0
    (fun m rec : nat => S (cPair (cPair 0 (m + m)) rec)) n.

Lemma codeNVars1IsPR : isPR 1 codeNVars1.
Proof.
  unfold codeNVars1; apply indIsPR with
    (f := fun m rec : nat => S (cPair (cPair 0 (m + m)) rec)).
  apply compose2_1IsPR with 
    (f := fun m rec : nat => cPair (cPair 0 (m + m)) rec).
  - apply compose2_2IsPR with
      (f := fun m rec : nat => cPair 0 (m + m))
      (g := fun m rec : nat => rec).
    + apply filter10IsPR with (g := fun m : nat => cPair 0 (m + m)).
      apply compose1_2IsPR with 
        (f := fun m : nat => 0) (f' := fun m : nat => m + m).
      * apply const1_NIsPR.
      * apply compose1_2IsPR with 
          (f := fun m : nat => m) (f' := fun m : nat => m).
        -- apply idIsPR.
        -- apply idIsPR.
        -- apply plusIsPR.
      * apply cPairIsPR.
    + apply pi2_2IsPR.
    + apply cPairIsPR.
  - apply succIsPR.
Qed.

Definition codeNVars2 (n : nat) : nat :=
  nat_rec (fun _ => nat) 0
    (fun m rec : nat => S (cPair (cPair 0 (S (m + m))) rec)) n.

Lemma codeNVars2IsPR : isPR 1 codeNVars2.
Proof.
  unfold codeNVars2; apply indIsPR with
    (f := fun m rec : nat => S (cPair (cPair 0 (S (m + m))) rec)).
  apply compose2_1IsPR with 
    (f := fun m rec : nat => cPair (cPair 0 (S (m + m))) rec).
  - apply compose2_2IsPR with
      (f := fun m rec : nat => cPair 0 (S (m + m)))
      (g := fun m rec : nat => rec).
    + apply filter10IsPR with (g := fun m : nat => cPair 0 (S (m + m))).
      apply compose1_2IsPR with
        (f := fun m : nat => 0) (f' := fun m : nat => S (m + m)).
      * apply const1_NIsPR.
      * apply compose1_1IsPR with (f := fun m : nat => m + m).
      -- apply compose1_2IsPR with 
          (f := fun m : nat => m) (f' := fun m : nat => m).
         ++ apply idIsPR.
         ++ apply idIsPR.
         ++ apply plusIsPR.
      -- apply succIsPR.
      * apply cPairIsPR.
    + apply pi2_2IsPR.
    + apply cPairIsPR.
  - apply succIsPR.
Qed.

Lemma codeNVarsCorrect (n: nat) :
 codeNVars1 n = codeTerms L codeF n (fst (nVars L n)) /\
 codeNVars2 n = codeTerms L codeF n (snd (nVars L n)).
Proof.
  split.
  - induction n as [| n Hrecn].
    + cbn; reflexivity.
    + simpl; rewrite Hrecn.
      destruct (nVars L n); simpl; reflexivity.
  - induction n as [| n Hrecn].
    + simpl; reflexivity.
    + simpl; rewrite Hrecn.
      destruct (nVars L n); simpl; reflexivity.
Qed.

Definition checkPrfEQ4 (p recs : nat) :=
  let r := cdr (cdr p) in
  let A := cPair (S (S (S (S r)))) (codeNVars1 (pred (codeArityR r))) in
  let B := cPair (S (S (S (S r)))) (codeNVars2 (pred (codeArityR r))) in
  notZero (codeArityR r) *
    charFunction 2 Nat.eqb (codeAxmEqHelp (pred (codeArityR r)) (codeIff A B))
      (car p).

Lemma codeOrIsPR : isPR 2 codeOr.
Proof.
  unfold codeOr; apply compose2_2IsPR with 
    (f := fun a b : nat => codeNot a) (g := fun a b : nat => b).
  - apply filter10IsPR, codeNotIsPR.
  - apply pi2_2IsPR. 
  - apply codeImpIsPR.
Qed.

Lemma codeAndIsPR : isPR 2 codeAnd.
Proof.
  unfold codeAnd; apply compose2_1IsPR with 
    (f := fun a b : nat => codeOr (codeNot a) (codeNot b)).
  - apply compose2_2IsPR with 
      (f := fun a b : nat => codeNot a) (g := fun a b : nat => codeNot b).
    + apply filter10IsPR.
      apply codeNotIsPR.
    + apply filter01IsPR.
      apply codeNotIsPR.
    + apply codeOrIsPR.
  - apply codeNotIsPR.
Qed.

Lemma codeIffIsPR : isPR 2 codeIff.
Proof.
  unfold codeIff; apply compose2_2IsPR with (g := fun a b : nat => codeImp b a).
  - apply codeImpIsPR.
  - apply swapIsPR; apply codeImpIsPR.
  - apply codeAndIsPR.
Qed.

Lemma checkPrfEQ4IsPR : isPR 2 checkPrfEQ4.
Proof.
  unfold checkPrfEQ4; apply filter10IsPR with
    (g := fun p : nat =>
            notZero (codeArityR (cdr (cdr p))) *
              charFunction 2 Nat.eqb
                (codeAxmEqHelp (pred (codeArityR (cdr (cdr p))))
                   (codeIff
                      (cPair (S (S (S (S (cdr (cdr p))))))
                         (codeNVars1 
                            (pred (codeArityR (cdr (cdr p))))))
                      (cPair (S (S (S (S (cdr (cdr p))))))
                         (codeNVars2 (pred (codeArityR 
                                              (cdr (cdr p))))))))
                (car p)).
  assert (H: isPR 1 (fun p : nat => cdr (cdr p)))
  by (apply compose1_1IsPR; apply cPairPi2IsPR).
  apply compose1_2IsPR with
    (f := fun p : nat => notZero (codeArityR (cdr (cdr p))))
    (f' := fun p : nat =>
             charFunction 2 Nat.eqb
               (codeAxmEqHelp (pred (codeArityR (cdr (cdr p))))
                  (codeIff
                     (cPair (S (S (S (S (cdr (cdr p))))))
                        (codeNVars1 (pred (codeArityR (cdr (cdr p))))))
                     (cPair (S (S (S (S (cdr (cdr p))))))
                        (codeNVars2 (pred (codeArityR 
                                             (cdr (cdr p))))))))
               (car p)).
  - apply compose1_1IsPR with
      (f := fun p : nat => codeArityR (cdr (cdr p))).
    + apply compose1_1IsPR with (f := fun p : nat => cdr (cdr p)). 
      * assumption.
      * apply codeArityRIsPR.
    + apply notZeroIsPR.
  - apply compose1_2IsPR with
      (f := fun p : nat =>
              codeAxmEqHelp (pred (codeArityR (cdr (cdr p))))
                (codeIff
                   (cPair (S (S (S (S (cdr (cdr p))))))
                      (codeNVars1 (pred (codeArityR (cdr (cdr p))))))
                   (cPair (S (S (S (S (cdr (cdr p))))))
                      (codeNVars2 
                         (pred (codeArityR (cdr (cdr p)))))))).
    + apply compose1_2IsPR with
        (f := fun p : nat => pred (codeArityR (cdr (cdr p))))
        (f' := fun p : nat =>
                 codeIff
                   (cPair (S (S (S (S (cdr (cdr p))))))
                      (codeNVars1 (pred (codeArityR (cdr (cdr p))))))
                   (cPair (S (S (S (S (cdr (cdr p))))))
                      (codeNVars2 (pred (codeArityR (cdr (cdr p))))))).
      * apply compose1_1IsPR with
          (f := fun p : nat => codeArityR (cdr (cdr p))).
        -- apply compose1_1IsPR with (f := fun p : nat => cdr (cdr p)).
           assumption.
           apply codeArityRIsPR.
        -- apply predIsPR.
      * apply compose1_2IsPR with
          (f := fun p : nat =>
                  cPair (S (S (S (S (cdr (cdr p))))))
                    (codeNVars1 (pred (codeArityR (cdr (cdr p))))))
          (f' := fun p : nat =>
                   cPair (S (S (S (S (cdr (cdr p))))))
                     (codeNVars2 (pred (codeArityR (cdr (cdr p)))))).
        -- apply compose1_2IsPR with
             (f := fun p : nat => S (S (S (S (cdr (cdr p))))))
             (f' := fun p : nat =>
                      codeNVars1 (pred (codeArityR (cdr (cdr p))))).
           ++ apply compose1_1IsPR with 
                (f := fun p : nat => cdr (cdr p)) (g := iterate S 4).
           ** assumption.
           ** apply iterateIsPR.
              apply succIsPR.
           ++ apply compose1_1IsPR with 
                (f := fun p : nat => pred (codeArityR (cdr (cdr p)))).
              ** apply compose1_1IsPR with
                   (f := fun p : nat => codeArityR (cdr (cdr p))).
                 apply compose1_1IsPR with
                   (f := fun p : nat => cdr (cdr p)).
                 assumption.
                 apply codeArityRIsPR.
                 apply predIsPR.
              ** apply codeNVars1IsPR.
           ++ apply cPairIsPR.
        -- apply compose1_2IsPR with
             (f := fun p : nat => S (S (S (S (cdr (cdr p))))))
             (f' := fun p : nat =>
                      codeNVars2 (pred (codeArityR (cdr (cdr p))))).
           ++ apply compose1_1IsPR with 
                (f := fun p : nat => cdr (cdr p)) (g := iterate S 4).
              ** assumption.
              ** apply iterateIsPR.
                 apply succIsPR.
           ++ apply compose1_1IsPR with
                (f := fun p : nat => 
                        pred (codeArityR (cdr (cdr p)))).
              ** apply compose1_1IsPR with 
                   (f := fun p : nat => codeArityR (cdr (cdr p))).
                 apply compose1_1IsPR with
                   (f := fun p : nat => cdr (cdr p)).
                 assumption.
                 apply codeArityRIsPR.
                 apply predIsPR.
              ** apply codeNVars2IsPR.
           ++ apply cPairIsPR.
        -- apply codeIffIsPR.
      * apply codeAxmEqHelpIsPR.
    + apply cPairPi1IsPR.
    + apply eqIsPR.
  - apply multIsPR.
Qed.

Definition checkPrfEQ5 (p recs : nat) :=
  let f := cdr (cdr p) in
  notZero (codeArityF f) *
    charFunction 2 Nat.eqb
      (codeAxmEqHelp (pred (codeArityF f))
         (cPair 0
            (cPair (cPair (S f) (codeNVars1 (pred (codeArityF f))))
               (cPair (S f) (codeNVars2 (pred (codeArityF f))))))) 
      (car p).

Lemma checkPrfEQ5IsPR : isPR 2 checkPrfEQ5.
Proof.
  unfold checkPrfEQ5; apply filter10IsPR with
    (g := fun p : nat =>
            notZero (codeArityF (cdr (cdr p))) *
              charFunction 2 Nat.eqb
                (codeAxmEqHelp (pred (codeArityF (cdr (cdr p))))
                   (cPair 0
                      (cPair
                         (cPair (S (cdr (cdr p)))
                            (codeNVars1
                               (pred (codeArityF (cdr (cdr p))))))
                         (cPair (S (cdr (cdr p)))
                            (codeNVars2
                               (pred (codeArityF (cdr 
                                                    (cdr p)))))))))
                (car p)).
  assert (H: isPR 1 (fun p : nat => cdr (cdr p))) by
  (apply compose1_1IsPR; apply cPairPi2IsPR).
  apply compose1_2IsPR with
    (f := fun p : nat => notZero (codeArityF (cdr (cdr p))))
    (f' := fun p : nat =>
           charFunction 2 Nat.eqb
             (codeAxmEqHelp (pred (codeArityF (cdr (cdr p))))
                (cPair 0
                   (cPair
                      (cPair (S (cdr (cdr p)))
                         (codeNVars1
                            (pred (codeArityF (cdr (cdr p))))))
                      (cPair (S (cdr (cdr p)))
                         (codeNVars2
                            (pred (codeArityF (cdr (cdr p)))))))))
             (car p)).
  - apply compose1_1IsPR with
      (f := fun p : nat => codeArityF (cdr (cdr p))).
    + apply compose1_1IsPR with 
        (f := fun p : nat => cdr (cdr p)).
      * assumption.
      * apply codeArityFIsPR.
    + apply notZeroIsPR.
  - apply compose1_2IsPR with
      (f := fun p : nat =>
              codeAxmEqHelp (pred (codeArityF (cdr (cdr p))))
                (cPair 0
                   (cPair
                      (cPair (S (cdr (cdr p)))
                         (codeNVars1 
                            (pred 
                               (codeArityF (cdr (cdr p))))))
                      (cPair (S (cdr (cdr p)))
                         (codeNVars2 (pred 
                                        (codeArityF 
                                           (cdr (cdr p))))))))).
    + apply compose1_2IsPR with
      (f := fun p : nat => pred (codeArityF (cdr (cdr p))))
      (f' := fun p : nat =>
               cPair 0
                 (cPair
                    (cPair (S (cdr (cdr p)))
                       (codeNVars1 
                          (pred 
                             (codeArityF (cdr (cdr p))))))
                    (cPair (S (cdr (cdr p)))
                       (codeNVars2 (pred 
                                      (codeArityF 
                                         (cdr (cdr p)))))))).
      * apply compose1_1IsPR with 
          (f := fun p : nat => codeArityF (cdr (cdr p))).
        -- apply compose1_1IsPR with 
             (f := fun p : nat => cdr (cdr p)).
           ++ assumption.
           ++ apply codeArityFIsPR.
        -- apply predIsPR.
      * apply compose1_2IsPR with
          (f := fun p : nat =>
                  cPair (S (cdr (cdr p)))
                    (codeNVars1 (pred 
                                   (codeArityF (cdr (cdr p))))))
          (f' := fun p : nat =>
                   cPair (S (cdr (cdr p)))
                     (codeNVars2 (pred (codeArityF
                                          (cdr (cdr p))))))
          (g := fun a b : nat => cPair 0 (cPair a b)).
        -- apply compose1_2IsPR with
             (f := fun p : nat => S (cdr (cdr p)))
             (f' := fun p : nat =>
                      codeNVars1 
                        (pred (codeArityF (cdr (cdr p))))).
           ++ apply compose1_1IsPR with 
                (f := fun p : nat => cdr (cdr p)).
              ** assumption.
              ** apply succIsPR.
           ++ apply compose1_1IsPR with 
                (f := fun p : nat => 
                        pred (codeArityF (cdr (cdr p)))).
              ** apply compose1_1IsPR with 
                   (f := fun p : nat => codeArityF (cdr (cdr p))).
                 apply compose1_1IsPR with 
                   (f := fun p : nat => cdr (cdr p)).
                 assumption.
                 apply codeArityFIsPR.
                 apply predIsPR.
              ** apply codeNVars1IsPR.
           ++ apply cPairIsPR.
        -- apply compose1_2IsPR with
             (f := fun p : nat => S (cdr (cdr p)))
             (f' := fun p : nat =>
                      codeNVars2 (pred (codeArityF 
                                          (cdr (cdr p))))).
           ++ apply compose1_1IsPR with 
                (f := fun p : nat => cdr (cdr p)).
              ** assumption.
              ** apply succIsPR.
           ++ apply compose1_1IsPR with
                (f := fun p : nat => 
                        pred (codeArityF (cdr (cdr p)))).
              ** apply compose1_1IsPR with 
                   (f := fun p : nat => 
                           codeArityF (cdr (cdr p))).
                 apply compose1_1IsPR with 
                   (f := fun p : nat => cdr (cdr p)).
                 assumption.
                 apply codeArityFIsPR.
                 apply predIsPR.
              ** apply codeNVars2IsPR.
           ++ apply cPairIsPR.
        -- apply compose2_2IsPR with (f := fun a b : nat => 0).
           ++ apply filter10IsPR with (g := fun _ : nat => 0).
              apply const1_NIsPR.
           ++ apply cPairIsPR.
           ++ apply cPairIsPR.
      * apply codeAxmEqHelpIsPR.
    + apply cPairPi1IsPR.
    + apply eqIsPR.
- apply multIsPR.
Qed.

Definition checkPrfHelp : nat -> nat :=
  evalStrongRec 0
    (fun p recs : nat =>
     let type := car (cdr p) in
     switchPR type
       (switchPR (pred type)
          (switchPR (pred (pred type))
             (switchPR (pred (pred (pred type)))
                (switchPR (pred (pred (pred (pred type))))
                   (switchPR (pred (pred (pred (pred (pred type)))))
                      (switchPR
                         (pred (pred (pred (pred (pred (pred type))))))
                         (switchPR
                            (pred
                               (pred (pred (pred (pred (pred (pred type)))))))
                            (switchPR
                               (pred
                                  (pred
                                     (pred
                                        (pred
                                           (pred (pred (pred (pred type))))))))
                               (switchPR
                                  (pred
                                     (pred
                                        (pred
                                           (pred
                                              (pred
                                                 (pred
                                                  (pred (pred (pred type)))))))))
                                  (switchPR
                                     (pred
                                        (pred
                                           (pred
                                              (pred
                                                 (pred
                                                  (pred
                                                  (pred
                                                  (pred 
                                                     (pred (pred type))))))))))
                                     (switchPR
                                        (pred
                                           (pred
                                              (pred
                                                 (pred
                                                  (pred
                                                  (pred
                                                  (pred
                                                  (pred
                                                  (pred 
                                                     (pred (pred type)))))))))))
                                        (switchPR
                                           (pred
                                              (pred
                                                 (pred
                                                  (pred
                                                  (pred
                                                  (pred
                                                  (pred
                                                  (pred
                                                  (pred
                                                  (pred (pred (pred type))))))))))))
                                           (switchPR
                                              (pred
                                                 (pred
                                                  (pred
                                                  (pred
                                                  (pred
                                                  (pred
                                                  (pred
                                                  (pred
                                                  (pred
                                                  (pred
                                                  (pred (pred (pred type)))))))))))))
                                              0 (checkPrfEQ5 p recs))
                                           (checkPrfEQ4 p recs))
                                        (checkPrfEQ3 p recs))
                                     (checkPrfEQ2 p recs))
                                  (checkPrfEQ1 p recs)) 
                               (checkPrfFA3 p recs)) 
                            (checkPrfFA2 p recs)) (checkPrfFA1 p recs))
                      (checkPrfCP p recs)) (checkPrfIMP2 p recs))
                (checkPrfIMP1 p recs)) (checkPrfGEN p recs))
          (checkPrfMP p recs)) (checkPrfAXM p recs)).

Lemma checkPrfHelpIsPR : isPR 1 checkPrfHelp.
Proof.
  set
    (f :=
       list_rec (fun _ => nat -> nat -> nat -> nat) (fun _ _ _ : nat => 0)
         (fun (a : nat -> nat -> nat) (l : list (nat -> nat -> nat))
              (rec : nat -> nat -> nat -> nat) (n p recs : nat) =>
            switchPR (iterate pred n (car (cdr p))) 
              (rec (S n) p recs) (a p recs))) in *.
  set
    (l :=
       checkPrfAXM
         :: checkPrfMP
         :: checkPrfGEN
         :: checkPrfIMP1
         :: checkPrfIMP2
         :: checkPrfCP
         :: checkPrfFA1
         :: checkPrfFA2
         :: checkPrfFA3
         :: checkPrfEQ1
         :: checkPrfEQ2
         :: checkPrfEQ3
         :: checkPrfEQ4 :: checkPrfEQ5 :: nil) 
    in *.
  assert
    (H: forall (l : list (nat -> nat -> nat)) (n : nat),
        list_rect (fun _ => Set) unit
          (fun (a : nat -> nat -> nat) _ (rec : Set) => 
             (isPR 2 a * rec)%type) l ->
        isPR 2 (f l n)). 
  { intro l0; induction l0 as [| a l0 Hrecl0].
    - simpl in |- *.
      intros n H; apply filter10IsPR with (g := fun _ : nat => 0).
      apply const1_NIsPR.
    - simpl; intros n H.
      apply compose2_3IsPR with 
        (f1 := fun p recs : nat => iterate pred n (car (cdr p))).
      + apply filter10IsPR with
          (g := fun p : nat => iterate pred n (car (cdr p))).
        apply compose1_1IsPR with (f := fun p : nat => car (cdr p)).
        * apply compose1_1IsPR.
          -- apply cPairPi2IsPR.
          -- apply cPairPi1IsPR.
        * apply iterateIsPR.
          apply predIsPR.
      + apply Hrecl0.
        eapply snd.
        apply H.
      + eapply fst.
        apply H.
      + apply switchIsPR.
  } 
  assert (H0: isPR 2 (f l 0)).
  { apply H.
    simpl; repeat split.
    - apply checkPrfAXMIsPR.
    - apply checkPrfMPIsPR.
    - apply checkPrfGENIsPR.
    - apply checkPrfIMP1IsPR.
    - apply checkPrfIMP2IsPR.
    - apply checkPrfCPIsPR.
    - apply checkPrfFA1IsPR.
    - apply checkPrfFA2IsPR.
    - apply checkPrfFA3IsPR.
    - apply checkPrfEQ1IsPR.
    - apply checkPrfEQ2IsPR.
    - apply checkPrfEQ3IsPR.
    - apply checkPrfEQ4IsPR.
    - apply checkPrfEQ5IsPR.
  } 
  unfold checkPrfHelp; apply evalStrongRecIsPR, H0. 
Qed.

Definition checkPrf (f p : nat) : nat :=
  switchPR (wellFormedFormula f) (checkPrfHelp (cPair f p)) 0.

(* begin snippet checkPrfIsPR:: no-out *)
Lemma checkPrfIsPR : isPR 2 checkPrf.
(* end snippet checkPrfIsPR *)
Proof.
  unfold checkPrf; apply compose2_3IsPR with
    (f1 := fun f p : nat => wellFormedFormula f)
    (f2 := fun f p : nat => checkPrfHelp (cPair f p))
    (f3 := fun f p : nat => 0).
  - apply filter10IsPR.
    unfold wellFormedFormula; apply wellFormedFormulaIsPR.
    + apply codeArityFIsPR.
    + apply codeArityRIsPR.
  - apply compose2_1IsPR.
    + apply cPairIsPR.
    + apply checkPrfHelpIsPR.
  - apply filter10IsPR with (g := fun _ : nat => 0).
    apply const1_NIsPR.
  - apply switchIsPR.
Qed.

(* begin snippet checkPrfCorrect1:: no-out *)
Lemma checkPrfCorrect1 (l : list Formula) (f : Formula) (p : Prf l f):
 checkPrf (codeFormula L codeF codeR f) (codePrf L codeF codeR l f p) 
 =  S (codeList (map (codeFormula L codeF codeR) l)).
(* end snippet checkPrfCorrect1 *)
Proof.
  unfold checkPrf;
    rewrite
      (wellFormedFormulaCorrect1 L codeF codeArityF codeArityFIsCorrect1 codeR
         codeArityR codeArityRIsCorrect1).
  simpl; lazy beta delta [checkPrfHelp] in |- *.
  set
    (A :=
       fun p0 recs : nat =>
         let type := car (cdr p0) in
         switchPR type
           (switchPR (pred type)
              (switchPR (pred (pred type))
                 (switchPR (pred (pred (pred type)))
                    (switchPR (pred (pred (pred (pred type))))
                       (switchPR (pred (pred (pred (pred (pred type)))))
                          (switchPR (pred (pred (pred (pred 
                                                         (pred (pred type))))))
                             (switchPR
                                (pred 
                                   (pred (pred 
                                            (pred (pred (pred (pred type)))))))
                                (switchPR
                                   (pred
                                      (pred
                                         (pred
                                            (pred (pred 
                                                     (pred 
                                                        (pred (pred type))))))))
                                   (switchPR
                                      (pred
                                         (pred
                                            (pred
                                               (pred
                                                  (pred
                                                     (pred 
                                                        (pred 
                                                           (pred 
                                                              (pred type)))))))))
                                      (switchPR
                                         (pred
                                            (pred
                                               (pred
                                                  (pred
                                                     (pred
                                                        (pred
                                                           (pred
                                                              (pred (pred 
                                                                       (pred 
                                                                          type))))))))))
                                         (switchPR
                                            (pred
                                               (pred
                                                  (pred
                                                     (pred
                                                        (pred
                                                           (pred
                                                              (pred
                                                                 (pred
                                                                    (pred (pred (pred type)))))))))))
                                            (switchPR
                                               (pred
                                                  (pred
                                                     (pred
                                                        (pred
                                                           (pred
                                                              (pred
                                                                 (pred
                                                                    (pred
                                                                       (pred
                                                                          (pred (pred (pred type))))))))))))
                                               (switchPR
                                                  (pred
                                                     (pred
                                                        (pred
                                                           (pred
                                                              (pred
                                                                 (pred
                                                                    (pred
                                                                       (pred
                                                                          (pred
                                                                             (pred
                                                                                (pred (pred (pred type)))))))))))))
                                                  0 (checkPrfEQ5 p0 recs))
                                               (checkPrfEQ4 p0 recs))
                                            (checkPrfEQ3 p0 recs))
                                         (checkPrfEQ2 p0 recs))
                                      (checkPrfEQ1 p0 recs)) 
                                   (checkPrfFA3 p0 recs)) 
                                (checkPrfFA2 p0 recs)) (checkPrfFA1 p0 recs))
                          (checkPrfCP p0 recs)) (checkPrfIMP2 p0 recs))
                    (checkPrfIMP1 p0 recs)) (checkPrfGEN p0 recs))
              (checkPrfMP p0 recs)) (checkPrfAXM p0 recs)) 
    in *.
  induction p
    as
    [A0|
      Axm1 Axm2 A0 B p1 Hrecp1 p0 Hrecp0|
      Axm A0 v n p Hrecp|
      A0 B|
      A0 B C|
      A0 B|
      A0 v t|
      A0 v n|
      A0 B v|
    |
    |
    |
      R|
      f];
    unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList in |- *;
    rewrite computeEvalStrongRecHelp;
    unfold compose2, evalComposeFunc, evalOneParamList, evalList in |- *;
    simpl in |- *; rewrite cPairProjections1.
  - unfold A at 1 in |- *.
    repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ];
      simpl in |- *.
    unfold checkPrfAXM;
      repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ];
      simpl.
    rewrite Nat.eqb_refl. 
    reflexivity.
  - set (C :=
           cPair
             (cPair
                (cPair 1
                   (cPair (codeFormula L codeF codeR A0)
                      (codeFormula L codeF codeR B)))
                (codePrf L codeF codeR Axm1 (impH  A0 B) p1))
             (cPair (codeFormula L codeF codeR A0) 
                (codePrf L codeF codeR Axm2 A0 p0)))
      in *.
    unfold A at 1 in |- *.
    repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    simpl; unfold C at 1 in |- *.
    unfold checkPrfMP in |- *.
    repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    simpl in |- *.
    + repeat rewrite evalStrongRecHelp1.
      * rewrite Nat.eqb_refl.
        rewrite Hrecp0.
        replace
          (cPair 1
             (cPair (codeFormula L codeF codeR A0) 
                (codeFormula L codeF codeR B)))
          with (codeFormula L codeF codeR (impH A0 B)); 
          [ idtac | reflexivity ].
        rewrite Hrecp1.
        rewrite
          (wellFormedFormulaCorrect1 L codeF codeArityF 
             codeArityFIsCorrect1 codeR
             codeArityR codeArityRIsCorrect1).
        simpl in |- *.
        replace (map (codeFormula L codeF codeR) (Axm1 ++ Axm2)) 
          with
          (map (codeFormula L codeF codeR) Axm1 ++
             map (codeFormula L codeF codeR) Axm2).
        { rewrite codeAppCorrect; reflexivity. }
        generalize (codeFormula L codeF codeR); intro n.
        clear p1 A Hrecp1 Hrecp0 C.
        induction Axm1 as [| a Axm1 HrecAxm1].
        -- reflexivity.
        -- simpl; rewrite HrecAxm1; reflexivity.
      * eapply Nat.lt_le_trans; [ idtac | apply cPairLe2 ].
        eapply Nat.le_lt_trans; [ idtac | apply cPairLt2 ].
        unfold C in |- *; apply cPairLe2.
      * eapply Nat.lt_le_trans; [ idtac | apply cPairLe2 ].
        eapply Nat.le_lt_trans; [ idtac | apply cPairLt2 ].
        unfold C in |- *.
        apply cPairLe1.
  - unfold A at 1 in |- *.
    repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    simpl in |- *.
    unfold checkPrfGEN in |- *.
    repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    repeat rewrite evalStrongRecHelp1.
    + rewrite Hrecp.
      unfold pred in |- *.
      rewrite codeFreeVarListFormulaCorrect.
      rewrite codeInCorrect.
      induction (In_dec eq_nat_dec v (freeVarListFormula L Axm)).
      * elim n; assumption.
      * replace
          (charFunction 2 Nat.eqb 
             (cPair 3
                (cPair v (codeFormula L codeF codeR A0)))
             (cPair 3 (cPair v (codeFormula L codeF codeR A0)))) 
          with 1.
        { simpl; reflexivity. }
        simpl in |- *.
        rewrite Nat.eqb_refl.
        reflexivity.
    + eapply Nat.lt_le_trans; [ idtac | apply cPairLe2 ].
      eapply Nat.le_lt_trans; [ idtac | apply cPairLt2 ].
      apply cPairLe2.
  - unfold A at 1 in |- *.
    repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    simpl in |- *.
    unfold checkPrfIMP1 in |- *.
    repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    unfold charFunction in |- *.
    rewrite Nat.eqb_refl.
    reflexivity.
  - unfold A at 1 in |- *.
    repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    simpl in |- *.
    unfold checkPrfIMP2 in |- *.
    repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    unfold charFunction in |- *.
    rewrite Nat.eqb_refl.
    reflexivity.
  - unfold A at 1 in |- *.
    repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    simpl in |- *.
    unfold checkPrfCP in |- *.
    repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    unfold charFunction in |- *.
    rewrite Nat.eqb_refl.
    reflexivity.
  - unfold A at 1 in |- *.
    repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    simpl in |- *.
    unfold checkPrfFA1 in |- *.
    repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    rewrite codeSubFormulaCorrect.
    unfold charFunction in |- *.
    rewrite Nat.eqb_refl.
    rewrite (wellFormedTermCorrect1 L codeF codeArityF codeArityFIsCorrect1).
    reflexivity.
  - unfold A at 1 in |- *.
    repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    simpl in |- *.
    unfold checkPrfFA2 in |- *.
    repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    rewrite codeFreeVarFormulaCorrect.
    rewrite codeInCorrect.
    induction (In_dec eq_nat_dec v (freeVarFormula L A0)).
    + elim n; assumption.
    + unfold charFunction in |- *; rewrite Nat.eqb_refl.
      reflexivity.
  - unfold A at 1 in |- *.
    repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    simpl; unfold checkPrfFA3 in |- *.
    repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    unfold charFunction in |- *.
    now rewrite Nat.eqb_refl.
  - set (C :=
           cPair 0
             (cPair (codeTerm L codeF (var 0))
                (codeTerm L codeF (var 0))))
      in *.
    unfold A at 1 in |- *.
    (* Was working in V7.3 but starts converting for very long in v8...
Replace (car (cPairPi2 (cPair C (cPair (9) (0))))) with (9).
     *)
    (* For v8 *)
    cut (car (cdr (cPair C (cPair 9 0))) = 9);
      [ intro H; rewrite H; clear H | idtac ].
(**)
    + simpl in |- *; unfold checkPrfEQ1 in |- *.
      (* Conversion was short in V7.3 but is very long in V8...
Repeat First [Rewrite cPairProjections1|Rewrite cPairProjections2].
       *)
      (* For v8 *)
      rewrite (cPairProjections2 C (cPair 9 0)).
      rewrite (cPairProjections1 C (cPair 9 0)).
      rewrite (cPairProjections2 9 0).
      (* *)
      unfold C in |- *; unfold charFunction in |- *; rewrite Nat.eqb_refl.
      simpl in |- *.
      reflexivity.
    + (* Conversion was short in V7.3 but is very long in V8...
Repeat First [Rewrite cPairProjections1|Rewrite cPairProjections2].
       *)
      (* For v8 *)
      rewrite (cPairProjections2 C (cPair 9 0)).
      rewrite (cPairProjections1 9 0).
(* *)
      reflexivity.
  - set (C :=
           cPair 1
             (cPair
                (cPair 0
                   (cPair (codeTerm L codeF (var 0))
                      (codeTerm L codeF (var 1))))
                (cPair 0
                   (cPair (codeTerm L codeF (var 1))
                      (codeTerm L codeF (var 0)))))) in *.
    unfold A at 1 in |- *.
    cut (car (cdr (cPair C (cPair 10 0))) = 10).
    + generalize (car (cdr (cPair C (cPair 10 0)))).
      intros n H; rewrite H.
      simpl in |- *.
      unfold checkPrfEQ2 in |- *.
      replace
        (codeFormula L codeF codeR
           (impH  (equal (var 0) (var 1))
              (equal (var 1) (var 0)))) with C;
        [ idtac | reflexivity ].
      generalize C; intros C0.
      rewrite (cPairProjections2 C0 (cPair 10 0)).
      rewrite (cPairProjections2 10 0).
      rewrite (cPairProjections1 C0 (cPair 10 0)).
      unfold charFunction in |- *.
      repeat rewrite Nat.eqb_refl.
      reflexivity.
    + rewrite (cPairProjections2 C (cPair 10 0)).
      now rewrite (cPairProjections1 10 0).
  - set (C :=
           cPair 1
             (cPair
                (cPair 0
                   (cPair (codeTerm L codeF (var 0))
                      (codeTerm L codeF (var 1))))
                (cPair 1
                   (cPair
                      (cPair 0
                         (cPair (codeTerm L codeF (var 1))
                            (codeTerm L codeF (var 2))))
                      (cPair 0
                         (cPair (codeTerm L codeF (var 0))
                            (codeTerm L codeF (var 2)))))))) 
      in *.
    unfold A at 1 in |- *.
    cut (car (cdr (cPair C (cPair 11 0))) = 11).
    + generalize (car (cdr (cPair C (cPair 11 0)))).
      intros n H; rewrite H; simpl. 
      unfold checkPrfEQ3 in |- *.
      replace
        (codeFormula L codeF codeR
           (impH (equal (var 0) (var 1))
              (impH (equal (var 1) (var 2))
                 (equal (var 0) (var 2))))) 
        with C; [ idtac | reflexivity ].
      generalize C; intros.
      rewrite (cPairProjections2 C0 (cPair 11 0)).
      rewrite (cPairProjections1 C0 (cPair 11 0)).
      rewrite (cPairProjections2 11 0).
      unfold charFunction in |- *.
      repeat rewrite Nat.eqb_refl.
      reflexivity.
      + rewrite (cPairProjections2 C (cPair 11 0)).
        rewrite (cPairProjections1 11 0).
        reflexivity.
  - unfold A at 1 in |- *.
    repeat first [ rewrite cPairProjections1 | 
                   rewrite cPairProjections2 ].
    simpl in |- *.
    unfold checkPrfEQ4 in |- *.
    repeat first 
      [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    rewrite codeArityRIsCorrect1.
    replace
      (codeAxmEqHelp (pred (S (arityR L R)))
         (codeIff
            (cPair (S (S (S (S (codeR R)))))
               (codeNVars1 (pred (S (arityR L  R)))))
                                      
            (cPair (S (S (S (S (codeR R)))))
               (codeNVars2 
                  (pred (S (arity L (inl (Functions L) R)))))))) 
      with
      (codeFormula L codeF codeR (AxmEq4 L R)).
    unfold charFunction in |- *.
    repeat rewrite Nat.eqb_refl.
    reflexivity.
    unfold AxmEq4 in |- *.
    clear A.
    simpl in |- *.
    induction (codeNVarsCorrect (arityR L R)).
    rewrite H.
    rewrite H0.
    clear H H0.
    induction (nVars L (arity L (inl (Functions L) R))).
    simpl in |- *.
    replace
      (codeIff
         (cPair (S (S (S (S (codeR R)))))
            (codeTerms L codeF (arityR L R) a))
         (cPair (S (S (S (S (codeR R)))))
            (codeTerms L codeF (arityR L R) b)))
        with
        (codeFormula L codeF codeR 
           (iffH (atomic R a) (atomic R b))).
    + generalize (arityR L R).
      intros n; induction n as [| n Hrecn].
      * reflexivity.
      * simpl; now rewrite Hrecn.
    + rewrite <- codeIffCorrect; reflexivity.
  - unfold A at 1 in |- *.
    repeat first 
      [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    simpl in |- *.
    unfold checkPrfEQ5 in |- *.
    repeat first 
      [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    rewrite codeArityFIsCorrect1.
    replace
      (codeAxmEqHelp (pred (S (arityF L f)))
         (cPair 0
            (cPair
               (cPair (S (codeF f))
                  (codeNVars1 
                     (pred (S (arityF L f)))))
               (cPair (S (codeF f))
                  (codeNVars2 
                     (pred (S (arityF L f)))))))) 
      with  (codeFormula L codeF codeR (AxmEq5 L f)).
    + unfold charFunction in |- *; repeat rewrite Nat.eqb_refl.
      reflexivity.
    + unfold AxmEq5 in |- *; clear A; simpl. 
      induction (codeNVarsCorrect (arityF L f)).
      rewrite H, H0. 
      clear H H0.
      induction (nVars L (arityF L f)).
      simpl;
        replace
          (cPair 0
             (cPair
                (cPair (S (codeF f))
                   (codeTerms L codeF
                      (arityF L f) a))
                    (cPair (S (codeF f))
                       (codeTerms L codeF 
                          (arityF L f) b)))) 
        with
 (codeFormula L codeF codeR 
    (equal (apply f a) (apply f b))).
      * generalize (arityF L f).
        intros n;induction n as [| n Hrecn].
        -- reflexivity.
        -- simpl; rewrite Hrecn.
           reflexivity.
      * reflexivity.
Qed.

(* begin snippet checkPrfCorrect2:: no-out *)
Lemma checkPrfCorrect2 (n m : nat):
 checkPrf n m <> 0 ->
 exists f : Formula,
   codeFormula L codeF codeR f = n /\
   (exists l : list Formula,
      (exists p : Prf l f, codePrf L codeF codeR l f p = m)).
(* end snippet checkPrfCorrect2:: no-out *)
Proof.
  revert n m;
  assert (multLemma1 : forall a b : nat, a * b <> 0 -> a <> 0).
  { intros a b H H0; apply H; rewrite H0;  reflexivity. }
  assert (multLemma2 : forall a b : nat, a * b <> 0 -> b <> 0).
  { intros a b H H0; rewrite Nat.mul_comm in H.
    now apply (multLemma1 b a). 
  } 
  assert
    (H: forall m n : nat,
        n < m ->
        checkPrf (car n) (cdr n) <> 0 ->
        exists f : Formula,
          (exists l : list Formula,
              (exists p : Prf l f,
                  cPair (codeFormula L codeF codeR f) 
                    (codePrf L codeF codeR l f p) =
                    n))).
  { 
    intro m; induction m as [| m Hrecm].
    - intros n H H0; elim (Nat.nlt_0_r _ H).
    - intros n H H0; assert (H': n <= m) by lia.
      rewrite Nat.lt_eq_cases in H'; destruct H' as [H1 | H1].
      + apply Hrecm; assumption.
      + unfold checkPrf in H0.
        assert (H2: wellFormedFormula (car n) <> 0).
        { destruct (wellFormedFormula (car n)).
          assumption.
          discriminate.
        } 
        induction
          (wellFormedFormulaCorrect2 L codeF codeArityF 
             codeArityFIsCorrect1
             codeArityFIsCorrect2 codeR codeArityR 
             codeArityRIsCorrect1
             codeArityRIsCorrect2 _ H2) as [x H3].
        exists x.
        destruct (wellFormedFormula (car n)).
        * now elim H2.
        * simpl in H0; clear H2; unfold checkPrfHelp in H0.
        (* to fix !!! *)
         set (A := 
                 fun p recs : nat =>
                   switchPR (car (cdr p))
                     (switchPR (pred (car (cdr p)))
                        (switchPR (pred (pred (car (cdr p))))
                           (switchPR 
                              (pred (pred (pred (car 
                                                 (cdr p)))))
                            (switchPR 
                               (pred (pred 
                                        (pred (pred 
                                                 (car
                                                    (cdr p))))))
                               (switchPR
                                  (pred 
                                     (pred (pred 
                                              (pred (pred 
                                                       (car 
                                                          (cdr p)))))))
                                  (switchPR
                                     (pred
                                        (pred
                                           (pred
                                              (pred (pred (pred (car (cdr p))))))))
                                     (switchPR
                                        (pred
                                           (pred
                                              (pred
                                                 (pred
                                                    (pred
                                                       (pred (pred (car (cdr p)))))))))
                                        (switchPR
                                           (pred
                                              (pred
                                                 (pred
                                                    (pred
                                                       (pred
                                                          (pred
                                                             (pred
                                                                (pred
                                                                   (car (cdr p))))))))))
                                           (switchPR
                                              (pred
                                                 (pred
                                                    (pred
                                                       (pred
                                                          (pred
                                                             (pred
                                                                (pred
                                                                   (pred
                                                                      (pred
                                                                         (car (cdr p)))))))))))
                                              (switchPR
                                                 (pred
                                                    (pred
                                                       (pred
                                                          (pred
                                                             (pred
                                                                (pred
                                                                   (pred
                                                                      (pred
                                                                         (pred
                                                                            (pred
                                                                               (car (cdr p))))))))))))
                                                 (switchPR
                                                    (pred
                                                       (pred
                                                          (pred
                                                             (pred
                                                                (pred
                                                                   (pred
                                                                      (pred
                                                                         (pred
                                                                            (pred
                                                                               (pred
                                                                                  (pred
                                                                                     (car (cdr p)))))))))))))
                                                    (switchPR
                                                       (pred
                                                          (pred
                                                             (pred
                                                                (pred
                                                                   (pred
                                                                      (pred
                                                                         (pred
                                                                            (pred
                                                                               (pred
                                                                                  (pred
                                                                                     (pred
                                                                                        (pred
                                                                                           (car (cdr p))))))))))))))
                                                       (switchPR
                                                          (pred
                                                             (pred
                                                                (pred
                                                                   (pred
                                                                      (pred
                                                                         (pred
                                                                            (pred
                                                                               (pred
                                                                                  (pred
                                                                                     (pred
                                                                                        (pred
                                                                                           (pred
                                                                                              (pred
                                                                                                 (car (cdr p)))))))))))))))
                                                          0 (checkPrfEQ5 p recs))
                                                       (checkPrfEQ4 p recs))
                                                    (checkPrfEQ3 p recs))
                                                 (checkPrfEQ2 p recs)) 
                                              (checkPrfEQ1 p recs)) 
                                           (checkPrfFA3 p recs)) (checkPrfFA2 p recs))
                                     (checkPrfFA1 p recs)) (checkPrfCP p recs))
                               (checkPrfIMP2 p recs)) (checkPrfIMP1 p recs))
                         (checkPrfGEN p recs)) (checkPrfMP p recs)) 
                   (checkPrfAXM p recs)) in *.
         unfold evalStrongRec, evalComposeFunc, 
           evalOneParamList, evalList in H0;
           rewrite computeEvalStrongRecHelp in H0;
           unfold compose2, evalComposeFunc, evalOneParamList, 
           evalList in H0; simpl in H0.
         rewrite cPairProjections1 in H0.
         assert (H2: cPair (car (cdr n)) (cdr (cdr n)) = 
                   cdr n)
         by apply cPairProjections.
         unfold A at 1 in H0.
         repeat first
           [ rewrite cPairProjections1 in H0 | 
             rewrite cPairProjections2 in H0 ].
         destruct (car (cdr n)).
         --  simpl in H0.
             unfold checkPrfAXM in H0.
             repeat first
               [ rewrite cPairProjections1 in H0 | 
                 rewrite cPairProjections2 in H0 ].
             rewrite <- H3 in H0.
             induction (eq_nat_dec (cdr (cdr n)) 
                          (codeFormula L codeF codeR x)) as [a | ?].
             ++ exists (x :: nil).
                exists (AXM L x).
                rewrite H3.
                simpl in |- *.
                rewrite a in H2.
                rewrite H2.
                apply cPairProjections.
             ++ elim H0.
                unfold charFunction in |- *.
                rewrite nat_eqb_false.
                reflexivity.
                assumption.
         -- destruct n1.
            ++ simpl in H0.
               unfold checkPrfMP in H0.
               repeat first
                 [ rewrite cPairProjections1 in H0 | 
                   rewrite cPairProjections2 in H0 ].
               assert (H4: cdr (cdr n) < n).
               { apply Nat.lt_le_trans with (cPair 1 (cdr (cdr n)));
                   [ idtac | rewrite H2; apply cPairLe2A ].
                 apply cPairLt2.
               }
               assert (H5: car (cdr (cdr n)) < n).
               { apply Nat.le_lt_trans with (cdr (cdr n)).
                 apply cPairLe1A.
                 assumption.
               } 
               assert (H6: cdr (cdr (cdr n)) < n).
               { apply Nat.le_lt_trans with (cdr (cdr n)).
                 apply cPairLe2A.
                 assumption.
               }
            rewrite evalStrongRecHelp1 in H0.
            ** rewrite evalStrongRecHelp1 in H0.
               assert (wellFormedFormula 
                      (car (cdr (cdr (cdr n)))) <> 0).
               { intro H7; apply H0; now rewrite H7. }
               induction
                 (eq_nat_dec (car (car (cdr (cdr n))))
                    (codeImp (car (cdr (cdr (cdr n)))) 
                       (car n))).
               induction
                 (wellFormedFormulaCorrect2 L codeF codeArityF 
                    codeArityFIsCorrect1
                    codeArityFIsCorrect2 codeR codeArityR codeArityRIsCorrect1
                    codeArityRIsCorrect2 _ H7).
               assert
                 (H9: checkPrf (car (car (cdr (cdr n))))
                    (cdr (car (cdr (cdr n)))) <> 0).
               { unfold checkPrf in |- *.
                 rewrite a.
                 rewrite <- H3.
                 rewrite <- H8.
                 rewrite codeImpCorrect.
                 rewrite
                   (wellFormedFormulaCorrect1 L codeF codeArityF 
                      codeArityFIsCorrect1 codeR
                      codeArityR codeArityRIsCorrect1).
                 simpl; unfold checkPrfHelp in |- *; fold A in |- *.
                 rewrite H8.
                 rewrite H3.
                 replace
                   (cPair 1 (cPair (car (cdr
                                                (cdr (cdr n)))) 
                               (car n)))
                   with (car (car (cdr (cdr n)))).
                 { rewrite cPairProjections.
                   destruct (evalStrongRec 0 A 
                               (car (cdr (cdr n)))).
                   rewrite Nat.mul_comm in H0.
                   rewrite
                     (Nat.mul_comm
                        (charFunction 2 Nat.eqb 
                           (car
                              (car (cdr 
                                           (cdr n))))
                           (codeImp (car (cdr (cdr 
                                                           (cdr n))))
                              (car n))))
                     in H0.
                   simpl in H0.
                   assumption.
                   discriminate.
                 }
               }
               assert
                   (H10: checkPrf (car (cdr (cdr 
                                                         (cdr n))))
                      (cdr (cdr (cdr (cdr n)))) <> 0).
               { unfold checkPrf; rewrite <- H8.
                 rewrite
                   (wellFormedFormulaCorrect1 L codeF codeArityF 
                      codeArityFIsCorrect1 codeR
                      codeArityR codeArityRIsCorrect1).
                 simpl; unfold checkPrfHelp; fold A.
                 rewrite H8.
                 rewrite cPairProjections.
                 destruct (evalStrongRec 0 A 
                             (cdr (cdr (cdr n)))).
                 - rewrite Nat.mul_comm in H0.
                   rewrite (Nat.mul_comm
                              (charFunction 2 Nat.eqb 
                                 (car (car (cdr (cdr n))))
                                 (codeImp (car (cdr 
                                                       (cdr (cdr n))))
                                    (car n))))
                     in H0.
                   rewrite (Nat.mul_comm (evalStrongRec 0 A 
                                            (car (cdr (cdr n)))))
                     in H0.
                 simpl in H0.
                 assumption.
                 - discriminate.
               } 
               assert (H11: car (cdr (cdr n)) < m).
               { apply Nat.lt_le_trans with n.
                 assumption.
                 rewrite H1; apply le_n.
               }
               assert (H12: cdr (cdr (cdr n)) < m).
               { apply Nat.lt_le_trans with n.
                 assumption.
                 rewrite H1; apply le_n.
               } 
               induction (Hrecm _ H11 H9).
               induction (Hrecm _ H12 H10).
               induction H13 as (x3, H13).
               induction H13 as (x4, H13).
               induction H14 as (x5, H14).
               induction H14 as (x6, H14).
               exists (x3 ++ x5).
               rewrite <- H13 in a.
               rewrite <- H14 in a.
               repeat rewrite cPairProjections1 in a.
               rewrite <- H3 in a.
               rewrite codeImpCorrect in a.
               assert (H15: x1 = impH x2 x).
               { apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
                 assumption.
               } 
               cut
                 (cPair (codeFormula L codeF codeR x1) 
                    (codePrf L codeF codeR x3 x1 x4) =
                    car (cdr (cdr n))).
               { generalize x4; clear H13 x4; rewrite H15.
                 intros x4 H13; exists (MP L x3 x5 x2 x x4 x6).
                 rewrite <- (cPairProjections n).
                 rewrite H3.
                 simpl in |- *.
                 rewrite <- H2.
                 replace
                   (cPair 1
                      (cPair (codeFormula L codeF codeR x2) 
                         (codeFormula L codeF codeR x)))
                   with (codeFormula L codeF codeR x1).
                 { rewrite H14;  rewrite H15; rewrite H13.
                   rewrite cPairProjections; reflexivity.
                 } 
               } 
               assumption.
               unfold charFunction in H0; rewrite nat_eqb_false in H0.
               rewrite Nat.mul_comm in H0.
               simpl in H0; elim H0.
               reflexivity.
               assumption.
               rewrite cPairProjections; assumption.
            ** rewrite cPairProjections; assumption.
            ++ destruct n1.
               ** simpl in H0.
                  unfold checkPrfGEN in H0.
                  repeat first
                    [ rewrite cPairProjections1 in H0 |
                      rewrite cPairProjections2 in H0 ].
                  assert (cdr (cdr (cdr n)) < n).
                  eapply Nat.le_lt_trans.
                  apply cPairLe2A.
                  apply Nat.lt_le_trans with (cPair 2 (cdr (cdr n)));
                    [ idtac | rewrite H2; apply cPairLe2A ].
                  apply cPairLt2.
                  rewrite evalStrongRecHelp1 in H0.
                  induction
                    (eq_nat_dec
                       (cPair 3
                          (cPair (car (cdr (cdr n)))
                             (car (cdr (cdr (cdr n)))))) 
                       (car n)).
                  rewrite <- a in H3.
                  destruct x as [t t0| r t| f f0| f| n1 f]; simpl in H3;
                    try
                      match goal with
                      | H:(cPair ?X1 _ = cPair ?X2 _) |- _ =>
                          cut (X1 = X2); [ intro I; discriminate I 
                                         | eapply cPairInj1; apply H ]
                      end.
                  assert (H5: n1 = car (cdr (cdr n))).
                  { eapply cPairInj1.
                    eapply cPairInj2.
                    apply H3.
                  } 
                  assert
                    (H6: codeFormula L codeF codeR f = 
                           car (cdr (cdr (cdr n)))).
                  { eapply cPairInj2. 
                    eapply cPairInj2.
                    apply H3.
                  } 
                  assert
                    (H7: checkPrf (car (cdr (cdr (cdr n))))
                           (cdr (cdr (cdr (cdr n)))) <> 0).
                  { unfold checkPrf; rewrite <- H6.
                    rewrite
                      (wellFormedFormulaCorrect1 L codeF codeArityF 
                         codeArityFIsCorrect1 codeR
                         codeArityR codeArityRIsCorrect1).
                    simpl; unfold checkPrfHelp; fold A; rewrite H6.
                    rewrite cPairProjections.
                    destruct (evalStrongRec 0 A 
                                (cdr (cdr (cdr n)))).
                    rewrite Nat.mul_comm in H0.
                    simpl in H0.
                    assumption.
                    discriminate.
                  } 
                  assert (H8: cdr (cdr (cdr n)) < m).
                  { apply Nat.lt_le_trans with n.
                    assumption.
                    rewrite H1; apply le_n.
                  } 
                  induction (Hrecm _ H8 H7)as [x H9].
                  induction H9 as (x0, H9).
                  induction H9 as (x1, H9).
                  exists x0.
                  rewrite <- H5 in H0.
                  rewrite <- H9 in H0.
                  assert
                    (H10: checkPrf (codeFormula L codeF codeR x) 
                            (codePrf L codeF codeR x0 x x1) =
                            S (codeList (map (codeFormula L codeF codeR) x0)))
                    by apply checkPrfCorrect1.
                  unfold checkPrf in H10.
                  rewrite
                    (wellFormedFormulaCorrect1 L codeF codeArityF 
                       codeArityFIsCorrect1 codeR
                       codeArityR codeArityRIsCorrect1) in H10.
                  simpl in H10; unfold checkPrfHelp in H10; fold A in H10.
                  rewrite H10 in H0.
                  unfold pred in H0.
                  rewrite codeFreeVarListFormulaCorrect in H0.
                  rewrite codeInCorrect in H0.
                  induction (In_dec eq_nat_dec n1 (freeVarListFormula L x0)).
                  rewrite (Nat.mul_comm 
                             (S (codeList 
                                   (map (codeFormula L codeF codeR) x0)))) 
                    in H0.
                  rewrite Nat.mul_comm in H0.
                  simpl in H0.
                  elim H0; reflexivity.
                  rewrite <- H9 in H6.
                  rewrite cPairProjections1 in H6.
                  cut
                    (cPair (codeFormula L codeF codeR x) 
                       (codePrf L codeF codeR x0 x x1) =
                       cdr (cdr (cdr n))).
                  { generalize x1.
                    clear H10 H0 x1 H9.
                    replace x with f.
                    - intros x1 H0; exists (GEN L x0 f n1 b x1).
                      simpl; rewrite H3.
                      rewrite a.
                      rewrite H0.
                      rewrite H5.
                      rewrite cPairProjections.
                      rewrite H2.
                      apply cPairProjections.
                    - apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
                      assumption.
                  } 
                  assumption.
                  unfold charFunction in H0.
                  rewrite nat_eqb_false in H0.
                  elim H0.
                  simpl; reflexivity.
                  assumption.
                  rewrite cPairProjections.
                  assumption.
               ** destruct n1.
                  *** simpl in H0.
                      unfold checkPrfIMP1 in H0.
                      repeat first
                        [ rewrite cPairProjections1 in H0 |
                          rewrite cPairProjections2 in H0 ].
                      exists (nil (A:=Formula)).
                      rewrite <- H3 in H0.
                      induction
                        (eq_nat_dec
                           (cPair 1
                              (cPair (car (cdr (cdr n)))
                                 (cPair 1
                                    (cPair (cdr (cdr (cdr n)))
                                       (car (cdr (cdr n)))))))
                           (codeFormula L codeF codeR x)).
                      destruct x as [t t0| r t| f f0| f| n1 f]; simpl in a;
                        try
                          match goal with
                          | H:(cPair ?X1 _ = cPair ?X2 _) |- _ =>
                              cut (X1 = X2); 
                              [ intro I; discriminate I | eapply cPairInj1; 
                                                          apply H ]
                          end.
                      assert (H4: car (cdr (cdr n)) = 
                                    codeFormula L codeF codeR f).
                      { eapply cPairInj1.
                        eapply cPairInj2.
                        apply a.
                      } 
                      assert
                        (H5: cPair 1
                           (cPair (cdr (cdr (cdr n)))
                              (car (cdr (cdr n)))) = 
                           codeFormula L codeF codeR f0).
                      { eapply cPairInj2.
                        eapply cPairInj2.
                        apply a.
                      } 
                      clear a.
                      destruct f0 as [t t0| r t| f0 f1| f0| n1 f0]; 
                        simpl in H5;
                        try
                          match goal with
                          | H:(cPair ?X1 _ = cPair ?X2 _) |- _ =>
                              cut (X1 = X2); 
                              [ intro I; discriminate I | eapply cPairInj1; 
                                                          apply H ]
                          end.
                      assert (H6:cdr (cdr (cdr n)) = 
                                   codeFormula L codeF codeR f0).
                      { eapply cPairInj1; eapply cPairInj2.
                        apply H5.
                      }
                      assert (H7: car (cdr (cdr n)) = 
                                    codeFormula L codeF codeR f1).
                      { eapply cPairInj2.
                        eapply cPairInj2.
                        apply H5.
                      } 
                      assert (H8: f1 = f).
                      { apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
                        transitivity (car (cdr (cdr n))).
                        symmetry  in |- *.
                        assumption.
                        assumption.
                      } 
                      rewrite H8; rewrite H8 in H3.
                      exists (IMP1 L f f0).
                      rewrite H3.
                      simpl in |- *.
                      rewrite <- H4.
                      rewrite <- H6.
                      rewrite cPairProjections.
                      rewrite H2.
                      apply cPairProjections.
                      elim H0.
                      unfold charFunction in |- *.
                      rewrite nat_eqb_false.
                      reflexivity.
                      assumption.
                  *** destruct n1.
                      simpl in H0.
                      unfold checkPrfIMP2 in H0.
                      repeat first
                        [ rewrite cPairProjections1 in H0 | 
                          rewrite cPairProjections2 in H0 ].
                      exists (nil (A:=Formula)).
                      clear A.
                      rewrite <- H3 in H0.
                      rename x into f.
                      induction
                        (eq_nat_dec
                           (cPair 1
                              (cPair
                                 (cPair 1
                                    (cPair (car (cdr (cdr n)))
                                       (cPair 1
                                          (cPair (car (cdr (cdr (cdr n))))
                                             (cdr (cdr (cdr (cdr n))))))))
                                 (cPair 1
                                    (cPair
                                       (cPair 1
                                          (cPair (car (cdr (cdr n)))
                                             (car (cdr (cdr (cdr n))))))
                                       (cPair 1
                                          (cPair (car (cdr (cdr n)))
                                             (cdr (cdr (cdr (cdr n))))))))))
                           (codeFormula L codeF codeR f)).
                      repeat
                        match goal with
                        | H:(cPair ?X1 (cPair ?X2 ?X3) = 
                               cPair ?X1 (cPair ?X4 ?X5)) |- _ =>
                            assert (X2 = X4);
                            [ eapply cPairInj1; eapply cPairInj2; apply H
                            | assert (X3 = X5);
                              [ eapply cPairInj2; eapply cPairInj2; apply H | clear H ] ]
                        | H:(cPair ?X1 (cPair _ _) = 
                               codeFormula L codeF codeR ?X2) |- _ =>
                            destruct X2;
                            simpl in H;
                            try
                              match goal with
                              | J:(cPair ?X1 _ = cPair ?X2 _) |- _ =>
                                  cut (X1 = X2);
                                  [ intro I; discriminate I | 
                                    eapply cPairInj1; apply J ]
                              end
                        end.
                      rewrite H3.
                      replace f2_2_1 with f1_1.
                      replace f1_2_2 with f2_2_2.
                      replace f1_2_1 with f2_1_2.
                      replace f2_1_1 with f1_1.
                      exists (IMP2 L f1_1 f2_1_2 f2_2_2).
                      simpl in |- *.
                      rewrite <- H9.
                      rewrite <- H8.
                      rewrite cPairProjections.
                      rewrite <- H6.
                      rewrite cPairProjections.
                      rewrite H2.
                      apply cPairProjections.
                      apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
                      transitivity (car (cdr (cdr n)));
                        [ symmetry  in |- *; assumption | assumption ].
                      apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
                      transitivity 
                        (car (cdr (cdr (cdr n))));
                        [ symmetry  in |- *; assumption | assumption ].
                      apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
                      transitivity
                        (cdr (cdr (cdr (cdr n))));
                        [ symmetry  in |- *; assumption | assumption ].
                      apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
                      transitivity (car (cdr (cdr n)));
                        [ symmetry  in |- *; assumption | assumption ].
                      elim H0.
                      unfold charFunction in |- *.
                      rewrite nat_eqb_false.
                      reflexivity.
                      assumption.
                      destruct n1.
                      simpl in H0.
                      unfold checkPrfCP in H0.
                      clear A.
                      repeat first
                        [ rewrite cPairProjections1 in H0 |
                          rewrite cPairProjections2 in H0 ].
                      exists (nil (A:=Formula)).
                      rewrite <- H3 in H0.
                      rename x into f.
                      induction
                        (eq_nat_dec
                           (cPair 1
                              (cPair
                                 (cPair 1
                                    (cPair (cPair 2 (car (cdr 
                                                                 (cdr n))))
                                       (cPair 2 (cdr (cdr (cdr n))))))
                                 (cPair 1
                                    (cPair (cdr (cdr (cdr n)))
                                       (car (cdr (cdr n)))))))
                           (codeFormula L codeF codeR f)).
                      repeat
                        match goal with
                        | H:(cPair 1 (cPair ?X2 ?X3) = 
                               cPair 1 (cPair ?X4 ?X5)) |- _ =>
                            assert (X2 = X4);
                            [ eapply cPairInj1; eapply cPairInj2; apply H
                            | assert (X3 = X5);
                              [ eapply cPairInj2; eapply cPairInj2; 
                                apply H | clear H ] ]
                        | H:(cPair 2 ?X2 = cPair 2 ?X4) |- _ =>
                            assert (X2 = X4); 
                            [ eapply cPairInj2; apply H | clear H ]
                        | H:(cPair ?X1 _ = 
                               codeFormula L codeF codeR ?X2) |- _ =>
                            destruct X2;
                            simpl in H;
                            try
                              match goal with
                              | J:(cPair ?X1 _ = cPair ?X2 _) |- _ =>
                                  cut (X1 = X2);
                                  [ intro I; discriminate I |
                                    eapply cPairInj1; apply J ]
                              end
                        end.
                      rewrite H3.
                      replace f2_2 with f1_1.
                      replace f1_2 with f2_1.
                      exists (CP L f1_1 f2_1).
                      simpl in |- *.
                      rewrite <- H8.
                      rewrite <- H6.
                      rewrite cPairProjections.
                      rewrite H2.
                      apply cPairProjections.
                      apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
                      transitivity (cdr (cdr (cdr n)));
                        [ symmetry  in |- *; assumption | assumption ].
                      apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
                      transitivity (car (cdr (cdr n)));
                        [ symmetry  in |- *; assumption | assumption ].
                      elim H0.
                      unfold charFunction in |- *.
                      rewrite nat_eqb_false.
                      reflexivity.
                      assumption.
                      destruct n1.
                      simpl in H0.
                      unfold checkPrfFA1 in H0.
                      clear A.
                      repeat first
                        [ rewrite cPairProjections1 in H0 | 
                          rewrite cPairProjections2 in H0 ].
                      exists (nil (A:=Formula)).
                      rewrite <- H3 in H0.
                      rename x into f.
                      induction
                        (eq_nat_dec
                           (cPair 1
                              (cPair
                                 (cPair 3
                                    (cPair (car (cdr (cdr (cdr n))))
                                       (car (cdr (cdr n)))))
                                 (codeSubFormula (car (cdr (cdr n)))
                                    (car (cdr (cdr (cdr n))))
                                    (cdr (cdr (cdr (cdr n)))))))
                           (codeFormula L codeF codeR f)).
                      repeat
                        match goal with
                        | H:(cPair 1 (cPair ?X2 ?X3) = cPair 1 (cPair ?X4 ?X5)) |- _ =>
                            assert (X2 = X4);
                            [ eapply cPairInj1; eapply cPairInj2; apply H
                            | assert (X3 = X5);
                              [ eapply cPairInj2; eapply cPairInj2; apply H |
                                clear H ] ]
                        | H:(cPair 3 (cPair ?X2 ?X3) = 
                               cPair 3 (cPair ?X4 ?X5)) |- _ =>
                            assert (X2 = X4);
                            [ eapply cPairInj1; eapply cPairInj2; apply H
                            | assert (X3 = X5);
                              [ eapply cPairInj2; eapply cPairInj2; apply H | 
                                clear H ] ]
                        | H:(cPair ?X1 _ = codeFormula L codeF codeR ?X2) 
                          |- _ =>
                            destruct X2;
                            simpl in H;
                            try
                              match goal with
                              | J:(cPair ?X1 _ = cPair ?X2 _) |- _ =>
                                  cut (X1 = X2);
                                  [ intro I; discriminate I | 
                                    eapply cPairInj1; apply J ]
                              end
                        end.
                      rewrite H3.
                      rewrite H6 in H5.
                      rewrite H7 in H5.
                      assert (H4: wellFormedTerm 
                                    (cdr
                                       (cdr 
                                          (cdr (cdr n)))) <> 0).
                      { eapply multLemma1.
                        apply H0.
                      } 
                      induction
                        (wellFormedTermCorrect2 L codeF codeArityF 
                           codeArityFIsCorrect1
                           codeArityFIsCorrect2 _ H4).
                      rewrite <- H8 in H5.
                      rewrite codeSubFormulaCorrect in H5.
                      replace f2 with (substituteFormula L f1 n1 x).
                      exists (FA1 L f1 n1 x).
                      simpl in |- *.
                      rewrite <- H7.
                      rewrite <- H6.
                      rewrite H8.
                      repeat rewrite cPairProjections.
                      rewrite H2.
                      apply cPairProjections.
                      apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
                      assumption.
                      elim H0.
                      unfold charFunction in |- *.
                      rewrite nat_eqb_false.
                      rewrite Nat.mul_comm.
                      reflexivity.
                      assumption.
                      destruct n1.
                      simpl in H0.
                      unfold checkPrfFA2 in H0.
                      clear A.
                      repeat first
                        [ rewrite cPairProjections1 in H0 | 
                          rewrite cPairProjections2 in H0 ].
                      exists (nil (A:=Formula)).
                      rewrite <- H3 in H0.
                      rename x into f.
                      induction
                        (eq_nat_dec
                           (cPair 1
                              (cPair (car (cdr (cdr n)))
                                 (cPair 3
                                    (cPair (cdr (cdr (cdr n)))
                                       (car (cdr (cdr n)))))))
                           (codeFormula L codeF codeR f)).
                      repeat
                        match goal with
                        | H:(cPair 1 (cPair ?X2 ?X3) = 
                               cPair 1 (cPair ?X4 ?X5)) |- _ =>
                            assert (X2 = X4);
                            [ eapply cPairInj1; eapply cPairInj2; apply H
                            | assert (X3 = X5);
                              [ eapply cPairInj2; eapply cPairInj2; apply H | 
                                clear H ] ]
                        | H:(cPair 3 (cPair ?X2 ?X3) = 
                               cPair 3 (cPair ?X4 ?X5)) |- _ =>
                            assert (X2 = X4);
                            [ eapply cPairInj1; eapply cPairInj2; apply H
                            | assert (X3 = X5);
                              [ eapply cPairInj2; eapply cPairInj2; apply H |
                                clear H ] ]
                        | H:(cPair ?X1 _ = codeFormula L codeF codeR ?X2)
                          |- _ =>
                            destruct X2;
                            simpl in H;
                            try
                              match goal with
                              | J:(cPair ?X1 _ = cPair ?X2 _) |- _ =>
                                  cut (X1 = X2);
                                  [ intro I; discriminate I | 
                                    eapply cPairInj1; apply J ]
                              end
                        end.
                      rewrite H3.
                      replace f2 with f1.
                      rewrite H6 in H0.
                      rewrite H4 in H0.
                      rewrite codeFreeVarFormulaCorrect in H0.
                      rewrite codeInCorrect in H0.
                      induction (In_dec eq_nat_dec n1 (freeVarFormula L f1)).
                      elim H0.
                      reflexivity.
                      exists (FA2 L f1 n1 b).
                      simpl in |- *.
                      rewrite <- H4.
                      rewrite <- H6.
                      rewrite cPairProjections.
                      rewrite H2.
                      apply cPairProjections.
                      apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
                      transitivity (car (cdr (cdr n)));
                        [ symmetry  in |- *; assumption | assumption ].
                      elim H0.
                      unfold charFunction in |- *.
                      rewrite nat_eqb_false.
                      rewrite Nat.mul_comm.
                      reflexivity.
                      assumption.
                      destruct n1.
                      simpl in H0.
                      unfold checkPrfFA3 in H0.
                      clear A.
                      repeat first
                        [ rewrite cPairProjections1 in H0 | 
                          rewrite cPairProjections2 in H0 ].
                      exists (nil (A:=Formula)).
                      rewrite <- H3 in H0.
                      rename x into f.
                      induction
                        (eq_nat_dec
                           (cPair 1
                              (cPair
                                 (cPair 3
                                    (cPair (cdr (cdr (cdr (cdr n))))
                                       (cPair 1
                                          (cPair (car (cdr (cdr n)))
                                             (car (cdr (cdr (cdr n))))))))
                                 (cPair 1
                                    (cPair
                                       (cPair 3
                                          (cPair (cdr (cdr (cdr (cdr n))))
                                             (car (cdr (cdr n)))))
                                       (cPair 3
                                          (cPair (cdr (cdr (cdr (cdr n))))
                                             (car (cdr (cdr (cdr n))))))))))
                           (codeFormula L codeF codeR f)).
                      repeat
                        match goal with
                        | H:(cPair 1 (cPair ?X2 ?X3) = 
                               cPair 1 (cPair ?X4 ?X5)) |- _ =>
                            assert (X2 = X4);
                            [ eapply cPairInj1; eapply cPairInj2; apply H
                            | assert (X3 = X5);
                              [ eapply cPairInj2; eapply cPairInj2; apply H 
                              | clear H ] ]
                        | H:(cPair 3 (cPair ?X2 ?X3) = 
                               cPair 3 (cPair ?X4 ?X5)) |- _ =>
                            assert (X2 = X4);
                            [ eapply cPairInj1; eapply cPairInj2; apply H
                            | assert (X3 = X5);
                              [ eapply cPairInj2; eapply cPairInj2; apply H | 
                                clear H ] ]
                        | H:(cPair ?X1 _ = 
                               codeFormula L codeF codeR ?X2) |- _ =>
                            destruct X2;
                            simpl in H;
                            try
                              match goal with
                              | J:(cPair ?X1 _ = cPair ?X2 _) |- _ =>
                                  cut (X1 = X2);
                                  [ intro I; discriminate I |
                                    eapply cPairInj1; apply J ]
                              end
                        end.
                      rewrite H3.
                      replace f2_1 with f1_1.
                      replace f1_2 with f2_2.
                      replace n3 with n1.
                      replace n2 with n1.
                      exists (FA3 L f1_1 f2_2 n1).
                      simpl in |- *.
                      rewrite <- H4.
                      rewrite <- H8.
                      rewrite <- H5.
                      repeat rewrite cPairProjections.
                      rewrite H2.
                      apply cPairProjections.
                      transitivity (cdr (cdr
                                                (cdr (cdr n))));
                        [ symmetry  in |- *; assumption | assumption ].
                      transitivity (cdr (cdr (cdr 
                                                          (cdr n))));
                        [ symmetry  in |- *; assumption | assumption ].
                      apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
                      transitivity 
                        (car (cdr (cdr (cdr n))));
                        [ symmetry  in |- *; assumption | assumption ].
                      apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
                      transitivity (car (cdr (cdr n)));
                        [ symmetry  in |- *; assumption | assumption ].
                      elim H0.
                      unfold charFunction in |- *.
                      rewrite nat_eqb_false.
                      reflexivity.
                      assumption.
                      destruct n1.
                      simpl in H0.
                      unfold checkPrfEQ1 in H0.
                      clear A.
                      exists (nil (A:=Formula)).
                      rewrite <- H3 in H0.
                      induction
                        (eq_nat_dec
                           (codeFormula L codeF codeR 
                              (equal (var 0) (var 0)))
                           (codeFormula L codeF codeR x)).
                      rewrite H3.
                      replace x with (@equal L (var 0) 
                                        (var 0)).
                      exists (EQ1 L).
                      simpl in |- *.
                      induction (eq_nat_dec (cdr (cdr n)) 0).
                      rewrite a0 in H2.
                      rewrite H2.
                      apply cPairProjections.
                      elim H0.
                      unfold charFunction in |- *.
                      rewrite nat_eqb_false.
                      reflexivity.
                      rewrite cPairProjections2.
                      assumption.
                      apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
                      assumption.
                      elim H0.
                      unfold charFunction in |- *.
                      rewrite
                        (nat_eqb_false
                           (codeFormula L codeF codeR 
                              (equal (var 0) (var 0)))).
                  
                      rewrite Nat.mul_comm.
                      reflexivity.
                      rewrite cPairProjections1.
                      assumption.
                      destruct n1.
                      simpl in H0.
                      unfold checkPrfEQ2 in H0.
                      clear A.
                      exists (nil (A:=Formula)).
                      rewrite <- H3 in H0.
                      induction
                        (eq_nat_dec
                           (codeFormula L codeF codeR
                              (impH (equal (var 0) 
                                             (var 1))
                                 (equal (var 1) (var 0))))
                           (codeFormula L codeF codeR x)).
                      rewrite H3.
                      replace x with
                        (@impH L (equal (var 0) (var 1))
                           (equal (var 1) (var 0))).
                      exists (EQ2 L).
                      simpl in |- *.
                      induction (eq_nat_dec (cdr (cdr n)) 0).
                      rewrite a0 in H2.
                      rewrite H2.
                      apply cPairProjections.
                      elim H0.
                      unfold charFunction in |- *.
                      rewrite nat_eqb_false.
                      reflexivity.
                      rewrite cPairProjections2.
                      assumption.
                      apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
                      assumption.
                      elim H0.
                      unfold charFunction in |- *.
                      rewrite
                        (nat_eqb_false
                           (codeFormula L codeF codeR
                              (impH (equal (var 0) (var 1))
                                 (equal (var 1) (var 0))))).
                      
                      rewrite Nat.mul_comm.
                      reflexivity.
                      rewrite cPairProjections1.
                      assumption.
                      (* Checking the result is too long in v8
Simpl in H0.
                       *)
                      (* Replacement for v8 *)
                      repeat rewrite <- pred_Sn in H0.
                      assert
                        (H4 : forall n2 p q : nat, switchPR (S n2) p q = p).
                      simple destruct n2; trivial.
                      repeat rewrite H4 in H0.
                      clear H4.
                      destruct n1.
                      simpl in H0.
                      unfold checkPrfEQ3 in H0.
                      clear A.
                      exists (nil (A:=Formula)).
                      rewrite <- H3 in H0.
                      induction
                        (eq_nat_dec
                           (codeFormula L codeF codeR
                              (impH (equal (var 0) (var 1))
                                 (impH (equal (var 1) (var 2))
                                    (equal (var 0) (var 2)))))
                           (codeFormula L codeF codeR x)).
                      rewrite H3.
                      replace x with
                        (@impH L (equal (var 0) (var 1))
                           (impH (equal (var 1) (var 2))
                              (equal (var 0) (var 2)))).
                      exists (EQ3 L).
                      simpl in |- *.
                      rewrite cPairProjections2 in H0.
                      rewrite cPairProjections1 in H0.
                      induction (eq_nat_dec (cdr (cdr n)) 0).
                      rewrite a0 in H2.
                      rewrite H2.
                      apply cPairProjections.
                      elim H0.
                      unfold charFunction in |- *.
                      rewrite nat_eqb_false.
                      reflexivity.
                      assumption.
                      apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
                      assumption.
                      elim H0.
                      unfold charFunction in |- *.
                      rewrite
                        (nat_eqb_false
                           (codeFormula L codeF codeR
                              (impH (equal (var 0) 
                                             (var 1))
                                 (impH (equal (var 1) 
                                                (var 2))
                                    (equal (var 0) 
                                       (var 2))))))
                      .
                      rewrite Nat.mul_comm.
                      reflexivity.
                      rewrite cPairProjections1.
                      assumption.
                      destruct n1.
                      simpl in H0.
                      unfold checkPrfEQ4 in H0.
                      clear A.
                      repeat rewrite cPairProjections2 in H0.
                      repeat rewrite cPairProjections1 in H0.
                      exists (nil (A:=Formula)).
                      rewrite <- H3 in H0.
                      assert (codeArityR (cdr (cdr n)) <> 0).
                      unfold notZero in H0.
                      unfold not in |- *; intros.
                      rewrite H4 in H0.
                      apply H0.
                      reflexivity.
                      induction (codeArityRIsCorrect2 _ H4).
                      rewrite <- H5 in H0.
                      rewrite codeArityRIsCorrect1 in H0.
                      simpl in H0.
                      induction (codeNVarsCorrect (arityR L x0)).
                      rewrite H6 in H0.
                      rewrite H7 in H0.
                      clear H6 H7.
                      assert
                        (codeIff
                           (cPair (S (S (S (S (codeR x0)))))
                              (codeTerms L codeF 
                                 (arityR L x0)
                                 (fst (nVars L (arityR L x0)))))
                               (cPair (S (S (S (S (codeR x0)))))
                              (codeTerms L codeF (arityR  L x0)
                                 (snd (nVars L (arityR L x0))))) =
                           codeIff
                             (codeFormula L codeF codeR
                                (atomic x0 (fst 
                                              (nVars L 
                                                 (arityR L x0)))))
                             (codeFormula L codeF codeR
                                (atomic x0 (snd 
                                              (nVars L 
                                                 (arityR L x0)))))).
                      reflexivity.
                      rewrite H6 in H0.
                      clear H6.
                      rewrite codeIffCorrect in H0.
                      assert (AxmEq4 L x0 = x).
                      clear H5.
                      unfold AxmEq4 in |- *.
                      induction (nVars L (arityR L x0)).
                      simpl in |- *.
                      unfold fst, snd in H0.
                      cut
                        ((if Nat.eqb
                               (codeAxmEqHelp (arityR L x0)
                                  (codeFormula L codeF codeR 
                                     (iffH (atomic x0 a) (atomic x0 b))))
                               (codeFormula L codeF codeR x)
                          then 1
                          else 0) + 0 <> 0).
                      { 
                        generalize (iffH (atomic x0 a) (atomic x0 b)).
                        intros f H5.
                        clear H0.
                        clear a b.
                        cut
                          (codeAxmEqHelp (arityR L x0)
                             (codeFormula L codeF codeR f) = 
                             codeFormula L codeF codeR x).
                        { generalize x.
                          clear H5.
                          induction (arityR L x0); 
                            simpl in |- *; intros.
                          apply (codeFormulaInj L codeF codeR codeFInj 
                                   codeRInj).
                          assumption.
                          rename x1 into f0.
                          repeat
                            match goal with
                            | H:(cPair 1 (cPair ?X2 ?X3) = 
                                   cPair 1 (cPair ?X4 ?X5)) |- _ =>
                                assert (X2 = X4);
                                [ eapply cPairInj1; eapply cPairInj2; apply H
                                | assert (X3 = X5);
                                  [ eapply cPairInj2; eapply cPairInj2; 
                                    apply H | clear H ] ]
                            | H:(cPair 0 (cPair ?X2 ?X3) = 
                                   cPair 0 (cPair ?X4 ?X5)) |- _ =>
                                assert (X2 = X4);
                                [ eapply cPairInj1; eapply cPairInj2; apply H
                                | assert (X3 = X5);
                                  [ eapply cPairInj2; eapply cPairInj2; 
                                    apply H | clear H ] ]
                            | H:(cPair ?X1 _ = 
                                   codeFormula L codeF codeR ?X2) |- _ =>
                                destruct X2;
                                simpl in H;
                                try
                                  match goal with
                                  | J:(cPair ?X1 _ = cPair ?X2 _) |- _ =>
                                      cut (X1 = X2);
                                      [ intro I; discriminate I | 
                                        eapply cPairInj1; apply J ]
                                  end
                            end.
                          rewrite (IHn1 f0_2).
                          destruct t.
                          replace n2 with (n1 + n1).
                          destruct t0.
                          replace n3 with (S (n1 + n1)).
                          reflexivity.
                          apply cPairInj2 with 0 0.
                          apply H7.
                          elim O_S with (codeF f0).
                          apply cPairInj1 with 
                            (S (n1 + n1)) 
                            (codeTerms L codeF (arityF L f0) t).
                          apply H7.
                          apply cPairInj2 with 0 0.
                          apply H0.
                          elim O_S with (codeF f0).
                          apply cPairInj1 with 
                            (n1 + n1) 
                            (codeTerms L codeF (arityF L f0) t).
                          apply H0.
                          assumption.
                        } 
                        induction
                          (eq_nat_dec
                             (codeAxmEqHelp (arityR L x0)
                                (codeFormula L codeF codeR f))
                             (codeFormula L codeF codeR x)).
                        assumption.
                        elim H5.
                        rewrite nat_eqb_false.
                        reflexivity.
                        assumption.
                      } 
                      assumption.
                      rewrite H3.
                      rewrite <- H6.
                      exists (EQ4 L x0).
                      simpl in |- *.
                      rewrite H5.
                      rewrite H2.
                      apply cPairProjections.
                      destruct n1.
                      simpl in H0.
                      unfold checkPrfEQ5 in H0.
                      clear A.
                      repeat rewrite cPairProjections2 in H0.
                      repeat rewrite cPairProjections1 in H0.
                      exists (nil (A:=Formula)).
                      rewrite <- H3 in H0.
                      assert (codeArityF (cdr (cdr n)) <> 0).
                      unfold notZero in H0.
                      unfold not in |- *; intros.
                      rewrite H4 in H0.
                      apply H0.
                      reflexivity.
                      induction (codeArityFIsCorrect2 _ H4).
                      rewrite <- H5 in H0.
                      rewrite codeArityFIsCorrect1 in H0.
                      simpl in H0.
                      induction (codeNVarsCorrect (arityF L x0)).
                      rewrite H6 in H0.
                      rewrite H7 in H0.
                      clear H6 H7.
                      assert
                        (cPair 0
                           (cPair
                              (cPair (S (codeF x0))
                                 (codeTerms L codeF 
                                    (arityF L x0)
                                    (fst (nVars L 
                                            (arityF L x0)))))
                              (cPair (S (codeF x0))
                                 (codeTerms L codeF 
                                    (arityF L x0)
                                    (snd (nVars L 
                                            (arityF L x0)))))) =
                           codeFormula L codeF codeR
                             (equal (apply x0 
                                       (fst (nVars L (arityF L x0))))
                                (apply x0 (snd (nVars L (arityF L x0)))))).
                      reflexivity.
                      rewrite H6 in H0.
                      clear H6.
                      assert (AxmEq5 L x0 = x).
                      clear H5.
                      unfold AxmEq5 in |- *.
                      induction (nVars L (arityF L x0)).
                      simpl in |- *.
                      unfold fst, snd in H0.
                      cut
                        ((if Nat.eqb
                               (codeAxmEqHelp (arityF L x0)
                                  (codeFormula L codeF codeR 
                                     (equal (apply x0 a) (apply x0 b))))
                               (codeFormula L codeF codeR x)
                          then 1 else 0) + 0 <> 0).
                      generalize (equal (apply x0 a) (apply x0 b)).
                      intros.
                      clear H0.
                      clear a b.
                      cut
                        (codeAxmEqHelp (arityF L x0)
                           (codeFormula L codeF codeR f) = 
                           codeFormula L codeF codeR x).
                      generalize x.
                      clear H5.
                      induction (arityF L x0); 
                        simpl in |- *; intros.
                      apply (codeFormulaInj L codeF codeR codeFInj codeRInj).
                      assumption.
                      repeat
                        match goal with
                        | H:(cPair 1 (cPair ?X2 ?X3) = 
                               cPair 1 (cPair ?X4 ?X5)) |- _ =>
                            assert (X2 = X4);
                            [ eapply cPairInj1; eapply cPairInj2; apply H
                            | assert (X3 = X5);
                              [ eapply cPairInj2; eapply cPairInj2; apply H | 
                                clear H ] ]
                        | H:(cPair 0 (cPair ?X2 ?X3) =
                               cPair 0 (cPair ?X4 ?X5)) |- _ =>
                            assert (X2 = X4);
                            [ eapply cPairInj1; eapply cPairInj2; apply H
                            | assert (X3 = X5);
                              [ eapply cPairInj2; eapply cPairInj2; apply H | 
                                clear H ] ]
                        | H:(cPair ?X1 _ = 
                               codeFormula L codeF codeR ?X2) |- _ =>
                            destruct X2;
                            simpl in H;
                            try
                              match goal with
                              | J:(cPair ?X1 _ = cPair ?X2 _) |- _ =>
                                  cut (X1 = X2);
                                  [ intro I; discriminate I | 
                                    eapply cPairInj1; apply J ]
                              end
                        end.
                      rewrite (IHn1 x1_2).
                      destruct t.
                      replace n2 with (n1 + n1).
                      destruct t0.
                      replace n3 with (S (n1 + n1)).
                      reflexivity.
                      apply cPairInj2 with 0 0.
                      apply H7.
                      elim O_S with (codeF f0).
                      apply
                        cPairInj1
                        with (S (n1 + n1)) 
                             (codeTerms L codeF 
                                (arityF L f0) t).
                      apply H7.
                      apply cPairInj2 with 0 0.
                      apply H0.
                      elim O_S with (codeF f0).
                      apply
                        cPairInj1
                        with (n1 + n1) 
                             (codeTerms L codeF (arityF L f0) t).
                      apply H0.
                      assumption.
                      induction
                        (eq_nat_dec
                           (codeAxmEqHelp (arityF L x0)
                              (codeFormula L codeF codeR f)) 
                           (codeFormula L codeF codeR x)).
                      assumption.
                      elim H5.
                      rewrite nat_eqb_false.
                      reflexivity.
                      assumption.
                      assumption.
                      rewrite H3.
                      rewrite <- H6.
                      exists (EQ5 L x0).
                      simpl in |- *.
                      rewrite H5.
                      rewrite H2.
                      apply cPairProjections.
                      elim H0.
                      simpl in |- *.
                      reflexivity.
  }
  intros n m H0.
  assert
    (H1: exists f : Formula,
        (exists l : list Formula,
            (exists p : Prf l f,
                cPair (codeFormula L codeF codeR f) 
                  (codePrf L codeF codeR l f p) =
                    cPair n m))).
  { eapply H.
    apply Nat.lt_succ_diag_r.
    rewrite cPairProjections1.
    rewrite cPairProjections2.
    assumption.
  } 
  decompose record H1.
  exists x; split.
  -  eapply cPairInj1.
     apply H2.
  - exists x0, x1; eapply cPairInj2; apply H2.
Qed.

End Check_Proof.

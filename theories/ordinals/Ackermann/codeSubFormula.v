(** codeSubFormula:

    Original file by Russel O'Connor

*)

From Coq Require Import Arith Vector Lia.
From  Coq Require Vector.

Require Import primRec  cPair folProp code extEqualNat.

Require Import codeSubTerm codeFreeVar Compat815.

Import LispAbbreviations. 

From LibHyps Require Export LibHyps.
From hydras Require Export MoreLibHyps NewNotations.

Section Code_Substitute_Formula.

Generalizable All Variables. 
Variable L : Language.
Context `(cL : Lcode L cf cr).


Notation Formula := (Formula L) (only parsing).
Notation Formulas := (Formulas L) (only parsing).
Notation System := (System L) (only parsing).
Notation Term := (Term L) (only parsing).
Notation Terms := (Terms L) (only parsing).
Let codeFormula := codeFormula (cl := cL).
Let codeTerm := codeTerm  (cl := cL).



Definition codeNewVar (l : nat) : nat :=
  evalStrongRec 0
    (fun n Hrecs : nat =>
     switchPR n
       (Nat.max (S (car (pred n)))
          (codeNth (n - S (cdr (pred n))) Hrecs)) 0) l.

Lemma codeNewVarCorrect (l : list nat) : 
  codeNewVar (codeList l) = newVar l.
Proof.
  unfold codeNewVar, newVar.
  set (f :=
  fun n Hrecs : nat =>
    switchPR n
    (Nat.max (S (car (pred n))) (codeNth (n - S (cdr (pred n))) Hrecs))
    0).
  induction l as [| a l Hrecl].
  - simpl; unfold evalStrongRec; simpl; now rewrite cPairProjections1.
  - unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
    rewrite computeEvalStrongRecHelp; unfold compose2. 
    unfold f at 1; rewrite evalStrongRecHelp1.
    + simpl; repeat rewrite cPairProjections1.
      rewrite <- Hrecl; repeat rewrite cPairProjections2.
      reflexivity.
    + simpl; repeat rewrite cPairProjections2.
      apply  Nat.lt_succ_r,  cPairLe2.
Qed.

Lemma codeNewVarIsPR : isPR 1 codeNewVar.
Proof.
  unfold codeNewVar; apply  (evalStrongRecIsPR 0) with
    (f := fun n Hrecs : nat =>
            switchPR n
              (Nat.max (S (car (pred n)))
                 (codeNth (n - S (cdr (pred n))) Hrecs)) 0).
  apply
    compose2_3IsPR
    with
    (g := switchPR)
    (f1 := fun n Hrecs : nat => n)
    (f2 := fun n Hrecs : nat =>
             Nat.max (S (car (pred n)))
               (codeNth (n - S (cdr (pred n))) Hrecs))
    (f3 := fun n Hrecs : nat => 0).
  - apply pi1_2IsPR.
  - apply compose2_2IsPR with
      (h := Nat.max)
      (f := fun n Hrecs : nat => S (car (pred n)))
      (g := fun n Hrecs : nat => codeNth (n - S (cdr (pred n))) Hrecs).
    + apply filter10IsPR with (g := fun n : nat => S (car (pred n))).
      apply compose1_1IsPR with (g := S) 
                                (f := fun n : nat => car (pred n)).
      * apply compose1_1IsPR.
        -- apply predIsPR.
        -- apply cPairPi1IsPR.
      * apply succIsPR.
    + apply compose2_2IsPR with
        (h := codeNth)
        (f := fun n Hrecs : nat => n - S (cdr (pred n)))
        (g := fun n Hrecs : nat => Hrecs).
      * apply filter10IsPR with (g := fun n : nat => n - S (cdr (pred n))).
        apply compose1_2IsPR with
          (g := minus)
          (f := fun n : nat => n)
          (f' := fun n : nat => S (cdr (pred n))).
        -- apply idIsPR.
        -- apply compose1_1IsPR with 
             (g := S) (f := fun n : nat => cdr (pred n)).
           ++ apply compose1_1IsPR.
              ** apply predIsPR.
              ** apply cPairPi2IsPR.
           ++ apply succIsPR.
        -- apply minusIsPR.
      * apply pi2_2IsPR.
      * apply codeNthIsPR.
    + apply maxIsPR.
  - apply filter10IsPR with (g := fun _ : nat => 0).
    apply const1_NIsPR.
  - apply switchIsPR.
Qed.


(*Trace has form
 ((v,s, formula_input), formula_output, [subTrace1], [subTrace2])*)

Definition checkSubFormulaTrace : nat -> nat :=
  evalStrongRec 0
    (fun trace recs : nat =>
     let v := cTriplePi1 (cTriplePi1 trace) in
     let s := cTriplePi2 (cTriplePi1 trace) in
     let input := cTriplePi3 (cTriplePi1 trace) in
     let output := cTriplePi2 trace in
     let rest := cTriplePi3 trace in
     let type := cPairPi1 input in
     switchPR type
       (switchPR (pred type)
          (switchPR (pred (pred type))
             (switchPR (pred (pred (pred type)))
                (charFunction 2 Nat.eqb output
                   (cPair type (codeSubTerms (cdr input) v s)))
                (switchPR
                   (charFunction 2 Nat.eqb v (car (cdr input)))
                   (charFunction 2 Nat.eqb input output)
                   (switchPR
                      (codeIn (car (cdr input)) (codeFreeVarTerm s))
                      (let nv :=
                         codeNewVar
                           (S
                              (cPair v
                                 (codeApp (codeFreeVarTerm s)
                                    (codeFreeVarFormula
                                       (cdr (cdr input)))))) in
                       charFunction 0
                         (Nat.eqb output
                            (cPair 3 (cPair nv (cTriplePi2 (cdr rest)))) &&
                          (Nat.eqb (cTriple v s (cTriplePi2 (car rest)))
                             (cTriplePi1 (cdr rest)) &&
                           Nat.eqb
                             (cTriple (car (cdr input))
                                (cPair 0 nv) (cdr (cdr input)))
                             (cTriplePi1 (car rest)))) *
                       (codeNth (trace - S (car rest)) recs *
                        codeNth (trace - S (cdr rest)) recs))
                      (charFunction 0
                         (Nat.eqb output
                            (cPair 3
                               (cPair (car (cdr input))
                                  (cTriplePi2 rest))) &&
                          Nat.eqb (cTriple v s (cdr (cdr input)))
                            (cTriplePi1 rest)) *
                       codeNth (trace - S rest) recs))))
             (charFunction 0
                (Nat.eqb output (cPair 2 (cTriplePi2 rest)) &&
                 Nat.eqb (cTriple v s (cdr input)) (cTriplePi1 rest)) *
              codeNth (trace - S rest) recs))
          (charFunction 0
             (Nat.eqb output
                (cPair 1
                   (cPair (cTriplePi2 (car rest))
                      (cTriplePi2 (cdr rest)))) &&
              (Nat.eqb (cTriple v s (car (cdr input)))
                 (cTriplePi1 (car rest)) &&
               Nat.eqb (cTriple v s (cdr (cdr input)))
                 (cTriplePi1 (cdr rest)))) *
           (codeNth (trace - S (car rest)) recs *
            codeNth (trace - S (cdr rest)) recs)))
       (charFunction 2 Nat.eqb output
          (cPair 0
             (cPair (codeSubTerm (car (cdr input)) v s)
                (codeSubTerm (cdr (cdr input)) v s))))).

Definition makeTraceImp (f1 : fol.Formula L)
  (f1rec : nat * fol.Term L -> nat) (f2 : fol.Formula L)
  (f2rec : nat * fol.Term L -> nat) (p : nat * fol.Term L) : nat :=
  let v := fst p in
  let s := snd p in
  cTriple (cTriple v (codeTerm s) (codeFormula (impH f1 f2)))
    (codeFormula (substF (impH f1 f2) v s))
    (cPair (f1rec p) (f2rec p)).

Definition makeTraceNot 
  (f : fol.Formula L) (frec : nat * fol.Term L -> nat)
  (p : nat * fol.Term L) : nat :=
  let v := fst p in
  let s := snd p in
  cTriple (cTriple v (codeTerm s) (codeFormula (notH f)))
    (codeFormula (substF (notH f) v s)) 
    (frec p).

Definition makeTraceForall (n : nat) (f : fol.Formula L)
  (rec : forall b : fol.Formula L,
      lt_depth L b (forallH n f) -> nat * fol.Term L -> nat)
  (p : nat * fol.Term L) : nat.
Proof. 
  set (v := fst p); set (s := snd p).
  destruct (eq_nat_dec n v) as [a | b].
  - exact
      (cTriple (cTriple v (codeTerm s) (codeFormula (forallH n f)))
         (codeFormula (substF (forallH n f) v s)) 0).
  - assert (H: lt_depth L f (forallH v f)) by apply depthForall.
    destruct (In_dec eq_nat_dec n (freeVarT s)) as [a | b0].
    + set (nv := newVar (v :: freeVarT s ++ freeVarF f)).
      assert (H0: lt_depth L (substF f n (var nv)) 
                    (forallH v f)).
      { apply eqDepth with f.
        symmetry  in |- *.
        apply subFormulaDepth.
        apply H.
      }
      exact
        (cTriple (cTriple v (codeTerm s) (codeFormula (forallH n f)))
           (codeFormula (substF (forallH n f) v s))
           (cPair (rec f H (n, var nv))
              (rec (substF f n (var nv)) H0 p))).
    + exact
        (cTriple (cTriple v (codeTerm s) (codeFormula (forallH n f)))
           (codeFormula (substF (forallH n f) v s)) 
           (rec f H p)).
Defined.

Definition makeTrace : fol.Formula L -> nat * fol.Term L -> nat :=
  Formula_depth_rec2 L (fun _ : fol.Formula L => nat * fol.Term L -> nat)
    (fun (t t0 : fol.Term L) (p : nat * fol.Term L) =>
     let v := fst p in
     let s := snd p in
     cTriple (cTriple v (codeTerm s) (codeFormula (equal t t0)))
       (codeFormula (substF (equal t t0) v s)) 0)
    (fun (r : Relations L) t (p : nat * fol.Term L) =>
     let v := fst p in
     let s := snd p in
     cTriple (cTriple v (codeTerm s) (codeFormula (atomic r t)))
       (codeFormula (substF (atomic r t) v s)) 0) 
    makeTraceImp
    makeTraceNot makeTraceForall.

Lemma makeTraceImpNice (f2 g : fol.Formula L) 
  (z1 z2 : nat * fol.Term L -> nat):
  (forall q : nat * fol.Term L, z1 q = z2 q) ->
  forall z3 z4 : nat * fol.Term L -> nat,
    (forall q : nat * fol.Term L, z3 q = z4 q) ->
    forall q : nat * fol.Term L,
      makeTraceImp f2 z1 g z3 q = makeTraceImp f2 z2 g z4 q.
Proof.
  intros H z3 z4 H0 q; unfold makeTraceImp.
  rewrite H, H0; reflexivity.
Qed.

Lemma makeTraceNotNice (f2 : fol.Formula L) 
  (z1 z2 : nat * fol.Term L -> nat) :
 (forall q : nat * fol.Term L, z1 q = z2 q) ->
 forall q : nat * fol.Term L, 
   makeTraceNot f2 z1 q = makeTraceNot f2 z2 q.
Proof.
  intros H q; unfold makeTraceNot; now rewrite H.
Qed.

Lemma makeTraceForallNice 
  (v0 : nat) (a : fol.Formula L)
  (z1 z2 : forall b : fol.Formula L,
      lt_depth L b (forallH v0 a) -> nat * fol.Term L -> nat):
  (forall (b : fol.Formula L) (q : lt_depth L b (forallH v0 a))
          (r : nat * fol.Term L), z1 b q r = z2 b q r) ->
  forall q : nat * fol.Term L,
    makeTraceForall v0 a z1 q = makeTraceForall v0 a z2 q.
Proof.
  intros H q; unfold makeTraceForall; now repeat rewrite H.
Qed.

Remark makeTrace1 (f : fol.Formula L) (v : nat) (s : fol.Term L):
 cTriplePi1 (makeTrace f (v, s)) = cTriple v (codeTerm s) (codeFormula f).
Proof.
  induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
    unfold makeTrace, makeTraceImp, makeTraceNot, Formula_depth_rec2,
    Formula_depth_rec in |- *; simpl in |- *;
    try (rewrite cTripleProj1; reflexivity).
  unfold makeTraceForall;
    destruct  (eq_nat_dec n (fst (v, s))) as [a| b]; simpl.
  - rewrite cTripleProj1; reflexivity.
  - destruct (In_dec eq_nat_dec n (freeVarT s)); simpl;
      rewrite cTripleProj1; reflexivity.
Qed.

Remark makeTrace2 (f : fol.Formula L) (v : nat) (s : fol.Term L):
 cTriplePi2 (makeTrace f (v, s)) = codeFormula (substF f v s).
Proof.
  induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
    unfold makeTrace, makeTraceImp, makeTraceNot, Formula_depth_rec2,
    Formula_depth_rec in |- *; simpl in |- *;
    try (rewrite cTripleProj2; reflexivity).
  unfold makeTraceForall; destruct (eq_nat_dec n (fst (v, s))); simpl.
  - rewrite cTripleProj2; reflexivity.
  - destruct  (In_dec eq_nat_dec n (freeVarT s)); simpl;
      rewrite cTripleProj2; reflexivity.
Qed.

Lemma makeTraceCorrect :
 forall (f : fol.Formula L) (v : nat) (s : fol.Term L),
 checkSubFormulaTrace (makeTrace f (v, s)) = 1.
Proof.
intro f; unfold checkSubFormulaTrace;
  set
    (A :=
       fun trace recs : nat =>
         switchPR (car (cTriplePi3 (cTriplePi1 trace)))
           (switchPR (pred (car (cTriplePi3 (cTriplePi1 trace))))
              (switchPR (pred (pred (car (cTriplePi3 (cTriplePi1 trace)))))
                 (switchPR
                    (pred (pred (pred (car (cTriplePi3 (cTriplePi1 trace))))))
                    (charFunction 2 Nat.eqb (cTriplePi2 trace)
                       (cPair (car (cTriplePi3 (cTriplePi1 trace)))
                          (codeSubTerms (cdr (cTriplePi3 (cTriplePi1 trace)))
                             (cTriplePi1 (cTriplePi1 trace))
                             (cTriplePi2 (cTriplePi1 trace)))))
                    (switchPR
                       (charFunction 2 Nat.eqb (cTriplePi1 (cTriplePi1 trace))
                          (car (cdr (cTriplePi3 (cTriplePi1 trace)))))
                       (charFunction 2 Nat.eqb (cTriplePi3 (cTriplePi1 trace))
                          (cTriplePi2 trace))
                       (switchPR
                          (codeIn
                             (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                             (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace))))
                          (charFunction 0
                             (Nat.eqb (cTriplePi2 trace)
                                (cPair 3
                                   (cPair
                                      (codeNewVar
                                         (S
                                            (cPair 
                                               (cTriplePi1 (cTriplePi1 trace))
                                               (codeApp
                                                  (codeFreeVarTerm
                                                     (cTriplePi2 
                                                        (cTriplePi1 trace)))
                                                  (codeFreeVarFormula
                                                     (cdr
                                                        (cdr
                                                           (cTriplePi3
                                                              (cTriplePi1 trace)))))))))
                                      (cTriplePi2 (cdr (cTriplePi3 trace))))) &&
                       (Nat.eqb
                          (cTriple (cTriplePi1 (cTriplePi1 trace))
                             (cTriplePi2 (cTriplePi1 trace))
                             (cTriplePi2 (car (cTriplePi3 trace))))
                          (cTriplePi1 (cdr (cTriplePi3 trace))) &&
                        Nat.eqb
                          (cTriple
                             (car
                                (cdr (cTriplePi3 (cTriplePi1 trace))))
                             (cPair 0
                                (codeNewVar
                                   (S
                                      (cPair (cTriplePi1 (cTriplePi1 trace))
                                         (codeApp
                                            (codeFreeVarTerm
                                               (cTriplePi2 (cTriplePi1 trace)))
                                            (codeFreeVarFormula
                                               (cdr
                                                  (cdr
                                                  (cTriplePi3
                                                  (cTriplePi1 trace))))))))))
                             (cdr
                                (cdr (cTriplePi3 (cTriplePi1 trace)))))
                          (cTriplePi1 (car (cTriplePi3 trace))))) *
                    (codeNth (trace - S (car (cTriplePi3 trace))) recs *
                     codeNth (trace - S (cdr (cTriplePi3 trace))) recs))
                   (charFunction 0
                      (Nat.eqb (cTriplePi2 trace)
                         (cPair 3
                            (cPair
                               (car
                                  (cdr (cTriplePi3 (cTriplePi1 trace))))
                               (cTriplePi2 (cTriplePi3 trace)))) &&
                       Nat.eqb
                         (cTriple (cTriplePi1 (cTriplePi1 trace))
                            (cTriplePi2 (cTriplePi1 trace))
                            (cdr
                               (cdr (cTriplePi3 (cTriplePi1 trace)))))
                         (cTriplePi1 (cTriplePi3 trace))) *
                    codeNth (trace - S (cTriplePi3 trace)) recs))))
          (charFunction 0
             (Nat.eqb (cTriplePi2 trace)
                (cPair 2 (cTriplePi2 (cTriplePi3 trace))) &&
              Nat.eqb
                (cTriple (cTriplePi1 (cTriplePi1 trace))
                   (cTriplePi2 (cTriplePi1 trace))
                   (cdr (cTriplePi3 (cTriplePi1 trace))))
                (cTriplePi1 (cTriplePi3 trace))) *
           codeNth (trace - S (cTriplePi3 trace)) recs))
       (charFunction 0
          (Nat.eqb (cTriplePi2 trace)
             (cPair 1
                (cPair (cTriplePi2 (car (cTriplePi3 trace)))
                   (cTriplePi2 (cdr (cTriplePi3 trace))))) &&
           (Nat.eqb
              (cTriple (cTriplePi1 (cTriplePi1 trace))
                 (cTriplePi2 (cTriplePi1 trace))
                 (car (cdr (cTriplePi3 (cTriplePi1 trace)))))
              (cTriplePi1 (car (cTriplePi3 trace))) &&
            Nat.eqb
              (cTriple (cTriplePi1 (cTriplePi1 trace))
                 (cTriplePi2 (cTriplePi1 trace))
                 (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
              (cTriplePi1 (cdr (cTriplePi3 trace))))) *
        (codeNth (trace - S (car (cTriplePi3 trace))) recs *
         codeNth (trace - S (cdr (cTriplePi3 trace))) recs)))
    (charFunction 2 Nat.eqb (cTriplePi2 trace)
       (cPair 0
          (cPair
             (codeSubTerm
                (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                (cTriplePi1 (cTriplePi1 trace))
                (cTriplePi2 (cTriplePi1 trace)))
             (codeSubTerm
                (cdr (cdr (cTriplePi3 (cTriplePi1 trace))))
                (cTriplePi1 (cTriplePi1 trace))
                (cTriplePi2 (cTriplePi1 trace))))))).
elim f using Formula_depth_ind2. 
- intros t t0 v s; 
    unfold makeTrace, Formula_depth_rec2, Formula_depth_rec; simpl.
  unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
  rewrite computeEvalStrongRecHelp.
  unfold compose2, evalComposeFunc, evalOneParamList, evalList; simpl.
  rewrite cPairProjections1.
  unfold A at 1 in |- *;
    repeat first
      [ rewrite cTripleProj1
      | rewrite cTripleProj2
      | rewrite cTripleProj3
      | rewrite cPairProjections1
      | rewrite cPairProjections2 ].
  simpl; unfold codeTerm; repeat rewrite codeSubTermCorrect.
  now rewrite  Nat.eqb_refl. 
- intros r t v s; unfold makeTrace, Formula_depth_rec2, Formula_depth_rec; simpl.
  unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList in |- *.
  rewrite computeEvalStrongRecHelp.
  unfold compose2, evalComposeFunc, evalOneParamList, evalList.
  simpl; rewrite cPairProjections1.
  unfold A at 1 in |- *;
    repeat first
      [ rewrite cTripleProj1
      | rewrite cTripleProj2
      | rewrite cTripleProj3
      | rewrite cPairProjections1
      | rewrite cPairProjections2 ].
  unfold codeTerm; rewrite codeSubTermsCorrect; simpl.
  now rewrite Nat.eqb_refl.
- intros f0 H f1 H0 v s. replace (makeTrace (impH f0 f1) (v, s)) with
    (cTriple (cTriple v (codeTerm s) (codeFormula (impH f0 f1)))
       (codeFormula (substF (impH f0 f1) v s))
       (cPair (makeTrace f0 (v, s)) (makeTrace f1 (v, s)))).
  + unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
    rewrite computeEvalStrongRecHelp.
    unfold compose2, evalComposeFunc, evalOneParamList, evalList; simpl.
    rewrite cPairProjections1.
    unfold A at 1 in |- *;
      repeat first
        [ rewrite cTripleProj1
        | rewrite cTripleProj2
        | rewrite cTripleProj3
        | rewrite cPairProjections1
        | rewrite cPairProjections2 ].
    rewrite evalStrongRecHelp1 with (m := makeTrace f0 (v, s)).
    * rewrite evalStrongRecHelp1 with (m := makeTrace f1 (v, s)).
      --  simpl; repeat rewrite makeTrace1; repeat rewrite makeTrace2.
          rewrite subFormulaImp, H, H0. 
          simpl; repeat rewrite Nat.eqb_refl; reflexivity.
      --  apply Nat.le_lt_trans with 
             (cPair (makeTrace f0 (v, s)) (makeTrace f1 (v, s))).
          ++ apply cPairLe2.
          ++  unfold cTriple; apply Nat.le_lt_trans
                with
                (cPair (codeFormula (substF (impH f0 f1) v s))
                   (cPair (makeTrace f0 (v, s)) (makeTrace f1 (v, s)))).
              apply cPairLe2.
              apply Nat.lt_le_trans  with
                (cPair 1
                   (cPair (codeFormula (substF (impH f0 f1) v s))
                      (cPair (makeTrace f0 (v, s)) (makeTrace f1 (v, s))))).
              ** apply cPairLt2.
              ** apply cPairLe3.
                 apply Nat.le_trans with
                   (cPair 1 (cPair (codeFormula f0) (codeFormula f1))).
                 apply cPairLe1.
                 apply Nat.le_trans with
                   (cPair (codeTerm s) (cPair 1 (cPair (codeFormula f0) 
                                                   (codeFormula f1)))).
                 apply cPairLe2.
                 apply cPairLe2.
                 apply le_n.
    * apply Nat.le_lt_trans with 
        (cPair (makeTrace f0 (v, s)) (makeTrace f1 (v, s))).
      --  apply cPairLe1.
      --   unfold cTriple;  apply Nat.le_lt_trans with
             (cPair (codeFormula (substF (impH f0 f1) v s))
                (cPair (makeTrace f0 (v, s)) (makeTrace f1 (v, s)))).
           ++ apply cPairLe2.
           ++ apply Nat.lt_le_trans with
                (cPair 1
                   (cPair (codeFormula (substF (impH f0 f1) v s))
                      (cPair (makeTrace f0 (v, s)) (makeTrace f1 (v, s))))).
              **  apply cPairLt2.
              **  apply cPairLe3.
                  apply Nat.le_trans with
                    (cPair 1 (cPair (codeFormula f0) (codeFormula f1))).
                  apply cPairLe1.
                  apply Nat.le_trans with
                    (cPair (codeTerm s) 
                       (cPair 1 (cPair (codeFormula f0) (codeFormula f1)))).
                  apply cPairLe2.
                  apply cPairLe2.
                  apply le_n.
  + symmetry;
    unfold makeTrace; rewrite (Formula_depth_rec2_imp L)
      with
      (Q := 
         fun _ : fol.Formula L =>
           (nat * fol.Term L)%type)
      (P := fun _ : fol.Formula L => nat).
    * unfold makeTraceImp at 1; reflexivity.
    * apply makeTraceImpNice.
    * apply makeTraceNotNice.
    * apply makeTraceForallNice.
- intros f0 H v s; replace (makeTrace (notH f0) (v, s)) with
    (cTriple (cTriple v (codeTerm s) (codeFormula (notH f0)))
       (codeFormula (substF (notH f0) v s)) 
       (makeTrace f0 (v, s))).
  + unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
    rewrite computeEvalStrongRecHelp.
    unfold compose2, evalComposeFunc, evalOneParamList, evalList.
    simpl; rewrite cPairProjections1.
    unfold A at 1 in |- *;
    repeat first
      [ rewrite cTripleProj1
      | rewrite cTripleProj2
      | rewrite cTripleProj3
      | rewrite cPairProjections1
      | rewrite cPairProjections2 ].
    rewrite evalStrongRecHelp1 with (m := makeTrace f0 (v, s)).
    * simpl; repeat rewrite makeTrace1; repeat rewrite makeTrace2.
      rewrite subFormulaNot, H; simpl; repeat rewrite Nat.eqb_refl; reflexivity.
    * apply Nat.le_lt_trans with
         (cPair (codeFormula (substF (notH f0) v s))
            (makeTrace f0 (v, s))).
      -- apply cPairLe2.
      -- apply Nat.lt_le_trans with
           (cPair 2
              (cPair (codeFormula (substF (notH f0) v s))
                 (makeTrace f0 (v, s)))).
         ++ apply cPairLt2.
         ++ unfold cTriple in |- *.
            apply cPairLe3.
            apply Nat.le_trans with (cPair 2 (codeFormula f0)).
            ** apply cPairLe1.
            ** apply Nat.le_trans with 
                 (cPair (codeTerm s) (cPair 2 (codeFormula f0)));
                 apply cPairLe2.
            ** apply le_n.
  +  symmetry; unfold makeTrace.
     rewrite (Formula_depth_rec2_not L)  with
       (Q := 
          fun _ : fol.Formula L =>
            (nat * fol.Term L)%type)
       (P := fun _ : fol.Formula L => nat).
     *  unfold makeTraceNot at 1 in |- *; reflexivity.
     *  apply makeTraceImpNice.
     *  apply makeTraceNotNice.
     *  apply makeTraceForallNice.
- intros v a H v0 s; replace (makeTrace (forallH v a) (v0, s)) 
    with
    (makeTraceForall v a (fun (b : fol.Formula L) _ => makeTrace b) (v0, s)).
  +  unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
     rewrite computeEvalStrongRecHelp.
     unfold compose2, evalComposeFunc, evalOneParamList, evalList;
       simpl.
     rewrite cPairProjections1;  unfold makeTraceForall; simpl.
     rewrite (subFormulaForall L).
     destruct (eq_nat_dec v v0) as [a0 | b].
     * simpl; unfold A at 1;
         repeat first
           [ rewrite cTripleProj1
           | rewrite cTripleProj2
           | rewrite cTripleProj3
           | rewrite cPairProjections1
           | rewrite cPairProjections2 ].
       replace (charFunction 2 Nat.eqb v0 v) with 1.
       -- simpl; rewrite Nat.eqb_refl; reflexivity.
       -- simpl; now rewrite a0, Nat.eqb_refl.
     *   induction (In_dec eq_nat_dec v (freeVarT s)) as [a0 | b0].
         -- simpl; unfold A at 1;
              repeat first
                [ rewrite cTripleProj1
                | rewrite cTripleProj2
                | rewrite cTripleProj3
                | rewrite cPairProjections1
                | rewrite cPairProjections2 ].
            replace (charFunction 2 Nat.eqb v0 v) with 0.
            replace (codeIn v (codeFreeVarTerm (codeTerm s))) with 1.
            ++  rewrite evalStrongRecHelp1 with
                  (m := 
                     makeTrace a
                       (v,
                         var
                           (newVar
                              (v0 :: freeVarT s ++ freeVarF a)))).
                ** rewrite evalStrongRecHelp1 with
                     (m := 
                        makeTrace
                          (substF a v
                             (var
                                (newVar
                                   (v0 :: freeVarT s ++ 
                                      freeVarF a))))
                          (v0, s)).
                   replace
                     (codeNewVar
                        (S
                           (cPair v0
                              (codeApp (codeFreeVarTerm (codeTerm s))
                                 (codeFreeVarFormula (codeFormula a)))))) 
                     with
                     (newVar (v0 :: freeVarT s ++ freeVarF a)).
                   simpl; repeat rewrite makeTrace1.
                   repeat rewrite makeTrace2.
                   repeat rewrite Nat.eqb_refl.
                   repeat rewrite H.
                   reflexivity.
                   eapply eqDepth.
                   symmetry  in |- *.
                   apply subFormulaDepth.
                   apply depthForall.
                   apply depthForall.
                   unfold codeTerm; rewrite codeFreeVarTermCorrect.
                   unfold codeFormula in |- *.
                   rewrite codeFreeVarFormulaCorrect.
                   rewrite codeAppCorrect.
                   rewrite <- codeNewVarCorrect.
                   reflexivity.
                   generalize
                     (makeTrace
                        (substF a v
                           (var (newVar (v0 :: freeVarT s ++ 
                                           freeVarF a)))) 
                        (v0, s))
                       (makeTrace a (v, var (newVar 
                                               (v0 :: freeVarT s ++ 
                                                  freeVarF a))))
                       (cPair (newVar (v0 :: freeVarT s ++ 
                                         freeVarF a))
                          (codeFormula
                             (substF 
                                (substF a v
                                   (var
                                      (newVar (v0 :: freeVarT s ++ 
                                                 freeVarF a)))) v0 s)))
                       (cTriple v0 (codeTerm s) 
                          (cPair 3 (cPair v (codeFormula a)))).
                   intros n n0 n1 n2.
                   apply Nat.le_lt_trans with (cPair n0 n).
                   apply cPairLe2.
                   unfold cTriple in |- *.
                   apply Nat.lt_le_trans with (cPair 3 (cPair n0 n)).
                   apply cPairLt2.
                   apply Nat.le_trans with (cPair (cPair 3 n1) (cPair n0 n)).
                   apply cPairLe3.
                   apply cPairLe1.
                   apply le_n.
                   apply cPairLe2.
                ** generalize
                    (makeTrace
                       (substF a v
                          (var (newVar (v0 :: freeVarT s ++ 
                                          freeVarF a)))) 
                       (v0, s))
                      (makeTrace a (v, var (newVar (v0 :: freeVarT s 
                                                      ++ freeVarF a))))
                      (cPair (newVar (v0 :: freeVarT s ++ 
                                        freeVarF a))
                         (codeFormula
                            (substF 
                               (substF a v
                                  (var
                                     (newVar (v0 :: freeVarT s ++ 
                                                freeVarF a)))) v0 s)))
                      (cTriple v0 (codeTerm s) 
                         (cPair 3 (cPair v (codeFormula a)))).
                   intros n n0 n1 n2.
                   apply Nat.le_lt_trans with (cPair n0 n).
                   apply cPairLe1.
                   unfold cTriple in |- *.
                   apply Nat.lt_le_trans with (cPair 3 (cPair n0 n)).
                   apply cPairLt2.
                   apply Nat.le_trans with (cPair (cPair 3 n1) (cPair n0 n)).
                   apply cPairLe3.
                   apply cPairLe1.
                   apply le_n.
                   apply cPairLe2.
            ++ unfold codeTerm; rewrite codeFreeVarTermCorrect.
               rewrite codeInCorrect.
               induction (In_dec eq_nat_dec v (freeVarT s)) as [a1 | b0].
               **   reflexivity.
               ** elim b0; assumption.
            ++   simpl; rewrite nat_eqb_false.
                 ** reflexivity.
                 ** congruence. 
         --   simpl; unfold A at 1;
                repeat first
                  [ rewrite cTripleProj1
                  | rewrite cTripleProj2
                  | rewrite cTripleProj3
                  | rewrite cPairProjections1
                  | rewrite cPairProjections2 ].
              replace (charFunction 2 Nat.eqb v0 v) with 0.
              ++ replace (codeIn v (codeFreeVarTerm (codeTerm s))) with 0.
                 **  rewrite evalStrongRecHelp1 with 
                       (m := makeTrace a (v0, s)).
                     simpl; repeat rewrite makeTrace1.
                     repeat rewrite makeTrace2.
                     repeat rewrite Nat.eqb_refl.
                     repeat rewrite H.
                     reflexivity.
                     apply depthForall.
                     generalize 
                       (makeTrace a (v0, s))
                         (cPair v (codeFormula (substF a v0 s)))
                         (cTriple v0 (codeTerm s) 
                            (cPair 3 
                               (cPair v (codeFormula a)))).
                     intros n n0 n1.
                     unfold cTriple; apply Nat.lt_le_trans with (cPair 3 n).
                     apply cPairLt2.
                     apply Nat.le_trans with (cPair (cPair 3 n0) n).
                     apply cPairLe3.
                     apply cPairLe1.
                     apply le_n.
                     apply cPairLe2.
                 **  unfold codeTerm in |- *.
                     rewrite codeFreeVarTermCorrect.
                     rewrite codeInCorrect.
                     destruct (In_dec eq_nat_dec v (freeVarT s)) 
                       as [a0 | b1].
                     elim b0; assumption.
                     reflexivity.
              ++  simpl; rewrite nat_eqb_false.
                  ** reflexivity.
                  ** congruence.
  + unfold makeTrace;
      rewrite
        (Formula_depth_rec2_forall L)
      with
      (Q := 
         fun _ : fol.Formula L =>
           (nat * fol.Term L)%type)
      (P := fun _ : fol.Formula L => nat).
    * unfold makeTraceForall at 1; reflexivity.
    * apply makeTraceImpNice.
    * apply makeTraceNotNice.
    * apply makeTraceForallNice.
Qed.

Lemma checkTraceCorrect :
 forall (f : fol.Formula L) (v : nat) (s : fol.Term L) (n m : nat),
 checkSubFormulaTrace (cTriple (cTriple v (codeTerm s) (codeFormula f)) n m) <>
 0 -> codeFormula (substF f v s) = n.
Proof.
  assert (mult_lemma1 : forall a b : nat, a * b <> 0 -> a <> 0 /\ b <> 0)
    by (intros a b; rewrite Nat.eq_mul_0; tauto).
  intro f; unfold checkSubFormulaTrace.
  set
    (A :=
       fun trace recs : nat =>
         switchPR (car (cTriplePi3 (cTriplePi1 trace)))
           (switchPR (pred (car (cTriplePi3 (cTriplePi1 trace))))
              (switchPR (pred (pred (car (cTriplePi3 (cTriplePi1 trace)))))
                 (switchPR
                    (pred (pred (pred (car (cTriplePi3 (cTriplePi1 trace))))))
                    (charFunction 2 Nat.eqb (cTriplePi2 trace)
                       (cPair (car (cTriplePi3 (cTriplePi1 trace)))
                          (codeSubTerms (cdr (cTriplePi3 (cTriplePi1 trace)))
                             (cTriplePi1 (cTriplePi1 trace))
                             (cTriplePi2 (cTriplePi1 trace)))))
                    (switchPR
                       (charFunction 2 Nat.eqb (cTriplePi1 (cTriplePi1 trace))
                          (car (cdr (cTriplePi3 (cTriplePi1 trace)))))
                       (charFunction 2 Nat.eqb (cTriplePi3 (cTriplePi1 trace))
                          (cTriplePi2 trace))
                       (switchPR
                          (codeIn
                             (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                             (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace))))
                          (charFunction 0
                             (Nat.eqb (cTriplePi2 trace)
                                (cPair 3
                                   (cPair
                                      (codeNewVar
                                         (S
                                            (cPair (cTriplePi1 (cTriplePi1 trace))
                                               (codeApp
                                                  (codeFreeVarTerm
                                                     (cTriplePi2 (cTriplePi1 trace)))
                                                  (codeFreeVarFormula
                                                     (cdr
                                                        (cdr
                                                           (cTriplePi3
                                                              (cTriplePi1 trace)))))))))
                                      (cTriplePi2 (cdr (cTriplePi3 trace))))) &&
                                (Nat.eqb
                                   (cTriple (cTriplePi1 (cTriplePi1 trace))
                                      (cTriplePi2 (cTriplePi1 trace))
                                      (cTriplePi2 (car (cTriplePi3 trace))))
                                   (cTriplePi1 (cdr (cTriplePi3 trace))) &&
                                   Nat.eqb
                                     (cTriple
                                        (car
                                           (cdr (cTriplePi3 (cTriplePi1 trace))))
                                        (cPair 0
                                           (codeNewVar
                                              (S
                                                 (cPair (cTriplePi1 (cTriplePi1 trace))
                                                    (codeApp
                                                       (codeFreeVarTerm
                                                          (cTriplePi2 (cTriplePi1 trace)))
                                                       (codeFreeVarFormula
                                                          (cdr
                                                             (cdr
                                                                (cTriplePi3
                                                                   (cTriplePi1 trace))))))))))
                                        (cdr
                                           (cdr (cTriplePi3 (cTriplePi1 trace)))))
                                     (cTriplePi1 (car (cTriplePi3 trace))))) *
                             (codeNth (trace - S (car (cTriplePi3 trace))) recs *
                                codeNth (trace - S (cdr (cTriplePi3 trace))) recs))
                          (charFunction 0
                             (Nat.eqb (cTriplePi2 trace)
                                (cPair 3
                                   (cPair
                                      (car
                                         (cdr (cTriplePi3 (cTriplePi1 trace))))
                                      (cTriplePi2 (cTriplePi3 trace)))) &&
                                Nat.eqb
                                  (cTriple (cTriplePi1 (cTriplePi1 trace))
                                     (cTriplePi2 (cTriplePi1 trace))
                                     (cdr
                                        (cdr (cTriplePi3 (cTriplePi1 trace)))))
                                  (cTriplePi1 (cTriplePi3 trace))) *
                             codeNth (trace - S (cTriplePi3 trace)) recs))))
                 (charFunction 0
                    (Nat.eqb (cTriplePi2 trace)
                       (cPair 2 (cTriplePi2 (cTriplePi3 trace))) &&
                       Nat.eqb
                         (cTriple (cTriplePi1 (cTriplePi1 trace))
                            (cTriplePi2 (cTriplePi1 trace))
                            (cdr (cTriplePi3 (cTriplePi1 trace))))
                         (cTriplePi1 (cTriplePi3 trace))) *
                    codeNth (trace - S (cTriplePi3 trace)) recs))
              (charFunction 0
                 (Nat.eqb (cTriplePi2 trace)
                    (cPair 1
                       (cPair (cTriplePi2 (car (cTriplePi3 trace)))
                          (cTriplePi2 (cdr (cTriplePi3 trace))))) &&
                    (Nat.eqb
                       (cTriple (cTriplePi1 (cTriplePi1 trace))
                          (cTriplePi2 (cTriplePi1 trace))
                          (car (cdr (cTriplePi3 (cTriplePi1 trace)))))
                       (cTriplePi1 (car (cTriplePi3 trace))) &&
                       Nat.eqb
                         (cTriple (cTriplePi1 (cTriplePi1 trace))
                            (cTriplePi2 (cTriplePi1 trace))
                            (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
                         (cTriplePi1 (cdr (cTriplePi3 trace))))) *
                 (codeNth (trace - S (car (cTriplePi3 trace))) recs *
                    codeNth (trace - S (cdr (cTriplePi3 trace))) recs)))
           (charFunction 2 Nat.eqb (cTriplePi2 trace)
              (cPair 0
                 (cPair
                    (codeSubTerm
                       (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                       (cTriplePi1 (cTriplePi1 trace))
                       (cTriplePi2 (cTriplePi1 trace)))
                    (codeSubTerm
                       (cdr (cdr (cTriplePi3 (cTriplePi1 trace))))
                       (cTriplePi1 (cTriplePi1 trace))
                       (cTriplePi2 (cTriplePi1 trace))))))) 
    in *.
elim f using Formula_depth_ind2. 
- intros t t0 v s n m H; unfold evalStrongRec in H.
  unfold evalComposeFunc, evalOneParamList, evalList in H.
  rewrite computeEvalStrongRecHelp in H.
  unfold compose2 in H.
  unfold evalComposeFunc, evalOneParamList, evalList in H.
  simpl in H.
  rewrite cPairProjections1 in H.
  unfold A at 1 in H;
    repeat first
      [ rewrite cTripleProj1 in H
      | rewrite cTripleProj2 in H
      | rewrite cTripleProj3 in H
      | rewrite cPairProjections1 in H
      | rewrite cPairProjections2 in H ].
  simpl in H.
  unfold codeTerm in H.
  repeat rewrite codeSubTermCorrect in H.
  induction
    (eq_nat_dec n
       (cPair 0
          (cPair (code.codeTerm (substT t v s))
             (code.codeTerm  (substT t0 v s))))) as [a | b].
  + rewrite a; reflexivity.
  + rewrite nat_eqb_false in H.
    * elim H; reflexivity.
    * assumption.
- intros r t v s n m H; unfold evalStrongRec in H.
  unfold evalComposeFunc, evalOneParamList, evalList in H.
  rewrite computeEvalStrongRecHelp in H.
  unfold compose2 in H.
  unfold evalComposeFunc, evalOneParamList, evalList in H.
  simpl in H; rewrite cPairProjections1 in H.
  unfold A at 1 in H;
    repeat first
      [ rewrite cTripleProj1 in H
      | rewrite cTripleProj2 in H
      | rewrite cTripleProj3 in H
      | rewrite cPairProjections1 in H
      | rewrite cPairProjections2 in H ].
  simpl in H; unfold codeTerm in H.
  repeat rewrite codeSubTermsCorrect in H.
  destruct  (eq_nat_dec n
               (cPair (S (S (S (S (cr r)))))
                  (codeTerms  (substTs t v s)))) 
    as [a | b].
  + rewrite a; reflexivity.
  + rewrite nat_eqb_false in H.  
    * now elim H.  
    * assumption.
- intros  f0 H f1 H0 v s n m H1; unfold evalStrongRec in H1.
  unfold evalComposeFunc, evalOneParamList, evalList in H1.
  rewrite computeEvalStrongRecHelp in H1.
  unfold compose2 in H1.
  unfold evalComposeFunc, evalOneParamList, evalList in H1.
  simpl in H1.
  rewrite cPairProjections1 in H1.
  unfold A at 1 in H1;
    repeat first
      [ rewrite cTripleProj1 in H1
      | rewrite cTripleProj2 in H1
      | rewrite cTripleProj3 in H1
      | rewrite cPairProjections1 in H1
      | rewrite cPairProjections2 in H1 ].
  rewrite evalStrongRecHelp1 with (m := car m) in H1.
  rewrite evalStrongRecHelp1 with (m := cdr m) in H1.
  simpl in H1.
  destruct
    (eq_nat_dec n
       (cPair 1 (cPair (cTriplePi2 (car m)) (cTriplePi2 (cdr m))))) as [a | b].
  + rewrite <- a in H1.
    rewrite Nat.eqb_refl in H1.
    destruct
      (eq_nat_dec (cTriple v (codeTerm s) (codeFormula f0))
         (cTriplePi1 (car m))) as [a0 | b].
    * rewrite <- a0 in H1.
      rewrite Nat.eqb_refl in H1.
      destruct
        (eq_nat_dec (cTriple v (codeTerm s) (codeFormula f1))
           (cTriplePi1 (cdr m))) as [a1 | b].
      -- rewrite <- a1 in H1.
         rewrite Nat.eqb_refl in H1.
         simpl in H1.
         rewrite Nat.add_comm in H1; simpl in H1.
         decompose record (mult_lemma1 _ _ H1) /r; intros H2 H3.
         rewrite <- (cTripleProj (car m)) in H2.
         rewrite <- (cTripleProj (cdr m)) in H3.
         rewrite <- a0 in H2; clear a0.
         rewrite <- a1 in H3; clear a1.
         rewrite <- (H _ _ _ _ H2) in a.
         rewrite <- (H0 _ _ _ _ H3) in a.
         rewrite subFormulaImp.
         rewrite a; reflexivity.
      -- rewrite nat_eqb_false in H1.
         ++ elim H1; reflexivity.
         ++ assumption.
    * rewrite nat_eqb_false in H1.
      -- elim H1; reflexivity.
      -- assumption.
  + rewrite nat_eqb_false in H1.
    * elim H1; reflexivity.
    * assumption.
  + apply Nat.le_lt_trans with (cPair (car m) (cdr m)).
    * apply cPairLe2.
    * rewrite cPairProjections.
      unfold cTriple in |- *.
      apply Nat.lt_le_trans with (cPair 1 (cPair n m)).
      -- apply Nat.le_lt_trans with (cPair n m).
         ++ apply cPairLe2.
         ++ apply cPairLt2.
      -- apply cPairLe3.
         ++ apply Nat.le_trans with (cPair 1 (cPair (codeFormula f0) (codeFormula f1))).
            ** apply cPairLe1.
            ** apply Nat.le_trans with
                 (cPair (codeTerm s) (cPair 1 (cPair (codeFormula f0) (codeFormula f1)))).
               apply cPairLe2.
               apply cPairLe2.
         ++ apply le_n.
  + apply Nat.le_lt_trans with (cPair (car m) (cdr m)).
    * apply cPairLe1.
    * rewrite cPairProjections.
      unfold cTriple in |- *.
      apply Nat.lt_le_trans with (cPair 1 (cPair n m)).
      -- apply Nat.le_lt_trans with (cPair n m).
         ++ apply cPairLe2.
         ++ apply cPairLt2.
      -- apply cPairLe3.
         ++ apply Nat.le_trans with (cPair 1 (cPair (codeFormula f0) (codeFormula f1))).
            ** apply cPairLe1.
            ** apply Nat.le_trans with
                 (cPair (codeTerm s) (cPair 1 (cPair (codeFormula f0) (codeFormula f1)))).
               apply cPairLe2.
               apply cPairLe2.
         ++ apply le_n.
- intros f0 H v s n m H0; unfold evalStrongRec in H0.
  unfold evalComposeFunc, evalOneParamList, evalList in H0.
  rewrite computeEvalStrongRecHelp in H0.
  unfold compose2 in H0.
  unfold evalComposeFunc, evalOneParamList, evalList in H0.
  simpl in H0.
  rewrite cPairProjections1 in H0.
  unfold A at 1 in H0;
    repeat first
      [ rewrite cTripleProj1 in H0
      | rewrite cTripleProj2 in H0
      | rewrite cTripleProj3 in H0
      | rewrite cPairProjections1 in H0
      | rewrite cPairProjections2 in H0 ].
  rewrite evalStrongRecHelp1 with (m := m) in H0.
  + simpl in H0.
    induction (eq_nat_dec n (cPair 2 (cTriplePi2 m))) as [a | b].
    * rewrite <- a, Nat.eqb_refl in H0.
      induction
        (eq_nat_dec (cTriple v (codeTerm s) (codeFormula f0)) (cTriplePi1 m)) as [a0 | b].
      -- rewrite <- a0 in H0.
         rewrite Nat.eqb_refl in H0.
         simpl in H0.
         rewrite Nat.add_comm in H0; simpl in H0.
         rewrite <- (cTripleProj m) in H0.
         rewrite <- a0 in H0; clear a0.
         rewrite <- (H _ _ _ _ H0) in a.
         rewrite subFormulaNot.
         rewrite a; reflexivity.
      -- rewrite nat_eqb_false in H0.
         elim H0; reflexivity.
         assumption.
    * rewrite nat_eqb_false in H0.
      -- elim H0; reflexivity.
      -- assumption.
  + unfold cTriple in |- *.
    apply Nat.lt_le_trans with (cPair 2 (cPair n m)).
    * apply Nat.le_lt_trans with (cPair n m).
      -- apply cPairLe2.
      -- apply cPairLt2.
    * apply cPairLe3.
      apply Nat.le_trans with (cPair 2 (codeFormula f0)).
      -- apply cPairLe1.
      -- apply Nat.le_trans with (cPair (codeTerm s) (cPair 2 (codeFormula f0))).
         ++ apply cPairLe2.
         ++ apply cPairLe2.
      -- apply le_n.
- intros v a H v0 s n m H0; rewrite subFormulaForall.
  unfold evalStrongRec in H0.
  unfold evalComposeFunc, evalOneParamList, evalList in H0.
  rewrite computeEvalStrongRecHelp in H0.
  unfold compose2 in H0.
  unfold evalComposeFunc, evalOneParamList, evalList in H0.
  simpl in H0.
  rewrite cPairProjections1 in H0.
  unfold A at 1 in H0;
    repeat first
      [ rewrite cTripleProj1 in H0
      | rewrite cTripleProj2 in H0
      | rewrite cTripleProj3 in H0
      | rewrite cPairProjections1 in H0
      | rewrite cPairProjections2 in H0 ].
  induction (eq_nat_dec v v0) as [a0 | b].
  + rewrite a0 in H0.
    assert (H1: charFunction 2 Nat.eqb v0 v0 = 1) by (simpl; now rewrite Nat.eqb_refl).
    rewrite H1 in H0.
    induction (eq_nat_dec (codeFormula (forallH v a)) n) as [a1 | b].
    * assumption.
    * assert (H2: charFunction 2 Nat.eqb (cPair 3 (cPair v0 (codeFormula a))) n = 0).
      { unfold charFunction; rewrite nat_eqb_false.
        reflexivity.
        rewrite <- a0.
        apply b.
      }
      rewrite H2 in H0.
      simpl in H0.
      elim H0; reflexivity.
  + assert (H1: charFunction 2 Nat.eqb v0 v = 0).
    { simpl; rewrite nat_eqb_false.
      reflexivity.
      auto.
    } 
    rewrite H1 in H0; clear H1.
    unfold codeTerm in H0; rewrite codeFreeVarTermCorrect in H0.
    rewrite codeInCorrect in H0.
    induction (In_dec eq_nat_dec v (freeVarT s)) as [a0 | ?].
    * rewrite evalStrongRecHelp1 with (m := car m) in H0.
      -- rewrite evalStrongRecHelp1 with (m := cdr m) in H0.
         ++ simpl in H0.
            induction
              (eq_nat_dec n
                 (cPair 3
                    (cPair
                       (codeNewVar
                          (S
                             (cPair v0
                                (codeApp (codeList (freeVarT s))
                                   (codeFreeVarFormula (codeFormula a))))))
                       (cTriplePi2 (cdr m))))) as [a1 | ?].
            ** rewrite <- a1 in H0.
               rewrite Nat.eqb_refl in H0.
               induction
                 (eq_nat_dec (cTriple v0 (code.codeTerm s) (cTriplePi2 (car m)))
                    (cTriplePi1 (cdr m))) as [a2 | ?].
               --- rewrite a2 in H0.
                   rewrite Nat.eqb_refl in H0.
                   induction
                     (eq_nat_dec
                        (cTriple v
                           (cPair 0
                              (codeNewVar
                                 (S
                                    (cPair v0
                                       (codeApp (codeList (freeVarT s))
                                          (codeFreeVarFormula (codeFormula a)))))))
                           (codeFormula a)) (cTriplePi1 (car m))) as [a3 | ?].
                   +++ rewrite a3 in H0.
                       rewrite Nat.eqb_refl in H0.
                       simpl in H0.
                       rewrite Nat.add_comm in H0.
                       simpl in H0.
                       decompose record (mult_lemma1 _ _ H0) /r.
                       intros H1 H2;
                       rewrite <- (cTripleProj (car m)) in H1.
                       rewrite <- (cTripleProj (cdr m)) in H2.
                       rewrite <- a2 in H2; clear a2.
                       rewrite <- a3 in H1; clear a3.
                       assert (lt_depth L a (forallH v a)) by 
                         apply depthForall.
                       assert
                         (H4: cPair 0
                                (codeNewVar
                                   (S
                                      (cPair v0
                                         (codeApp (codeList (freeVarT s))
                                            (codeFreeVarFormula (codeFormula a)))))) =
                                codeTerm
                                  (var
                                     (codeNewVar
                                        (S
                                           (cPair v0
                                              (codeApp (codeList (freeVarT s))
                                                 (codeFreeVarFormula 
                                                    (codeFormula a)))))))) by reflexivity.
                       rewrite H4 in H1.
                       rewrite <- (H _ H3 _ _ _ _ H1) in H2.
                       assert
                         (H5: lt_depth L
                                (substF a v
                                   (var
                                      (codeNewVar
                                         (S
                                            (cPair v0
                                               (codeApp (codeList (freeVarT s))
                                                  (codeFreeVarFormula (codeFormula a))))))))
                                (forallH v a)).
                   ***  eapply eqDepth.
                        symmetry  in |- *.
                        apply subFormulaDepth.
                        apply depthForall.
                   *** rewrite <- (H _ H5 _ _ _ _ H2) in a1.
                       rewrite a1.
                       unfold codeFormula at 2 4 in |- *.
                       rewrite codeFreeVarFormulaCorrect.
                       rewrite codeAppCorrect.
                       replace (S (cPair v0 (codeList 
                                               (freeVarT s ++ freeVarF a))))
                         with (codeList (v0 :: freeVarT s ++ freeVarF a));
                         [ idtac | reflexivity ].
                       rewrite codeNewVarCorrect.
                       reflexivity.
                   +++ rewrite nat_eqb_false in H0.
                       elim H0.
                       reflexivity.
                       assumption.
               --- rewrite nat_eqb_false in H0.
                   elim H0.
                   reflexivity.
                   assumption.
            ** rewrite nat_eqb_false in H0.
               elim H0.
               reflexivity.
               assumption.
         ++ apply Nat.le_lt_trans with (cPair (car m) (cdr m)).
            apply cPairLe2.
            rewrite cPairProjections.
            unfold cTriple in |- *.
            apply Nat.lt_le_trans with (cPair 3 (cPair n m)).
            ** apply Nat.le_lt_trans with (cPair n m).
               --- apply cPairLe2.
               --- apply cPairLt2.
            ** apply cPairLe3.
               --- apply Nat.le_trans with (cPair 3 (cPair v (codeFormula a))).
                   +++ apply cPairLe1.
                   +++ apply
                       Nat.le_trans
                       with (cPair (code.codeTerm s) 
                               (cPair 3 (cPair v (codeFormula a)))).
                       *** apply cPairLe2.
                       *** apply cPairLe2.
               --- apply le_n.
      -- apply Nat.le_lt_trans with (cPair (car m) (cdr m)).
         ++ apply cPairLe1.
         ++ rewrite cPairProjections.
            unfold cTriple in |- *.
            apply Nat.lt_le_trans with (cPair 3 (cPair n m)).
            ** apply Nat.le_lt_trans with (cPair n m).
               --- apply cPairLe2.
               --- apply cPairLt2.
            ** apply cPairLe3.
               apply Nat.le_trans with (cPair 3 (cPair v (codeFormula a))).
               --- apply cPairLe1.
               --- apply Nat.le_trans with 
                     (cPair (code.codeTerm s) 
                        (cPair 3 (cPair v (codeFormula a)))).
                   +++ apply cPairLe2.
                   +++ apply cPairLe2.
               --- apply le_n.
    * rewrite evalStrongRecHelp1 with (m := m) in H0.
      -- simpl in H0.
         induction (eq_nat_dec n (cPair 3 (cPair v (cTriplePi2 m)))) 
           as [a0 | ?].
         ++ rewrite <- a0 in H0.
            rewrite Nat.eqb_refl in H0.
            induction
              (eq_nat_dec (cTriple v0 (code.codeTerm s) (codeFormula a))
                 (cTriplePi1 m)) as [a1| ?].
            ** rewrite <- a1 in H0.
               rewrite Nat.eqb_refl in H0.
               simpl in H0.
               rewrite Nat.add_comm in H0.
               simpl in H0.
               assert (H1: lt_depth L a (forallH v a))
                 by apply depthForall.
               rewrite <- (cTripleProj m) in H0.
               rewrite <- a1 in H0; clear a1.
               rewrite <- (H _ H1 _ _ _ _ H0) in a0.
               rewrite a0.
               reflexivity.
            ** rewrite nat_eqb_false in H0.
               --- elim H0.
                   reflexivity.
               --- assumption.
         ++ rewrite nat_eqb_false in H0.
            elim H0.
            reflexivity.
            assumption.
      -- unfold cTriple in |- *.
         apply Nat.lt_le_trans with (cPair 3 (cPair n m)).
         ++ apply Nat.le_lt_trans with (cPair n m).
            ** apply cPairLe2.
            ** apply cPairLt2.
         ++ apply cPairLe3.
            ** apply Nat.le_trans with (cPair 3 (cPair v (codeFormula a))).
               --- apply cPairLe1.
               --- apply Nat.le_trans with 
                     (cPair (code.codeTerm s) 
                        (cPair 3 (cPair v (codeFormula a)))).
                   +++ apply cPairLe2.
                   +++ apply cPairLe2.
            ** apply le_n.
Qed.

Lemma switch5IsPR :
 forall (f1 f2 f3 f4 f5 : nat -> nat -> nat) (g : nat -> nat),
 isPR 2 f1 ->
 isPR 2 f2 ->
 isPR 2 f3 ->
 isPR 2 f4 ->
 isPR 2 f5 ->
 isPR 1 g ->
 isPR 2
   (fun n recs : nat =>
    switchPR (g n)
      (switchPR (pred (g n))
         (switchPR (pred (pred (g n)))
            (switchPR (pred (pred (pred (g n)))) (f1 n recs) (f2 n recs))
            (f3 n recs)) (f4 n recs)) (f5 n recs)).
Proof.
  intros ? ? ? ? ? g H H0 H1 H2 H3 H4.
  assert (H5: isPR 1 (fun trace : nat => pred (g trace))).
  { apply compose1_1IsPR.
    assumption.
    apply predIsPR.
  } 
  assert (H6: isPR 1 (fun trace : nat => pred (pred (g trace)))).
  { apply compose1_1IsPR with (f := fun trace : nat => pred (g trace)).
    assumption.
    apply predIsPR.
  } 
  assert (H7: isPR 1 (fun trace : nat => pred (pred (pred (g trace))))).
  { apply compose1_1IsPR with (f := fun trace : nat => pred (pred (g trace))).
    - assumption.
    - apply predIsPR.
  } 
  apply compose2_3IsPR with
    (f1 := fun trace recs : nat => g trace)
    (f2 := fun trace recs : nat =>
             switchPR (pred (g trace))
               (switchPR (pred (pred (g trace)))
                  (switchPR (pred (pred (pred (g trace)))) 
                     (f1 trace recs) (f2 trace recs)) 
                  (f3 trace recs)) (f4 trace recs))
    (f3 := f5).
  - apply filter10IsPR; assumption.
  - apply  compose2_3IsPR with
      (f1 := fun trace recs : nat => pred (g trace))
      (f2 := fun trace recs : nat =>
               switchPR (pred (pred (g trace)))
                 (switchPR (pred (pred (pred (g trace)))) 
                    (f1 trace recs) (f2 trace recs)) (f3 trace recs))
      (f3 := f4).
    + apply filter10IsPR with (g := fun trace : nat => pred (g trace)); 
        assumption.
    + apply compose2_3IsPR with
        (f1 := fun trace recs : nat => pred (pred (g trace)))
        (f2 := fun trace recs : nat =>
                 switchPR (pred (pred (pred (g trace)))) 
                   (f1 trace recs) (f2 trace recs))
        (f3 := f3).
      * apply filter10IsPR with (g := fun trace : nat => pred (pred (g trace))).
        assumption.
      * apply compose2_3IsPR with
          (f1 := fun trace recs : nat => pred (pred (pred (g trace))))
          (f2 := f1)
          (f3 := f2).
        -- apply filter10IsPR with 
             (g := fun trace : nat => pred (pred (pred (g trace)))).
           assumption.
        -- assumption.
        -- assumption.
        -- apply switchIsPR.
      * assumption.
      * apply switchIsPR; assumption.
    + assumption.
    + apply switchIsPR.
  - assumption.
  - apply switchIsPR. 
Qed.
 
Lemma checkTraceIsPR : isPR 1 checkSubFormulaTrace.
Proof.
  unfold checkSubFormulaTrace in |- *.
  assert (H: isPR 1 (fun trace : nat => car (cTriplePi3 (cTriplePi1 trace)))).
  { apply compose1_1IsPR with
      (g := cPairPi1)
      (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
    - apply compose1_1IsPR.
      + apply cTriplePi1IsPR.
      + apply cTriplePi3IsPR.
    - apply cPairPi1IsPR.
  } 
  apply evalStrongRecIsPR.
  assert
    (H0: forall (f1 f2 f3 f4 f5 : nat -> nat -> nat) (g : nat -> nat),
        isPR 2 f1 ->
        isPR 2 f2 ->
        isPR 2 f3 ->
        isPR 2 f4 ->
        isPR 2 f5 ->
        isPR 1 g ->
        isPR 2
          (fun trace recs : nat =>
             switchPR (g trace)
               (switchPR (pred (g trace))
                  (switchPR (pred (pred (g trace)))
                     (switchPR (pred (pred (pred (g trace)))) 
                        (f1 trace recs) (f2 trace recs)) (f3 trace recs))
                  (f4 trace recs)) (f5 trace recs))).
  - apply switch5IsPR.
  - assert (H1: isPR 1 (fun trace : nat => cTriplePi1 (cTriplePi1 trace))).
    + apply compose1_1IsPR; apply cTriplePi1IsPR.
    + assert (H2: isPR 1 (fun trace : nat => cTriplePi2 (cTriplePi1 trace))).
      { apply compose1_1IsPR.
        - apply cTriplePi1IsPR.
        - apply cTriplePi2IsPR.
      } 
      assert (H3: isPR 1 (fun trace : nat => cTriplePi3 (cTriplePi1 trace))).
      { apply compose1_1IsPR.
        apply cTriplePi1IsPR.
        apply cTriplePi3IsPR.
      } 
      assert (H4: isPR 1 (fun trace : nat => car (cTriplePi3 (cTriplePi1 trace)))).
      { apply compose1_1IsPR with 
          (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
        - assumption.
        - apply cPairPi1IsPR.
      } 
      apply H0 with
        (f1 := fun trace recs : nat =>
                 charFunction 2 Nat.eqb (cTriplePi2 trace)
                   (cPair (car (cTriplePi3 (cTriplePi1 trace)))
                      (codeSubTerms (cdr (cTriplePi3 (cTriplePi1 trace)))
                         (cTriplePi1 (cTriplePi1 trace))
                         (cTriplePi2 (cTriplePi1 trace)))))
        (f2 := fun trace recs : nat =>
                 switchPR
                   (charFunction 2 Nat.eqb (cTriplePi1 (cTriplePi1 trace))
                      (car (cdr (cTriplePi3 (cTriplePi1 trace)))))
                   (charFunction 2 Nat.eqb (cTriplePi3 (cTriplePi1 trace))
                      (cTriplePi2 trace))
                   (switchPR
                      (codeIn (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                         (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace))))
                      (charFunction 0
                         (Nat.eqb (cTriplePi2 trace)
                            (cPair 3
                               (cPair
                                  (codeNewVar
                                     (S
                                        (cPair (cTriplePi1 (cTriplePi1 trace))
                                           (codeApp
                                              (codeFreeVarTerm
                                                 (cTriplePi2 (cTriplePi1 trace)))
                                              (codeFreeVarFormula
                                                 (cdr
                                                    (cdr
                                                       (cTriplePi3
                                                          (cTriplePi1 trace)))))))))
                                  (cTriplePi2 (cdr (cTriplePi3 trace))))) &&
                            (Nat.eqb
                               (cTriple (cTriplePi1 (cTriplePi1 trace))
                                  (cTriplePi2 (cTriplePi1 trace))
                                  (cTriplePi2 (car (cTriplePi3 trace))))
                               (cTriplePi1 (cdr (cTriplePi3 trace))) &&
                               Nat.eqb
                                 (cTriple
                                    (car
                                       (cdr (cTriplePi3 (cTriplePi1 trace))))
                                    (cPair 0
                                       (codeNewVar
                                          (S
                                             (cPair (cTriplePi1 (cTriplePi1 trace))
                                                (codeApp
                                                   (codeFreeVarTerm
                                                      (cTriplePi2 (cTriplePi1 trace)))
                                                   (codeFreeVarFormula
                                                      (cdr
                                                         (cdr
                                                            (cTriplePi3
                                                               (cTriplePi1 trace))))))))))
                                    (cdr
                                       (cdr (cTriplePi3 (cTriplePi1 trace)))))
                                 (cTriplePi1 (car (cTriplePi3 trace))))) *
                         (codeNth (trace - S (car (cTriplePi3 trace))) recs *
                            codeNth (trace - S (cdr (cTriplePi3 trace))) recs))
                      (charFunction 0
                         (Nat.eqb (cTriplePi2 trace)
                            (cPair 3
                               (cPair
                                  (car
                                     (cdr (cTriplePi3 (cTriplePi1 trace))))
                                  (cTriplePi2 (cTriplePi3 trace)))) &&
                            Nat.eqb
                              (cTriple (cTriplePi1 (cTriplePi1 trace))
                                 (cTriplePi2 (cTriplePi1 trace))
                                 (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
                              (cTriplePi1 (cTriplePi3 trace))) *
                         codeNth (trace - S (cTriplePi3 trace)) recs)))
        (f3 := fun trace recs : nat =>
                 charFunction 0
                   (Nat.eqb (cTriplePi2 trace)
                      (cPair 2 (cTriplePi2 (cTriplePi3 trace))) &&
                      Nat.eqb
                        (cTriple (cTriplePi1 (cTriplePi1 trace))
                           (cTriplePi2 (cTriplePi1 trace))
                           (cdr (cTriplePi3 (cTriplePi1 trace))))
                        (cTriplePi1 (cTriplePi3 trace))) *
                   codeNth (trace - S (cTriplePi3 trace)) recs)
        (f4 := fun trace recs : nat =>
                 charFunction 0
                   (Nat.eqb (cTriplePi2 trace)
                      (cPair 1
                         (cPair (cTriplePi2 (car (cTriplePi3 trace)))
                            (cTriplePi2 (cdr (cTriplePi3 trace))))) &&
                      (Nat.eqb
                         (cTriple (cTriplePi1 (cTriplePi1 trace))
                            (cTriplePi2 (cTriplePi1 trace))
                            (car (cdr (cTriplePi3 (cTriplePi1 trace)))))
                         (cTriplePi1 (car (cTriplePi3 trace))) &&
                         Nat.eqb
                           (cTriple (cTriplePi1 (cTriplePi1 trace))
                              (cTriplePi2 (cTriplePi1 trace))
                              (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
                           (cTriplePi1 (cdr (cTriplePi3 trace))))) *
                   (codeNth (trace - S (car (cTriplePi3 trace))) recs *
                      codeNth (trace - S (cdr (cTriplePi3 trace))) recs))
        (f5 := fun trace recs : nat =>
                 charFunction 2 Nat.eqb (cTriplePi2 trace)
                   (cPair 0
                      (cPair
                         (codeSubTerm
                            (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                            (cTriplePi1 (cTriplePi1 trace))
                            (cTriplePi2 (cTriplePi1 trace)))
                         (codeSubTerm
                            (cdr (cdr (cTriplePi3 (cTriplePi1 trace))))
                            (cTriplePi1 (cTriplePi1 trace))
                            (cTriplePi2 (cTriplePi1 trace))))))
        (g := fun trace : nat => car (cTriplePi3 (cTriplePi1 trace))).
      * apply
          filter10IsPR
          with
          (g := fun trace : nat =>
                  charFunction 2 Nat.eqb (cTriplePi2 trace)
                    (cPair (car (cTriplePi3 (cTriplePi1 trace)))
                       (codeSubTerms (cdr (cTriplePi3 (cTriplePi1 trace)))
                          (cTriplePi1 (cTriplePi1 trace))
                          (cTriplePi2 (cTriplePi1 trace))))).
        apply compose1_2IsPR with
          (g := charFunction 2 Nat.eqb)
          (f := fun trace : nat => cTriplePi2 trace)
          (f' := fun trace : nat =>
                   cPair (car (cTriplePi3 (cTriplePi1 trace)))
                     (codeSubTerms (cdr (cTriplePi3 (cTriplePi1 trace)))
                        (cTriplePi1 (cTriplePi1 trace))
                        (cTriplePi2 (cTriplePi1 trace)))).
        -- apply cTriplePi2IsPR.
        -- apply  compose1_2IsPR with
             (f := fun trace : nat => car (cTriplePi3 (cTriplePi1 trace)))
             (f' := fun trace : nat =>
                      codeSubTerms (cdr (cTriplePi3 (cTriplePi1 trace)))
                        (cTriplePi1 (cTriplePi1 trace)) (cTriplePi2 (cTriplePi1 trace))).
           ++ assumption.
           ++ apply compose1_3IsPR with
                (f1 := fun trace : nat => cdr (cTriplePi3 (cTriplePi1 trace)))
                (f2 := fun trace : nat => cTriplePi1 (cTriplePi1 trace))
                (f3 := fun trace : nat => cTriplePi2 (cTriplePi1 trace)).
              ** apply compose1_1IsPR with 
                   (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
                 --- assumption.
                 --- apply cPairPi2IsPR.
              ** assumption.
              ** assumption.
              ** apply codeSubTermsIsPR.
           ++ apply cPairIsPR.
        -- apply eqIsPR.
      * apply  compose2_3IsPR with
          (f1 := fun trace recs : nat =>
                   charFunction 2 Nat.eqb (cTriplePi1 (cTriplePi1 trace))
                     (car (cdr (cTriplePi3 (cTriplePi1 trace)))))
          (f2 := fun trace recs : nat =>
                   charFunction 2 Nat.eqb (cTriplePi3 (cTriplePi1 trace))
                     (cTriplePi2 trace))
          (f3 := fun trace recs : nat =>
                   switchPR
                     (codeIn (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                        (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace))))
                     (charFunction 0
                        (Nat.eqb (cTriplePi2 trace)
                           (cPair 3
                              (cPair
                                 (codeNewVar
                                    (S
                                       (cPair (cTriplePi1 (cTriplePi1 trace))
                                          (codeApp
                                             (codeFreeVarTerm
                                                (cTriplePi2 (cTriplePi1 trace)))
                                             (codeFreeVarFormula
                                                (cdr
                                                   (cdr
                                                      (cTriplePi3
                                                         (cTriplePi1 trace)))))))))
                                 (cTriplePi2 (cdr (cTriplePi3 trace))))) &&
                           (Nat.eqb
                              (cTriple (cTriplePi1 (cTriplePi1 trace))
                                 (cTriplePi2 (cTriplePi1 trace))
                                 (cTriplePi2 (car (cTriplePi3 trace))))
                              (cTriplePi1 (cdr (cTriplePi3 trace))) &&
                              Nat.eqb
                                (cTriple
                                   (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                                   (cPair 0
                                      (codeNewVar
                                         (S
                                            (cPair (cTriplePi1 (cTriplePi1 trace))
                                               (codeApp
                                                  (codeFreeVarTerm
                                                     (cTriplePi2 (cTriplePi1 trace)))
                                                  (codeFreeVarFormula
                                                     (cdr
                                                        (cdr
                                                           (cTriplePi3 
                                                              (cTriplePi1 trace))))))))))
                                   (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
                                (cTriplePi1 (car (cTriplePi3 trace))))) *
                        (codeNth (trace - S (car (cTriplePi3 trace))) recs *
                           codeNth (trace - S (cdr (cTriplePi3 trace))) recs))
                     (charFunction 0
                        (Nat.eqb (cTriplePi2 trace)
                           (cPair 3
                              (cPair
                                 (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                                 (cTriplePi2 (cTriplePi3 trace)))) &&
                           Nat.eqb
                             (cTriple (cTriplePi1 (cTriplePi1 trace))
                                (cTriplePi2 (cTriplePi1 trace))
                                (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
                             (cTriplePi1 (cTriplePi3 trace))) *
                        codeNth (trace - S (cTriplePi3 trace)) recs)).
        -- apply filter10IsPR with
             (g := fun trace : nat =>
                     charFunction 2 Nat.eqb (cTriplePi1 (cTriplePi1 trace))
                       (car (cdr (cTriplePi3 (cTriplePi1 trace))))).
           apply
             compose1_2IsPR
             with
             (g := charFunction 2 Nat.eqb)
             (f := fun trace : nat => cTriplePi1 (cTriplePi1 trace))
             (f' := fun trace : nat =>
                      car (cdr (cTriplePi3 (cTriplePi1 trace)))).
           ++ assumption.
           ++ apply compose1_1IsPR with 
                (f := fun trace : nat => cdr (cTriplePi3 (cTriplePi1 trace))).
              ** apply compose1_1IsPR with 
                   (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
                 --- assumption.
                 --- apply cPairPi2IsPR.
              ** apply cPairPi1IsPR.
           ++ apply eqIsPR.
        -- apply filter10IsPR with
             (g := fun trace : nat =>
                     charFunction 2 Nat.eqb (cTriplePi3 (cTriplePi1 trace))
                       (cTriplePi2 trace)).
           apply
             compose1_2IsPR
             with
             (g := charFunction 2 Nat.eqb)
             (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace))
             (f' := cTriplePi2).
           ++ assumption.
           ++ apply cTriplePi2IsPR.
           ++ apply eqIsPR.
        -- apply compose2_3IsPR with
             (f1 := fun trace recs : nat =>
                      codeIn (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                        (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace))))
             (f2 := fun trace recs : nat =>
                      charFunction 0
                        (Nat.eqb (cTriplePi2 trace)
                           (cPair 3
                              (cPair
                                 (codeNewVar
                                    (S
                                       (cPair (cTriplePi1 (cTriplePi1 trace))
                                          (codeApp
                                             (codeFreeVarTerm
                                                (cTriplePi2 (cTriplePi1 trace)))
                                             (codeFreeVarFormula
                                                (cdr
                                                   (cdr
                                                      (cTriplePi3 
                                                         (cTriplePi1 trace)))))))))
                                 (cTriplePi2 (cdr (cTriplePi3 trace))))) &&
                           (Nat.eqb
                              (cTriple (cTriplePi1 (cTriplePi1 trace))
                                 (cTriplePi2 (cTriplePi1 trace))
                                 (cTriplePi2 (car (cTriplePi3 trace))))
                              (cTriplePi1 (cdr (cTriplePi3 trace))) &&
                              Nat.eqb
                                (cTriple
                                   (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                                   (cPair 0
                                      (codeNewVar
                                         (S
                                            (cPair (cTriplePi1 (cTriplePi1 trace))
                                               (codeApp
                                                  (codeFreeVarTerm
                                                     (cTriplePi2 (cTriplePi1 trace)))
                                                  (codeFreeVarFormula
                                                     (cdr
                                                        (cdr
                                                           (cTriplePi3 
                                                              (cTriplePi1 trace))))))))))
                                   (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
                                (cTriplePi1 (car (cTriplePi3 trace))))) *
                        (codeNth (trace - S (car (cTriplePi3 trace))) recs *
                           codeNth (trace - S (cdr (cTriplePi3 trace))) recs))
             (f3 := fun trace recs : nat =>
                      charFunction 0
                        (Nat.eqb (cTriplePi2 trace)
                           (cPair 3
                              (cPair
                                 (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                                 (cTriplePi2 (cTriplePi3 trace)))) &&
                           Nat.eqb
                             (cTriple (cTriplePi1 (cTriplePi1 trace))
                                (cTriplePi2 (cTriplePi1 trace))
                                (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
                             (cTriplePi1 (cTriplePi3 trace))) *
                        codeNth (trace - S (cTriplePi3 trace)) recs).
           ++ apply filter10IsPR with
                (g := fun trace : nat =>
                        codeIn (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                          (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace)))).
              apply compose1_2IsPR with
                (f := fun trace : nat =>
                        car (cdr (cTriplePi3 (cTriplePi1 trace))))
                (f' := fun trace : nat => codeFreeVarTerm (cTriplePi2 
                                                             (cTriplePi1 trace))).
              ** apply compose1_1IsPR with
                   (f := fun trace : nat => cdr (cTriplePi3 (cTriplePi1 trace))).
                 --- apply compose1_1IsPR with
                       (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
                     +++ assumption.
                     +++ apply cPairPi2IsPR.
                 --- apply cPairPi1IsPR.
              ** apply compose1_1IsPR with 
                   (f := fun trace : nat => cTriplePi2 (cTriplePi1 trace)).
                 --- assumption.
                 --- apply codeFreeVarTermIsPR.
              ** apply codeInIsPR.
           ++ assert
               (H5: isPR 1
                      (fun trace : nat =>
                         codeNewVar
                           (S
                              (cPair (cTriplePi1 (cTriplePi1 trace))
                                 (codeApp (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace)))
                                    (codeFreeVarFormula
                                       (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))))))).
              { apply
                compose1_1IsPR
                with
                (f := fun trace : nat =>
                        S
                          (cPair (cTriplePi1 (cTriplePi1 trace))
                             (codeApp (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace)))
                                (codeFreeVarFormula
                                   (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))))).
               apply compose1_1IsPR with
                  (f := fun trace : nat =>
                          cPair (cTriplePi1 (cTriplePi1 trace))
                            (codeApp (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace)))
                               (codeFreeVarFormula
                                  (cdr (cdr (cTriplePi3 (cTriplePi1 trace))))))).
                - apply compose1_2IsPR with
                    (f := fun trace : nat => cTriplePi1 (cTriplePi1 trace))
                    (f' := fun trace : nat =>
                             codeApp (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace)))
                               (codeFreeVarFormula
                                  (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))).
                  + assumption.
                  + apply compose1_2IsPR with
                      (f := fun trace : nat => codeFreeVarTerm 
                                                 (cTriplePi2 (cTriplePi1 trace)))
                      (f' := fun trace : nat =>
                               codeFreeVarFormula
                                 (cdr (cdr (cTriplePi3 (cTriplePi1 trace))))).
                    * apply compose1_1IsPR with
                        (f := fun trace : nat => cTriplePi2 (cTriplePi1 trace)).
                      -- assumption.
                      -- apply codeFreeVarTermIsPR.
                    * apply compose1_1IsPR with
                        (f := fun trace : nat =>
                                cdr (cdr (cTriplePi3 (cTriplePi1 trace)))).
                      -- apply compose1_1IsPR with 
                           (f := fun trace : nat => cdr (cTriplePi3 (cTriplePi1 trace))).
                         ++ apply compose1_1IsPR with
                              (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
                            ** assumption.
                            ** apply cPairPi2IsPR.
                         ++ apply cPairPi2IsPR.
                      -- apply codeFreeVarFormulaIsPR.
                    * apply codeAppIsPR.
                  + apply cPairIsPR.
                - apply succIsPR.
                - apply codeNewVarIsPR.
              } 
           **  apply compose2_2IsPR with
                (f := fun trace recs : nat =>
                        charFunction 0
                          (Nat.eqb (cTriplePi2 trace)
                             (cPair 3
                                (cPair
                                   (codeNewVar
                                      (S
                                         (cPair (cTriplePi1 (cTriplePi1 trace))
                                            (codeApp
                                               (codeFreeVarTerm
                                                  (cTriplePi2 (cTriplePi1 trace)))
                                               (codeFreeVarFormula
                                                  (cdr
                                                     (cdr
                                                        (cTriplePi3 (cTriplePi1 trace)))))))))
                                   (cTriplePi2 (cdr (cTriplePi3 trace))))) &&
                             (Nat.eqb
                                (cTriple (cTriplePi1 (cTriplePi1 trace))
                                   (cTriplePi2 (cTriplePi1 trace))
                                   (cTriplePi2 (car (cTriplePi3 trace))))
                                (cTriplePi1 (cdr (cTriplePi3 trace))) &&
                                Nat.eqb
                                  (cTriple
                                     (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                                     (cPair 0
                                        (codeNewVar
                                           (S
                                              (cPair (cTriplePi1 (cTriplePi1 trace))
                                                 (codeApp
                                                    (codeFreeVarTerm
                                                       (cTriplePi2 (cTriplePi1 trace)))
                                                    (codeFreeVarFormula
                                                       (cdr
                                                          (cdr
                                                             (cTriplePi3
                                                                (cTriplePi1 trace))))))))))
                                     (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
                                  (cTriplePi1 (car (cTriplePi3 trace))))))
                (g := fun trace recs : nat =>
                        codeNth (trace - S (car (cTriplePi3 trace))) recs *
                          codeNth (trace - S (cdr (cTriplePi3 trace))) recs).
               --- apply filter10IsPR with
                     (g := fun trace : nat =>
                             charFunction 0
                               (Nat.eqb (cTriplePi2 trace)
                                  (cPair 3
                                     (cPair
                                        (codeNewVar
                                           (S
                                              (cPair (cTriplePi1 (cTriplePi1 trace))
                                                 (codeApp
                                                    (codeFreeVarTerm
                                                       (cTriplePi2 (cTriplePi1 trace)))
                                                    (codeFreeVarFormula
                                                       (cdr
                                                          (cdr
                                                             (cTriplePi3 (cTriplePi1 trace)))))))))
                                        (cTriplePi2 (cdr (cTriplePi3 trace))))) &&
                                  (Nat.eqb
                                     (cTriple (cTriplePi1 (cTriplePi1 trace))
                                        (cTriplePi2 (cTriplePi1 trace))
                                        (cTriplePi2 (car (cTriplePi3 trace))))
                                     (cTriplePi1 (cdr (cTriplePi3 trace))) &&
                                     Nat.eqb
                                       (cTriple
                                          (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                                          (cPair 0
                                             (codeNewVar
                                                (S
                                                   (cPair (cTriplePi1 (cTriplePi1 trace))
                                                      (codeApp
                                                         (codeFreeVarTerm
                                                            (cTriplePi2 (cTriplePi1 trace)))
                                                         (codeFreeVarFormula
                                                            (cdr
                                                               (cdr
                                                                  (cTriplePi3 (cTriplePi1 trace))))))))))
                                          (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
                                       (cTriplePi1 (car (cTriplePi3 trace)))))).
                   apply
                     (andRelPR 1)
                     with
                     (R := fun trace : nat =>
                             Nat.eqb (cTriplePi2 trace)
                               (cPair 3
                                  (cPair
                                     (codeNewVar
                                        (S
                                           (cPair (cTriplePi1 (cTriplePi1 trace))
                                              (codeApp
                                                 (codeFreeVarTerm
                                                    (cTriplePi2 (cTriplePi1 trace)))
                                                 (codeFreeVarFormula
                                                    (cdr
                                                       (cdr (cTriplePi3 (cTriplePi1 trace)))))))))
                                     (cTriplePi2 (cdr (cTriplePi3 trace))))))
                     (R' := fun trace : nat =>
                              Nat.eqb
                                (cTriple (cTriplePi1 (cTriplePi1 trace))
                                   (cTriplePi2 (cTriplePi1 trace))
                                   (cTriplePi2 (car (cTriplePi3 trace))))
                                (cTriplePi1 (cdr (cTriplePi3 trace))) &&
                                Nat.eqb
                                  (cTriple (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                                     (cPair 0
                                        (codeNewVar
                                           (S
                                              (cPair (cTriplePi1 (cTriplePi1 trace))
                                                 (codeApp
                                                    (codeFreeVarTerm
                                                       (cTriplePi2 (cTriplePi1 trace)))
                                                    (codeFreeVarFormula
                                                       (cdr
                                                          (cdr
                                                             (cTriplePi3 
                                                                (cTriplePi1 trace))))))))))
                                     (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
                                  (cTriplePi1 (car (cTriplePi3 trace)))).
                   +++  unfold isPRrel in |- *.
                        apply
                          compose1_2IsPR
                          with
                          (g := charFunction 2 Nat.eqb)
                          (f := fun trace : nat => cTriplePi2 trace)
                          (f' := fun trace : nat =>
                                   cPair 3
                                     (cPair
                                        (codeNewVar
                                           (S
                                              (cPair (cTriplePi1 (cTriplePi1 trace))
                                                 (codeApp
                                                    (codeFreeVarTerm (cTriplePi2 (cTriplePi1 trace)))
                                                    (codeFreeVarFormula
                                                       (cdr
                                                          (cdr (cTriplePi3 (cTriplePi1 trace)))))))))
                                        (cTriplePi2 (cdr (cTriplePi3 trace))))).
                        apply cTriplePi2IsPR.
                        apply
                          compose1_2IsPR
                          with
                          (f := fun trace : nat => 3)
                          (f' := fun trace : nat =>
                                   cPair
                                     (codeNewVar
                                        (S
                                           (cPair (cTriplePi1 (cTriplePi1 trace))
                                              (codeApp
                                                 (codeFreeVarTerm 
                                                    (cTriplePi2 (cTriplePi1 trace)))
                                                 (codeFreeVarFormula
                                                    (cdr
                                                       (cdr 
                                                          (cTriplePi3 
                                                             (cTriplePi1 trace)))))))))
                                     (cTriplePi2 (cdr (cTriplePi3 trace)))).
                        *** apply const1_NIsPR.
                        *** apply  compose1_2IsPR with
                              (f := fun trace : nat =>
                                      codeNewVar
                                        (S
                                           (cPair (cTriplePi1 (cTriplePi1 trace))
                                              (codeApp (codeFreeVarTerm 
                                                          (cTriplePi2 (cTriplePi1 trace)))
                                                 (codeFreeVarFormula
                                                    (cdr (cdr (cTriplePi3 
                                                                 (cTriplePi1 trace)))))))))
                              (f' := fun trace : nat => 
                                       cTriplePi2 (cdr (cTriplePi3 trace))).
                            assumption.
                            apply compose1_1IsPR with
                              (f := fun trace : nat => cdr (cTriplePi3 trace)).
                            apply compose1_1IsPR.
                            apply cTriplePi3IsPR.
                            apply cPairPi2IsPR.
                            apply cTriplePi2IsPR.
                            apply cPairIsPR.
                        *** apply cPairIsPR.
                        *** apply eqIsPR.
                   +++ apply (andRelPR 1) with
                         (R := fun trace : nat =>
                                 Nat.eqb
                                   (cTriple (cTriplePi1 (cTriplePi1 trace))
                                      (cTriplePi2 (cTriplePi1 trace))
                                      (cTriplePi2 (car (cTriplePi3 trace))))
                                   (cTriplePi1 (cdr (cTriplePi3 trace))))
                         (R' := fun trace : nat =>
                                  Nat.eqb
                                    (cTriple (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                                       (cPair 0
                                          (codeNewVar
                                             (S
                                                (cPair (cTriplePi1 (cTriplePi1 trace))
                                                   (codeApp
                                                      (codeFreeVarTerm
                                                         (cTriplePi2 (cTriplePi1 trace)))
                                                      (codeFreeVarFormula
                                                         (cdr
                                                            (cdr
                                                               (cTriplePi3 
                                                                  (cTriplePi1 trace))))))))))
                                       (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
                                    (cTriplePi1 (car (cTriplePi3 trace)))).
                       apply compose1_2IsPR with
                         (g := charFunction 2 Nat.eqb)
                         (f := fun trace : nat =>
                                 cTriple (cTriplePi1 (cTriplePi1 trace))
                                   (cTriplePi2 (cTriplePi1 trace))
                                   (cTriplePi2 (car (cTriplePi3 trace))))
                         (f' := fun trace : nat => cTriplePi1 (cdr (cTriplePi3 trace))).
                       apply
                         compose1_3IsPR
                         with
                         (f1 := fun trace : nat => cTriplePi1 (cTriplePi1 trace))
                         (f2 := fun trace : nat => cTriplePi2 (cTriplePi1 trace))
                         (f3 := fun trace : nat => cTriplePi2 (car (cTriplePi3 trace))).
                       assumption.
                       assumption.
                       apply
                         compose1_1IsPR with 
                         (f := fun trace : nat => car (cTriplePi3 trace)).
                       apply compose1_1IsPR.
                       apply cTriplePi3IsPR.
                       apply cPairPi1IsPR.
                       apply cTriplePi2IsPR.
                       apply cTripleIsPR.
                       apply
                         compose1_1IsPR with 
                         (f := fun trace : nat => cdr (cTriplePi3 trace)).
                       apply compose1_1IsPR.
                       apply cTriplePi3IsPR.
                       apply cPairPi2IsPR.
                       apply cTriplePi1IsPR.
                       apply eqIsPR.
                       apply
                         compose1_2IsPR
                         with
                         (g := charFunction 2 Nat.eqb)
                         (f := fun trace : nat =>
                                 cTriple (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                                   (cPair 0
                                      (codeNewVar
                                         (S
                                            (cPair (cTriplePi1 (cTriplePi1 trace))
                                               (codeApp
                                                  (codeFreeVarTerm 
                                                     (cTriplePi2 (cTriplePi1 trace)))
                                                  (codeFreeVarFormula
                                                     (cdr
                                                        (cdr (cTriplePi3 
                                                                (cTriplePi1 trace))))))))))
                                   (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
                         (f' := fun trace : nat => cTriplePi1 (car (cTriplePi3 trace))).
                       apply
                         compose1_3IsPR
                         with
                         (f1 := fun trace : nat =>
                                  car (cdr (cTriplePi3 (cTriplePi1 trace))))
                         (f2 := fun trace : nat =>
                                  cPair 0
                                    (codeNewVar
                                       (S
                                          (cPair (cTriplePi1 (cTriplePi1 trace))
                                             (codeApp
                                                (codeFreeVarTerm 
                                                   (cTriplePi2 (cTriplePi1 trace)))
                                                (codeFreeVarFormula
                                                   (cdr
                                                      (cdr 
                                                         (cTriplePi3 
                                                            (cTriplePi1 trace))))))))))
                         (f3 := fun trace : nat =>
                                  cdr (cdr (cTriplePi3 (cTriplePi1 trace)))).
                       apply
                         compose1_1IsPR
                         with (f := fun trace : nat => 
                                      cdr (cTriplePi3 (cTriplePi1 trace))).
                       apply
                         compose1_1IsPR with 
                         (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
                       assumption.
                       apply cPairPi2IsPR.
                       apply cPairPi1IsPR.
                       apply
                         compose1_2IsPR
                         with
                         (f := fun trace : nat => 0)
                         (f' := fun trace : nat =>
                                  codeNewVar
                                    (S
                                       (cPair (cTriplePi1 (cTriplePi1 trace))
                                          (codeApp (codeFreeVarTerm 
                                                      (cTriplePi2 (cTriplePi1 trace)))
                                             (codeFreeVarFormula
                                                (cdr (cdr 
                                                        (cTriplePi3 
                                                           (cTriplePi1 trace))))))))).
                       apply const1_NIsPR.
                       assumption.
                       apply cPairIsPR.
                       apply compose1_1IsPR with 
                         (f := fun trace : nat => cdr (cTriplePi3 (cTriplePi1 trace))).
                       apply
                         compose1_1IsPR with 
                         (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
                       assumption.
                       apply cPairPi2IsPR.
                       apply cPairPi2IsPR.
                       apply cTripleIsPR.
                       apply
                         compose1_1IsPR with 
                         (f := fun trace : nat => car (cTriplePi3 trace)).
                       apply compose1_1IsPR. 
                       apply cTriplePi3IsPR.
                       apply cPairPi1IsPR.
                       apply cTriplePi1IsPR.
                       apply eqIsPR.
               --- apply
                   compose2_2IsPR
                   with
                   (f := fun trace recs : nat =>
                           codeNth (trace - S (car (cTriplePi3 trace))) recs)
                   (g := fun trace recs : nat =>
                           codeNth (trace - S (cdr (cTriplePi3 trace))) recs).
                   apply
                     compose2_2IsPR
                     with
                     (f := fun trace recs : nat => trace - S (car (cTriplePi3 trace)))
                     (g := fun trace recs : nat => recs).
                   apply
                     filter10IsPR
                     with (g := fun trace : nat => trace - S (car (cTriplePi3 trace))).
                   apply
                     compose1_2IsPR
                     with
                     (f := fun trace : nat => trace)
                     (f' := fun trace : nat => S (car (cTriplePi3 trace))).
                   apply idIsPR.
                   apply
                     compose1_1IsPR with (f := fun trace : nat => car (cTriplePi3 trace)).
                   apply compose1_1IsPR.
                   apply cTriplePi3IsPR.
                   apply cPairPi1IsPR.
                   apply succIsPR.
                   apply minusIsPR.
                   apply pi2_2IsPR.
                   apply codeNthIsPR.
                   apply
                     compose2_2IsPR
                     with
                     (f := fun trace recs : nat => trace - S (cdr (cTriplePi3 trace)))
                     (g := fun trace recs : nat => recs).
                   apply
                     filter10IsPR
                     with (g := fun trace : nat => trace - S (cdr (cTriplePi3 trace))).
                   apply
                     compose1_2IsPR
                     with
                     (f := fun trace : nat => trace)
                     (f' := fun trace : nat => S (cdr (cTriplePi3 trace))).
                   apply idIsPR.
                   apply
                     compose1_1IsPR with (f := fun trace : nat => cdr (cTriplePi3 trace)).
                   apply compose1_1IsPR.
                   apply cTriplePi3IsPR.
                   apply cPairPi2IsPR.
                   apply succIsPR.
                   apply minusIsPR.
                   apply pi2_2IsPR.
                   apply codeNthIsPR.
                   apply multIsPR.
               --- apply multIsPR.
           ++ apply
               compose2_2IsPR
               with
               (f := fun trace recs : nat =>
                       charFunction 0
                         (Nat.eqb (cTriplePi2 trace)
                            (cPair 3
                               (cPair
                                  (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                                  (cTriplePi2 (cTriplePi3 trace)))) &&
                            Nat.eqb
                              (cTriple (cTriplePi1 (cTriplePi1 trace))
                                 (cTriplePi2 (cTriplePi1 trace))
                                 (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
                              (cTriplePi1 (cTriplePi3 trace))))
               (g := fun trace recs : nat => codeNth 
                                               (trace - 
                                                  S 
                                                    (cTriplePi3 trace)) recs).
              apply
                filter10IsPR
                with
                (g := fun trace : nat =>
                        charFunction 0
                          (Nat.eqb (cTriplePi2 trace)
                             (cPair 3
                                (cPair
                                   (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                                   (cTriplePi2 (cTriplePi3 trace)))) &&
                             Nat.eqb
                               (cTriple (cTriplePi1 (cTriplePi1 trace))
                                  (cTriplePi2 (cTriplePi1 trace))
                                  (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
                               (cTriplePi1 (cTriplePi3 trace)))).
              apply
                (andRelPR 1)
                with
                (R := fun trace : nat =>
                        Nat.eqb (cTriplePi2 trace)
                          (cPair 3
                             (cPair (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                                (cTriplePi2 (cTriplePi3 trace)))))
                (R' := fun trace : nat =>
                         Nat.eqb
                           (cTriple (cTriplePi1 (cTriplePi1 trace))
                              (cTriplePi2 (cTriplePi1 trace))
                              (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
                           (cTriplePi1 (cTriplePi3 trace))).
              apply
                compose1_2IsPR
                with
                (g := charFunction 2 Nat.eqb)
                (f := cTriplePi2)
                (f' := fun trace : nat =>
                         cPair 3
                           (cPair (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                              (cTriplePi2 (cTriplePi3 trace)))).
              apply cTriplePi2IsPR.
              apply
                compose1_2IsPR
                with
                (f := fun trace : nat => 3)
                (f' := fun trace : nat =>
                         cPair (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                           (cTriplePi2 (cTriplePi3 trace))).
              apply const1_NIsPR.
              apply
                compose1_2IsPR
                with
                (f := fun trace : nat =>
                        car (cdr (cTriplePi3 (cTriplePi1 trace))))
                (f' := fun trace : nat => cTriplePi2 (cTriplePi3 trace)).
              apply
                compose1_1IsPR
                with (f := fun trace : nat => cdr 
                                                (cTriplePi3
                                                   (cTriplePi1 trace))).
              apply
                compose1_1IsPR with (f := fun trace : nat => 
                                            cTriplePi3 (cTriplePi1 trace)).
              assumption.
              apply cPairPi2IsPR.
              apply cPairPi1IsPR.
              apply compose1_1IsPR.
              apply cTriplePi3IsPR.
              apply cTriplePi2IsPR.
              apply cPairIsPR.
              apply cPairIsPR.
              apply eqIsPR.
              apply
                compose1_2IsPR
                with
                (g := charFunction 2 Nat.eqb)
                (f := fun trace : nat =>
                        cTriple (cTriplePi1 (cTriplePi1 trace))
                          (cTriplePi2 (cTriplePi1 trace))
                          (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
                (f' := fun trace : nat => cTriplePi1 (cTriplePi3 trace)).
              apply
                compose1_3IsPR
                with
                (f1 := fun trace : nat => cTriplePi1 (cTriplePi1 trace))
                (f2 := fun trace : nat => cTriplePi2 (cTriplePi1 trace))
                (f3 := fun trace : nat =>
                         cdr (cdr (cTriplePi3 (cTriplePi1 trace)))).
              assumption.
              assumption.
              apply
                compose1_1IsPR
                with (f := fun trace : nat => cdr (cTriplePi3 (cTriplePi1 trace))).
              apply
                compose1_1IsPR with (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
              assumption.
              apply cPairPi2IsPR.
              apply cPairPi2IsPR.
              apply cTripleIsPR.
              apply compose1_1IsPR.
              apply cTriplePi3IsPR.
              apply cTriplePi1IsPR.
              apply eqIsPR.
              apply
                compose2_2IsPR
                with
                (f := fun trace recs : nat => trace - S (cTriplePi3 trace))
                (g := fun trace recs : nat => recs).
              apply
                filter10IsPR with (g := fun trace : nat => trace - S (cTriplePi3 trace)).
              apply
                compose1_2IsPR
                with
                (f := fun trace : nat => trace)
                (f' := fun trace : nat => S (cTriplePi3 trace)).
              apply idIsPR.
              apply compose1_1IsPR.
              apply cTriplePi3IsPR.
              apply succIsPR.
              apply minusIsPR.
              apply pi2_2IsPR.
              apply codeNthIsPR.
              apply multIsPR.
           ++ apply switchIsPR.
        -- apply switchIsPR.
      * apply
          compose2_2IsPR
          with
          (f := fun trace recs : nat =>
                  charFunction 0
                    (Nat.eqb (cTriplePi2 trace)
                       (cPair 2 (cTriplePi2 (cTriplePi3 trace))) &&
                       Nat.eqb
                         (cTriple (cTriplePi1 (cTriplePi1 trace))
                            (cTriplePi2 (cTriplePi1 trace))
                            (cdr (cTriplePi3 (cTriplePi1 trace))))
                         (cTriplePi1 (cTriplePi3 trace))))
          (g := fun trace recs : nat => codeNth (trace - S (cTriplePi3 trace)) recs).
        apply
          filter10IsPR
          with
          (g := fun trace : nat =>
                  charFunction 0
                    (Nat.eqb (cTriplePi2 trace)
                       (cPair 2 (cTriplePi2 (cTriplePi3 trace))) &&
                       Nat.eqb
                         (cTriple (cTriplePi1 (cTriplePi1 trace))
                            (cTriplePi2 (cTriplePi1 trace))
                            (cdr (cTriplePi3 (cTriplePi1 trace))))
                         (cTriplePi1 (cTriplePi3 trace)))).
        apply
          (andRelPR 1)
          with
          (R := fun trace : nat =>
                  Nat.eqb (cTriplePi2 trace)
                    (cPair 2 (cTriplePi2 (cTriplePi3 trace))))
          (R' := fun trace : nat =>
                   Nat.eqb
                     (cTriple (cTriplePi1 (cTriplePi1 trace))
                        (cTriplePi2 (cTriplePi1 trace))
                        (cdr (cTriplePi3 (cTriplePi1 trace))))
                     (cTriplePi1 (cTriplePi3 trace))).
        apply
          compose1_2IsPR
          with
          (g := charFunction 2 Nat.eqb)
          (f := fun trace : nat => cTriplePi2 trace)
          (f' := fun trace : nat => cPair 2 (cTriplePi2 (cTriplePi3 trace))).
        apply cTriplePi2IsPR.
        apply
          compose1_2IsPR
          with
          (f := fun trace : nat => 2)
          (f' := fun trace : nat => cTriplePi2 (cTriplePi3 trace)).
        apply const1_NIsPR.
        apply compose1_1IsPR.
        apply cTriplePi3IsPR.
        apply cTriplePi2IsPR.
        apply cPairIsPR.
        apply eqIsPR.
        apply
          compose1_2IsPR
          with
          (g := charFunction 2 Nat.eqb)
          (f := fun trace : nat =>
                  cTriple (cTriplePi1 (cTriplePi1 trace))
                    (cTriplePi2 (cTriplePi1 trace))
                    (cdr (cTriplePi3 (cTriplePi1 trace))))
          (f' := fun trace : nat => cTriplePi1 (cTriplePi3 trace)).
        apply
          compose1_3IsPR
          with
          (f1 := fun trace : nat => cTriplePi1 (cTriplePi1 trace))
          (f2 := fun trace : nat => cTriplePi2 (cTriplePi1 trace))
          (f3 := fun trace : nat => cdr (cTriplePi3 (cTriplePi1 trace))).
        assumption.
        assumption.
        apply
          compose1_1IsPR with (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
        assumption.
        apply cPairPi2IsPR.
        apply cTripleIsPR.
        apply compose1_1IsPR.
        apply cTriplePi3IsPR.
        apply cTriplePi1IsPR.
        apply eqIsPR.
        apply
          compose2_2IsPR
          with
          (f := fun trace recs : nat => trace - S (cTriplePi3 trace))
          (g := fun trace recs : nat => recs).
        apply
          filter10IsPR with (g := fun trace : nat => trace - S (cTriplePi3 trace)).
        apply
          compose1_2IsPR
          with
          (f := fun trace : nat => trace)
          (f' := fun trace : nat => S (cTriplePi3 trace)).
        apply idIsPR.
        apply compose1_1IsPR.
        apply cTriplePi3IsPR.
        apply succIsPR.
        apply minusIsPR.
        apply pi2_2IsPR.
        apply codeNthIsPR.
        apply multIsPR.
      * apply
          compose2_2IsPR
          with
          (f := fun trace recs : nat =>
                  charFunction 0
                    (Nat.eqb (cTriplePi2 trace)
                       (cPair 1
                          (cPair (cTriplePi2 (car (cTriplePi3 trace)))
                             (cTriplePi2 (cdr (cTriplePi3 trace))))) &&
                       (Nat.eqb
                          (cTriple (cTriplePi1 (cTriplePi1 trace))
                             (cTriplePi2 (cTriplePi1 trace))
                             (car (cdr (cTriplePi3 (cTriplePi1 trace)))))
                          (cTriplePi1 (car (cTriplePi3 trace))) &&
                          Nat.eqb
                            (cTriple (cTriplePi1 (cTriplePi1 trace))
                               (cTriplePi2 (cTriplePi1 trace))
                               (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
                            (cTriplePi1 (cdr (cTriplePi3 trace))))))
          (g := fun trace recs : nat =>
                  codeNth (trace - S (car (cTriplePi3 trace))) recs *
                    codeNth (trace - S (cdr (cTriplePi3 trace))) recs).
        apply
          filter10IsPR
          with
          (g := fun trace : nat =>
                  charFunction 0
                    (Nat.eqb (cTriplePi2 trace)
                       (cPair 1
                          (cPair (cTriplePi2 (car (cTriplePi3 trace)))
                             (cTriplePi2 (cdr (cTriplePi3 trace))))) &&
                       (Nat.eqb
                          (cTriple (cTriplePi1 (cTriplePi1 trace))
                             (cTriplePi2 (cTriplePi1 trace))
                             (car (cdr (cTriplePi3 (cTriplePi1 trace)))))
                          (cTriplePi1 (car (cTriplePi3 trace))) &&
                          Nat.eqb
                            (cTriple (cTriplePi1 (cTriplePi1 trace))
                               (cTriplePi2 (cTriplePi1 trace))
                               (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
                            (cTriplePi1 (cdr (cTriplePi3 trace)))))).
        apply
          (andRelPR 1)
          with
          (R := fun trace : nat =>
                  Nat.eqb (cTriplePi2 trace)
                    (cPair 1
                       (cPair (cTriplePi2 (car (cTriplePi3 trace)))
                          (cTriplePi2 (cdr (cTriplePi3 trace))))))
          (R' := fun trace : nat =>
                   Nat.eqb
                     (cTriple (cTriplePi1 (cTriplePi1 trace))
                        (cTriplePi2 (cTriplePi1 trace))
                        (car (cdr (cTriplePi3 (cTriplePi1 trace)))))
                     (cTriplePi1 (car (cTriplePi3 trace))) &&
                     Nat.eqb
                       (cTriple (cTriplePi1 (cTriplePi1 trace))
                          (cTriplePi2 (cTriplePi1 trace))
                          (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
                       (cTriplePi1 (cdr (cTriplePi3 trace)))).
        apply
          compose1_2IsPR
          with
          (g := charFunction 2 Nat.eqb)
          (f := fun trace : nat => cTriplePi2 trace)
          (f' := fun trace : nat =>
                   cPair 1
                     (cPair (cTriplePi2 (car (cTriplePi3 trace)))
                        (cTriplePi2 (cdr (cTriplePi3 trace))))).
        apply cTriplePi2IsPR.
        apply
          compose1_2IsPR
          with
          (f := fun trace : nat => 1)
          (f' := fun trace : nat =>
                   cPair (cTriplePi2 (car (cTriplePi3 trace)))
                     (cTriplePi2 (cdr (cTriplePi3 trace)))).
        apply const1_NIsPR.
        apply
          compose1_2IsPR
          with
          (f := fun trace : nat => cTriplePi2 (car (cTriplePi3 trace)))
          (f' := fun trace : nat => cTriplePi2 (cdr (cTriplePi3 trace))).
        apply
          compose1_1IsPR with (f := fun trace : nat => car (cTriplePi3 trace)).
        apply compose1_1IsPR.
        apply cTriplePi3IsPR.
        apply cPairPi1IsPR.
        apply cTriplePi2IsPR.
        apply
          compose1_1IsPR with (f := fun trace : nat => cdr (cTriplePi3 trace)).
        apply compose1_1IsPR.
        apply cTriplePi3IsPR.
        apply cPairPi2IsPR.
        apply cTriplePi2IsPR.
        apply cPairIsPR.
        apply cPairIsPR.
        apply eqIsPR.
        apply
          (andRelPR 1)
          with
          (R := fun trace : nat =>
                  Nat.eqb
                    (cTriple (cTriplePi1 (cTriplePi1 trace))
                       (cTriplePi2 (cTriplePi1 trace))
                       (car (cdr (cTriplePi3 (cTriplePi1 trace)))))
                    (cTriplePi1 (car (cTriplePi3 trace))))
          (R' := fun trace : nat =>
                   Nat.eqb
                     (cTriple (cTriplePi1 (cTriplePi1 trace))
                        (cTriplePi2 (cTriplePi1 trace))
                        (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
                     (cTriplePi1 (cdr (cTriplePi3 trace)))).
        apply
          compose1_2IsPR
          with
          (g := charFunction 2 Nat.eqb)
          (f := fun trace : nat =>
                  cTriple (cTriplePi1 (cTriplePi1 trace))
                    (cTriplePi2 (cTriplePi1 trace))
                    (car (cdr (cTriplePi3 (cTriplePi1 trace)))))
          (f' := fun trace : nat => cTriplePi1 (car (cTriplePi3 trace))).
        apply
          compose1_3IsPR
          with
          (f1 := fun trace : nat => cTriplePi1 (cTriplePi1 trace))
          (f2 := fun trace : nat => cTriplePi2 (cTriplePi1 trace))
          (f3 := fun trace : nat =>
                   car (cdr (cTriplePi3 (cTriplePi1 trace)))).
        assumption.
        assumption.
        apply
          compose1_1IsPR
          with (f := fun trace : nat => cdr (cTriplePi3 (cTriplePi1 trace))).
        apply
          compose1_1IsPR with (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
        assumption.
        apply cPairPi2IsPR.
        apply cPairPi1IsPR.
        apply cTripleIsPR.
        apply
          compose1_1IsPR with (f := fun trace : nat => car (cTriplePi3 trace)).
        apply compose1_1IsPR.
        apply cTriplePi3IsPR.
        apply cPairPi1IsPR.
        apply cTriplePi1IsPR.
        apply eqIsPR.
        apply
          compose1_2IsPR
          with
          (g := charFunction 2 Nat.eqb)
          (f := fun trace : nat =>
                  cTriple (cTriplePi1 (cTriplePi1 trace))
                    (cTriplePi2 (cTriplePi1 trace))
                    (cdr (cdr (cTriplePi3 (cTriplePi1 trace)))))
          (f' := fun trace : nat => cTriplePi1 (cdr (cTriplePi3 trace))).
        apply
          compose1_3IsPR
          with
          (f1 := fun trace : nat => cTriplePi1 (cTriplePi1 trace))
          (f2 := fun trace : nat => cTriplePi2 (cTriplePi1 trace))
          (f3 := fun trace : nat =>
                   cdr (cdr (cTriplePi3 (cTriplePi1 trace)))).
        assumption.
        assumption.
        apply
          compose1_1IsPR
          with (f := fun trace : nat => cdr (cTriplePi3 (cTriplePi1 trace))).
        apply
          compose1_1IsPR with (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
        assumption.
        apply cPairPi2IsPR.
        apply cPairPi2IsPR.
        apply cTripleIsPR.
        apply
          compose1_1IsPR with (f := fun trace : nat => cdr (cTriplePi3 trace)).
        apply compose1_1IsPR.
        apply cTriplePi3IsPR.
        apply cPairPi2IsPR.
        apply cTriplePi1IsPR.
        apply eqIsPR.
        apply
          compose2_2IsPR
          with
          (f := fun trace recs : nat =>
                  codeNth (trace - S (car (cTriplePi3 trace))) recs)
          (g := fun trace recs : nat =>
                  codeNth (trace - S (cdr (cTriplePi3 trace))) recs).
        apply
          compose2_2IsPR
          with
          (f := fun trace recs : nat => trace - S (car (cTriplePi3 trace)))
          (g := fun trace recs : nat => recs).
        apply
          filter10IsPR
          with (g := fun trace : nat => trace - S (car (cTriplePi3 trace))).
        apply
          compose1_2IsPR
          with
          (f := fun trace : nat => trace)
          (f' := fun trace : nat => S (car (cTriplePi3 trace))).
        apply idIsPR.
        apply
          compose1_1IsPR with (f := fun trace : nat => car (cTriplePi3 trace)).
        apply compose1_1IsPR.
        apply cTriplePi3IsPR.
        apply cPairPi1IsPR.
        apply succIsPR.
        apply minusIsPR.
        apply pi2_2IsPR.
        apply codeNthIsPR.
        apply
          compose2_2IsPR
          with
          (f := fun trace recs : nat => trace - S (cdr (cTriplePi3 trace)))
          (g := fun trace recs : nat => recs).
        apply
          filter10IsPR
          with (g := fun trace : nat => trace - S (cdr (cTriplePi3 trace))).
        apply
          compose1_2IsPR
          with
          (f := fun trace : nat => trace)
          (f' := fun trace : nat => S (cdr (cTriplePi3 trace))).
        apply idIsPR.
        apply
          compose1_1IsPR with (f := fun trace : nat => cdr (cTriplePi3 trace)).
        apply compose1_1IsPR.
        apply cTriplePi3IsPR.
        apply cPairPi2IsPR.
        apply succIsPR.
        apply minusIsPR.
        apply pi2_2IsPR.
        apply codeNthIsPR.
        apply multIsPR.
        apply multIsPR.
      * apply
          filter10IsPR
          with
          (g := fun trace : nat =>
                  charFunction 2 Nat.eqb (cTriplePi2 trace)
                    (cPair 0
                       (cPair
                          (codeSubTerm
                             (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                             (cTriplePi1 (cTriplePi1 trace))
                             (cTriplePi2 (cTriplePi1 trace)))
                          (codeSubTerm
                             (cdr (cdr (cTriplePi3 (cTriplePi1 trace))))
                             (cTriplePi1 (cTriplePi1 trace))
                             (cTriplePi2 (cTriplePi1 trace)))))).
        apply
          compose1_2IsPR
          with
          (f := fun trace : nat => cTriplePi2 trace)
          (f' := fun trace : nat =>
                   cPair 0
                     (cPair
                        (codeSubTerm
                           (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                           (cTriplePi1 (cTriplePi1 trace))
                           (cTriplePi2 (cTriplePi1 trace)))
                        (codeSubTerm
                           (cdr (cdr (cTriplePi3 (cTriplePi1 trace))))
                           (cTriplePi1 (cTriplePi1 trace))
                           (cTriplePi2 (cTriplePi1 trace))))).
        apply cTriplePi2IsPR.
        apply
          compose1_2IsPR
          with
          (f := fun trace : nat => 0)
          (f' := fun trace : nat =>
                   cPair
                     (codeSubTerm
                        (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                        (cTriplePi1 (cTriplePi1 trace))
                        (cTriplePi2 (cTriplePi1 trace)))
                     (codeSubTerm
                        (cdr (cdr (cTriplePi3 (cTriplePi1 trace))))
                        (cTriplePi1 (cTriplePi1 trace))
                        (cTriplePi2 (cTriplePi1 trace)))).
        apply const1_NIsPR.
        apply
          compose1_2IsPR
          with
          (f := fun trace : nat =>
                  codeSubTerm (car (cdr (cTriplePi3 (cTriplePi1 trace))))
                    (cTriplePi1 (cTriplePi1 trace)) 
                    (cTriplePi2 (cTriplePi1 trace)))
          (f' := fun trace : nat =>
                   codeSubTerm (cdr (cdr (cTriplePi3 (cTriplePi1 trace))))
                     (cTriplePi1 (cTriplePi1 trace)) 
                     (cTriplePi2 (cTriplePi1 trace))).
        apply
          compose1_3IsPR
          with
          (f1 := fun trace : nat =>
                   car (cdr (cTriplePi3 (cTriplePi1 trace))))
          (f2 := fun trace : nat => cTriplePi1 (cTriplePi1 trace))
          (f3 := fun trace : nat => cTriplePi2 (cTriplePi1 trace)).
        apply
          compose1_1IsPR
          with (f := fun trace : nat => cdr (cTriplePi3 (cTriplePi1 trace))).
        apply
          compose1_1IsPR with (f := fun trace : nat => cTriplePi3 
                                                         (cTriplePi1 trace)).
        assumption.
        apply cPairPi2IsPR.
        apply cPairPi1IsPR.
        assumption.
        assumption.
        apply codeSubTermIsPR.
        apply
          compose1_3IsPR
          with
          (f1 := fun trace : nat =>
                   cdr (cdr (cTriplePi3 (cTriplePi1 trace))))
          (f2 := fun trace : nat => cTriplePi1 (cTriplePi1 trace))
          (f3 := fun trace : nat => cTriplePi2 (cTriplePi1 trace)).
        apply
          compose1_1IsPR
          with (f := fun trace : nat => cdr (cTriplePi3 (cTriplePi1 trace))).
        apply
          compose1_1IsPR with (f := fun trace : nat => cTriplePi3 (cTriplePi1 trace)).
        assumption.
        apply cPairPi2IsPR.
        apply cPairPi2IsPR.
        assumption.
        assumption.
        apply codeSubTermIsPR.
        apply cPairIsPR.
        apply cPairIsPR.
        apply eqIsPR.
      * assumption.
Qed. 

Definition ReplaceTermTermsTerm : nat -> nat -> nat :=
  evalStrongRec 1
    (fun t recs s : nat =>
     cPair
       (switchPR (car t)
          (cPair (car t) (cdr (codeNth (t - S (cdr t)) recs)))
          (cPair 0 s))
       (switchPR t
          (S
             (cPair (car (codeNth (t - S (car (pred t))) recs))
                (cdr (codeNth (t - S (cdr (pred t))) recs)))) 0)).

Remark ReplaceTermTermsTermIsPR : isPR 2 ReplaceTermTermsTerm.
Proof.
  unfold ReplaceTermTermsTerm; apply evalStrongRecIsPR.
  apply
    compose3_2IsPR
    with
    (f1 := fun t recs s : nat =>
             switchPR (car t)
               (cPair (car t)
                  (cdr (codeNth (t - S (cdr t)) recs))) 
               (cPair 0 s))
    (f2 := fun t recs s : nat =>
             switchPR t
               (S
                  (cPair (car (codeNth (t - S (car (pred t))) recs))
                     (cdr (codeNth (t - S (cdr (pred t))) recs)))) 0).
  - apply compose3_3IsPR with
      (f1 := fun t recs s : nat => car t)
      (f2 := fun t recs s : nat =>
               cPair (car t) (cdr (codeNth (t - S (cdr t)) recs)))
      (f3 := fun t recs s : nat => cPair 0 s).
    + apply filter100IsPR with (g := cPairPi1).
      apply cPairPi1IsPR.
    + apply filter110IsPR with
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
                 --- apply cPairPi2IsPR.
                 --- apply succIsPR.
              ** apply minusIsPR.
           ++ apply pi2_2IsPR.
           ++ apply codeNthIsPR.
        -- apply cPairPi2IsPR.
      * apply cPairIsPR.
    + apply filter001IsPR with (g := fun s : nat => cPair 0 s).
      apply compose1_2IsPR with (f := fun s : nat => 0) (f' := fun s : nat => s).
      * apply const1_NIsPR.
      * apply idIsPR.
      * apply cPairIsPR.
    + apply switchIsPR.
  - apply filter110IsPR with
      (g := fun t recs : nat =>
              switchPR t
                (S
                   (cPair (car (codeNth (t - S (car (pred t))) recs))
                      (cdr (codeNth (t - S (cdr (pred t))) recs)))) 0).
    apply
      compose2_3IsPR
      with
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
              isPR 2 (fun t recs : nat => g (codeNth (t - S (g (pred t))) recs))).
        { intros g H; apply compose2_1IsPR with
            (f := fun t recs : nat => codeNth (t - S (g (pred t))) recs).
          - apply compose2_2IsPR with
              (f := fun t recs : nat => t - S (g (pred t)))
              (g := fun t recs : nat => recs).
            + apply filter10IsPR with (g := fun t : nat => t - S (g (pred t))).
              apply compose1_2IsPR with
                (f := fun t : nat => t) (f' := fun t : nat => S (g (pred t))).
              * apply idIsPR.
              * apply compose1_1IsPR with (f := fun t : nat => g (pred t)).
                -- apply compose1_1IsPR.
                   now apply predIsPR.
                   assumption.
                -- apply succIsPR.
              * apply minusIsPR.
            + apply pi2_2IsPR.
            + apply codeNthIsPR.
          - assumption. 
        } 
        apply compose2_2IsPR with
          (f := fun t recs : nat =>
                  car (codeNth (t - S (car (pred t))) recs))
          (g := fun t recs : nat =>
                  cdr (codeNth (t - S (cdr (pred t))) recs)).
        -- apply H, cPairPi1IsPR.
        -- apply H.
           apply cPairPi2IsPR.
        -- apply cPairIsPR.
      * apply succIsPR.
    + exists (composeFunc 2 0 (PRnil _) zeroFunc).
      simpl; auto.
    + apply switchIsPR.
  - apply cPairIsPR.
Qed.

Definition ReplaceTermTerm (t s : nat) : nat :=
  car (ReplaceTermTermsTerm t s).

Definition ReplaceTermsTerm (t s : nat) : nat :=
  cdr (ReplaceTermTermsTerm t s).

Lemma ReplaceTermTermIsPR : isPR 2 ReplaceTermTerm.
Proof.
  unfold ReplaceTermTerm; apply compose2_1IsPR.
  - apply ReplaceTermTermsTermIsPR.
  - apply cPairPi1IsPR.
Qed.

Lemma ReplaceTermsTermIsPR : isPR 2 ReplaceTermsTerm.
Proof.
  unfold ReplaceTermsTerm; apply compose2_1IsPR.
  - apply ReplaceTermTermsTermIsPR.
  - apply cPairPi2IsPR.
Qed.
 

Remark ReplaceTermTermsTermMonotone :
 forall a s1 s2 : nat,
 s1 <= s2 ->
 ReplaceTermTerm a s1 <= ReplaceTermTerm a s2 /\
 ReplaceTermsTerm a s1 <= ReplaceTermsTerm a s2.
Proof.
  assert
    (H: forall a s1 s2 n : nat,
        n < a ->
        s1 <= s2 ->
        ReplaceTermTerm n s1 <= ReplaceTermTerm n s2 /\
          ReplaceTermsTerm n s1 <= ReplaceTermsTerm n s2).
  { intro a; unfold ReplaceTermTerm, ReplaceTermsTerm, ReplaceTermTermsTerm.
    set (A :=
           fun t recs s : nat =>
             cPair
               (switchPR (car t)
                  (cPair (car t) (cdr (codeNth (t - S (cdr t)) recs)))
                  (cPair 0 s))
               (switchPR t
                  (S
                     (cPair (car (codeNth (t - S (car (pred t))) recs))
                        (cdr (codeNth (t - S (cdr (pred t))) recs)))) 0)).
    induction a as [| a Hreca]; simpl in |- *.  
    - intros s1 s2 n H; elim (Nat.nlt_0_r _ H).
    - intros s1 s2 n H H0; 
        assert (H1:
            forall n m : nat,
                m < n ->
                extEqual 1
                  (evalComposeFunc 1 1 (Vector.cons _ 
                                          (evalStrongRecHelp 1 A n) 0 
                                          (Vector.nil _))
                     (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 A m)).
      { intros n0 m H1; now apply (evalStrongRecHelp2 1). }
      simpl in H1; unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
      repeat rewrite computeEvalStrongRecHelp.
      unfold compose2, evalComposeFunc, evalOneParamList, evalList; simpl.
      repeat rewrite cPairProjections1; split.
      + unfold A at 3 1; repeat rewrite cPairProjections1.
        assert (H2: cPair (car n) (cdr n) = n) by apply cPairProjections.
        destruct (car n).
        * simpl in |- *.
          apply cPairLe3.
          apply le_n.
          assumption.
        * simpl; assert (H3: cdr n < n).
          { apply Nat.lt_le_trans with (cPair (S n0) (cdr n)).
            - apply cPairLt2.
            - rewrite H2; apply le_n.
          } 
          repeat rewrite H1.
      -- apply cPairLe3.
         apply le_n.
         eapply proj2.
         apply Hreca.
         ++ apply Nat.lt_le_trans with n.
            ** apply H3.
            ** apply Compat815.lt_n_Sm_le.
               assumption.
         ++ assumption.
      -- assumption.
      -- assumption.
      + unfold A at 3 1 in |- *.
        repeat rewrite cPairProjections2.
        destruct n.
        * simpl; apply le_n.
        * assert (H2: cdr n < S n).
          { apply Nat.lt_succ_r.
            apply Nat.le_trans with (cPair (car n) (cdr n)).
            - apply cPairLe2.
            - rewrite cPairProjections; apply le_n.
          } 
          assert (H3: car n < S n).
          { apply Nat.lt_succ_r.
            apply Nat.le_trans with (cPair (car n) (cdr n)).
            - apply cPairLe1.
            - rewrite cPairProjections; apply le_n.
          } 
          repeat rewrite H1.
          -- simpl; apply le_n_S.
             apply cPairLe3.
             eapply proj1.
             apply Hreca.
             apply Nat.le_lt_trans with n. 
             ++ lia.
             ++ apply Nat.succ_lt_mono.
                assumption.
             ++ assumption.
             ++ eapply proj2.
                apply Hreca.
                apply Nat.le_lt_trans with n. 
                ** lia.
                ** apply Nat.lt_succ_r.
                   assumption.
                ** assumption.
          -- assumption.
          -- assumption.
          -- assumption.
          -- assumption.
  }
  intros a s1 s2 H0;  apply H with (S a).
  - apply Nat.lt_succ_diag_r.
  - assumption.
Qed.

Lemma ReplaceTermTermMonotone :
  forall a s1 s2 : nat,
    s1 <= s2 -> ReplaceTermTerm a s1 <= ReplaceTermTerm a s2.
Proof.
  intros; eapply proj1; now apply ReplaceTermTermsTermMonotone.
Qed.


Lemma ReplaceTermsTermMonotone :
 forall a s1 s2 : nat,
 s1 <= s2 -> ReplaceTermsTerm a s1 <= ReplaceTermsTerm a s2.
Proof.
  intros; eapply proj2; now apply ReplaceTermTermsTermMonotone.
Qed.

Remark maxLemma :
 forall a b c d : nat, a <= b -> c <= d -> Nat.max a c <= Nat.max b d.
Proof. lia. Qed. 

Remark maxLemma2 :
  forall a b : list nat,
    fold_right Nat.max 0 a <= fold_right Nat.max 0 (a ++ b).
Proof.
  induction a as [| a a0 Hreca].
  - intros; simpl; apply Nat.le_0_l.
  - intro b; simpl; apply maxLemma. 
    + apply le_n.
    + apply Hreca.
Qed.

Remark maxLemma3 :
  forall a b : list nat,
    fold_right Nat.max 0 b <= fold_right Nat.max 0 (a ++ b).
Proof.
  intros a b; induction a as [| a a0 Hreca].
  - apply le_n.
  - simpl; apply Nat.le_trans with (fold_right Nat.max 0 (a0 ++ b)).
    + assumption.
    + apply Nat.le_max_r.
Qed.


Remark maxApp :
 forall a b : list nat,
 {fold_right Nat.max 0 (a ++ b) = fold_right Nat.max 0 a} +
 {fold_right Nat.max 0 (a ++ b) = fold_right Nat.max 0 b}.
Proof.
  intros a b; induction a as [| a a0 Hreca].
  - simpl; now right.  
  - simpl. 
    induction (Nat.max_dec a (fold_right max 0 (a0 ++ b))) as [a1 | b0]. 
    + rewrite a1; left; symmetry.
      apply Nat.max_l.
      apply Nat.le_trans with (max a (fold_right max 0 (a0 ++ b))).
      * apply Nat.le_trans with (max a (fold_right max 0 a0)).
        -- apply Nat.le_max_r.
        -- apply maxLemma.
           ++ apply le_n.
           ++ apply maxLemma2.
      * rewrite a1; apply le_n.
    + induction Hreca as [a1| b1].
      * rewrite a1; now left. 
      * rewrite b0, b1; now right.
Qed.

Lemma boundSubTerm :
 forall (t : fol.Term L) (v : nat) (s : fol.Term L),
 codeTerm (substT t v s) <=
 ReplaceTermTerm (codeTerm t)
   (fold_right Nat.max 0 (codeTerm s :: freeVarT t)).
Proof.
  intro t; unfold ReplaceTermTerm, ReplaceTermsTerm, ReplaceTermTermsTerm.
  set
    (A :=
       fun t0 recs s0 : nat =>
         cPair
           (switchPR (car t0)
              (cPair (car t0) (cdr (codeNth (t0 - S (cdr t0)) recs)))
              (cPair 0 s0))
           (switchPR t0
              (S
                 (cPair (car (codeNth (t0 - S (car (pred t0))) recs))
                    (cdr (codeNth (t0 - S (cdr (pred t0))) recs)))) 0)).
  assert
    (H: forall n m : nat,
        m < n ->
        extEqual 1
          (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 A n) 0 (Vector.nil _))
             (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 A m)) by
    (intros n m H; now apply (evalStrongRecHelp2 1)).
  simpl in H.
  elim t using
    Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             forall (v : nat) (s : fol.Term L),
               codeTerms (substTs ts v s) <=
                 ReplaceTermsTerm (codeTerms ts)
                   (fold_right Nat.max 0 (codeTerm s :: freeVarTs ts)));
    simpl in |- *; intros; unfold evalStrongRec in |- *;
    unfold evalComposeFunc, evalOneParamList, evalList in |- *;
    repeat rewrite computeEvalStrongRecHelp; unfold compose2 in |- *;
    unfold evalComposeFunc, evalOneParamList, evalList in |- *; 
    simpl in |- *; repeat rewrite cPairProjections1.
  - unfold A; simpl; repeat rewrite cPairProjections1.
    replace (codeTerm (var n)) with (cPair 0 n); [ idtac | reflexivity ].
    repeat rewrite cPairProjections1.
    simpl in |- *.
    destruct (eq_nat_dec v n) as [a | b].
    + eapply Nat.le_trans; [ idtac | apply cPairLe2 ].
      apply Nat.le_max_l.
    + replace (codeTerm (var n)) with (cPair 0 n); [ idtac | reflexivity ].
      apply cPairLe3.
      * apply le_n.
      * eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
        apply Nat.le_max_l.
  - unfold A; repeat rewrite cPairProjections1.
    replace (codeTerm (apply f t0)) with
      (cPair (S (cf f)) (codeTerms t0)); [ idtac | reflexivity ].
    repeat rewrite cPairProjections1.
    rewrite H with
      (m := 
         cdr
           (cPair (S (cf f))
              (codeTerms  t0))).
    + simpl; replace
               (codeTerm
                  (apply f 
                     (substTs t0 v s)))
        with
        (cPair (S (cf f))
           (codeTerms 
              (substTs t0 v s)));
        [ idtac | reflexivity ].
      apply cPairLe3.
      apply le_n.
      unfold ReplaceTermsTerm, ReplaceTermTermsTerm in H0.
      fold A in H0.
      repeat rewrite cPairProjections2.
      apply (H0 v s).
    +  repeat rewrite cPairProjections2; apply cPairLt2.
  - apply Nat.le_0_l.
  - replace
      (codeTerms 
         (Tcons (substT t0 v s) 
            (substTs t1 v s))) with
      (S
         (cPair (codeTerm (substT t0 v s))
            (codeTerms (substTs t1 v s))));
      [ idtac | reflexivity ].
    unfold ReplaceTermsTerm in |- *.
    unfold ReplaceTermsTerm in H1.
    unfold ReplaceTermTermsTerm in |- *.
    unfold ReplaceTermTermsTerm in H1.
    fold A in H1 |- *.
    unfold evalStrongRec in |- *.
    unfold evalComposeFunc, evalOneParamList, evalList in |- *.
    repeat rewrite computeEvalStrongRecHelp.
    unfold compose2, evalComposeFunc, evalOneParamList, evalList.
    simpl; repeat rewrite cPairProjections1.
    unfold A at 1 in |- *.
    repeat rewrite cPairProjections2.
    repeat rewrite H.
    * replace (codeTerms (Tcons t0 t1)) with
        (S (cPair (codeTerm t0) (codeTerms t1))); 
        [ idtac | reflexivity ].
      -- simpl; repeat rewrite cPairProjections1.
         apply le_n_S.
         apply cPairLe3.
         ++ eapply Nat.le_trans.
            ** apply H0.
            ** apply
                (ReplaceTermTermMonotone (codeTerm t0)
                   (Nat.max (codeTerm s) (fold_right Nat.max 0 (freeVarT t0)))
                   (Nat.max (codeTerm s)
                      (fold_right Nat.max 0 (freeVarTs (Tcons t0 t1))))).
               apply maxLemma.
               apply le_n.
               replace (freeVarTs (Tcons t0 t1)) with
                 (freeVarT t0 ++ freeVarTs t1); [ idtac | reflexivity ].
               apply maxLemma2.
         ++ eapply Nat.le_trans.
            ** apply H1.
            ** repeat rewrite cPairProjections2.
               apply
                 (ReplaceTermsTermMonotone (codeTerms t1)
                    (Nat.max (codeTerm s) (fold_right Nat.max 0 (freeVarTs t1)))
                    (Nat.max (codeTerm s)
                       (fold_right Nat.max 0 (freeVarTs (Tcons t0 t1))))).
               apply maxLemma.
               apply le_n.
               replace (freeVarTs (Tcons t0 t1)) with
                 (freeVarT t0 ++ freeVarTs  t1); [ idtac | reflexivity ].
               apply maxLemma3.
    * replace (codeTerms (Tcons t0 t1)) with
        (S (cPair (codeTerm t0) (codeTerms t1))); 
        [ idtac | reflexivity ].
      simpl; repeat rewrite cPairProjections2.
      apply Nat.lt_succ_r. 
      apply cPairLe2.
    * replace (codeTerms (Tcons t0 t1)) with
        (S (cPair (codeTerm t0) (codeTerms t1))); 
        [ idtac | reflexivity ].
    simpl; repeat rewrite cPairProjections1.
    apply Nat.lt_succ_r, cPairLe1.
Qed.

Lemma boundSubTerms :
  forall (n : nat) (ts : fol.Terms L n) (v : nat) (s : fol.Term L),
    codeTerms (substTs ts v s) <=
      ReplaceTermsTerm (codeTerms  ts)
        (fold_right Nat.max 0 (codeTerm s :: freeVarTs ts)).
Proof.
  intros n ts.
  unfold ReplaceTermTerm in |- *.
  unfold ReplaceTermsTerm in |- *.
  unfold ReplaceTermTermsTerm in |- *.
  set
    (A :=
       fun t0 recs s0 : nat =>
         cPair
           (switchPR (car t0)
              (cPair (car t0) (cdr (codeNth (t0 - S (cdr t0)) recs)))
              (cPair 0 s0))
           (switchPR t0
              (S
                 (cPair (car (codeNth (t0 - S (car (pred t0))) recs))
                    (cdr (codeNth (t0 - S (cdr (pred t0))) recs)))) 0))
    in *.
  assert
    (H: forall n m : nat,
        m < n ->
        extEqual 1
          (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 A n) 0 (Vector.nil _))
             (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 A m)).
  { intros n0 m; apply (evalStrongRecHelp2 1); assumption. } 
  simpl in H; induction ts as [| n t ts Hrects]; simpl in |- *.  
  - intros v s; apply Nat.le_0_l.
  - intros v s; 
      replace
        (codeTerms 
           (Tcons (substT t v s) (substTs ts v s))) with
      (S
         (cPair (codeTerm (substT t v s))
            (codeTerms (substTs ts v s))));
      [ idtac | reflexivity ].
    unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList;
      repeat rewrite computeEvalStrongRecHelp; unfold compose2;
      unfold evalComposeFunc, evalOneParamList, evalList;
      simpl in |- *; repeat rewrite cPairProjections1.
    unfold A at 1; repeat rewrite cPairProjections2; repeat rewrite H.
    + replace (codeTerms (Tcons t ts)) with
        (S (cPair (codeTerm t) (codeTerms ts))); 
        [ idtac | reflexivity ].
      simpl; repeat rewrite cPairProjections1.
      apply le_n_S; apply cPairLe3.
      * eapply Nat.le_trans.
        -- apply boundSubTerm.
        -- apply
            (ReplaceTermTermMonotone (codeTerm t)
               (Nat.max (codeTerm s) (fold_right Nat.max 0 (freeVarT t)))
               (Nat.max (codeTerm s)
                  (fold_right Nat.max 0 (freeVarTs (Tcons t ts))))).
           apply maxLemma.
           ++ apply le_n.
           ++ replace (freeVarTs (Tcons t ts)) 
                with
                (freeVarT t ++ freeVarTs ts); [ idtac | reflexivity ].
              apply maxLemma2.
      * eapply Nat.le_trans.
        -- apply Hrects.
        -- repeat rewrite cPairProjections2.
           apply
             (ReplaceTermsTermMonotone (codeTerms ts)
                (Nat.max (codeTerm s) (fold_right Nat.max 0 (freeVarTs ts)))
                (Nat.max (codeTerm s)
                   (fold_right Nat.max 0 (freeVarTs (Tcons t ts))))).
           apply maxLemma.
           ++ apply le_n.
           ++ replace (freeVarTs (Tcons t ts)) 
                with  (freeVarT t ++ freeVarTs ts); 
                [ idtac | reflexivity ].
              apply maxLemma3.
    + replace (codeTerms (Tcons t ts)) 
        with  (S (cPair (codeTerm t) (codeTerms ts))); 
        [ idtac | reflexivity ].
      simpl; repeat rewrite cPairProjections2.
      apply Nat.lt_succ_r.
      apply cPairLe2.
    + replace (codeTerms (Tcons t ts)) 
        with  (S (cPair (codeTerm t) (codeTerms  ts))); 
        [ idtac | reflexivity ].
      simpl; repeat rewrite cPairProjections1.
      apply Nat.lt_succ_r,  cPairLe1.
Qed.

Lemma ReplaceTermTermSub :
 forall (t : fol.Term L) (v w s2 : nat),
 ReplaceTermTerm (codeTerm (substT t v (var w))) s2 =
 ReplaceTermTerm (codeTerm t) s2.
Proof.
  intro t; 
    unfold ReplaceTermTerm,  ReplaceTermsTerm, ReplaceTermTermsTerm.
  set
    (A :=
       fun t0 recs s0 : nat =>
         cPair
           (switchPR (car t0)
              (cPair (car t0) (cdr (codeNth (t0 - S (cdr t0)) recs)))
              (cPair 0 s0))
           (switchPR t0
              (S
                 (cPair (car (codeNth (t0 - S (car (pred t0))) recs))
                    (cdr (codeNth (t0 - S (cdr (pred t0))) recs)))) 0)).
  assert
    (H: forall n m : nat,
        m < n ->
        extEqual 1
          (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 A n) 0 (Vector.nil _))
             (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 A m)).
  { intros n m H; apply (evalStrongRecHelp2 1); assumption. }
  simpl in H;
    elim t using
      Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             forall v w s2 : nat,
               ReplaceTermsTerm
                 (codeTerms  (substTs ts v (var w))) s2 =
                 ReplaceTermsTerm (codeTerms ts) s2); 
    simpl in |- *; intros; unfold evalStrongRec in |- *;
    unfold evalComposeFunc, evalOneParamList, evalList in |- *;
    repeat rewrite computeEvalStrongRecHelp; unfold compose2 in |- *;
    unfold evalComposeFunc, evalOneParamList, evalList in |- *; 
    simpl in |- *; repeat rewrite cPairProjections1.
  - induction (eq_nat_dec v n); 
      (replace (codeTerm (var n)) with (cPair 0 n); [ idtac | reflexivity ]).
    + replace (codeTerm (var w)) with (cPair 0 w); [ idtac | reflexivity ].
      unfold A at 3 1 in |- *.
      repeat rewrite cPairProjections1.
      simpl; reflexivity.
    + reflexivity.
  - replace
      (codeTerm
         (apply f
            (substTs t0 v (var w))))
      with
      (cPair (S (cf f))
         (codeTerms 
            (substTs t0 v (var w))));
      [ idtac | reflexivity ].
    unfold A at 3 1 in |- *.
    repeat rewrite cPairProjections1.
    replace (codeTerm (apply f t0)) with
      (cPair (S (cf f)) (codeTerms t0)); [ idtac | reflexivity ].
    repeat rewrite H.
    + repeat rewrite cPairProjections1.
      simpl; repeat rewrite cPairProjections2.
      replace
        (cdr
           (evalStrongRec 1 A
              (codeTerms 
                 (substTs t0 v (var w)))
              s2)) with
        (cdr
           (evalStrongRec 1 A (codeTerms t0) s2)); [reflexivity | ].
      symmetry; apply (H0 v w s2).
      + repeat rewrite cPairProjections2.
        apply cPairLt2.
      + repeat rewrite cPairProjections2.
        apply cPairLt2.
  - reflexivity.
  - unfold ReplaceTermsTerm;
      unfold ReplaceTermsTerm in H1.
    unfold ReplaceTermTermsTerm;
      unfold ReplaceTermTermsTerm in H1.
    fold A in H1 |- *.
    unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
    repeat rewrite computeEvalStrongRecHelp.
    unfold compose2, evalComposeFunc, evalOneParamList, evalList.
    simpl; repeat rewrite cPairProjections1.
    unfold A at 3 1; repeat rewrite cPairProjections2; repeat rewrite H.
    + replace
        (codeTerms 
           (Tcons (substT t0 v (var w))
              (substTs t1 v (var w)))) 
        with
        (S
           (cPair (codeTerm (substT t0 v (var w)))
              (codeTerms (substTs t1 v (var w)))));
        [ idtac | reflexivity ].
      replace (codeTerms (Tcons t0 t1)) 
        with
        (S (cPair (codeTerm t0) (codeTerms t1))); 
        [ idtac | reflexivity ].
      simpl;
        repeat rewrite cPairProjections2.
      replace
        (car
           (evalStrongRec 1 A
              (car (cPair (codeTerm t0) (codeTerms  t1))) s2)) 
        with
        (car
           (evalStrongRec 1 A
              (car
                 (cPair (codeTerm (substT t0 v (var w)))
                    (codeTerms (substTs t1 v (var w))))) s2)).
      * replace (cdr (evalStrongRec 1 A (codeTerms t1) s2)) 
          with
          (cdr
             (evalStrongRec 1 A
                (codeTerms  (substTs t1 v (var w))) s2)).
        -- reflexivity.
        -- apply (H1 v w s2).
      * repeat rewrite cPairProjections1.
        apply (H0 v w s2).
    + replace (codeTerms (Tcons t0 t1)) 
        with
        (S (cPair (codeTerm t0) (codeTerms  t1))); 
        [ idtac | reflexivity ].
      simpl; rewrite cPairProjections2.
      apply Nat.lt_succ_r.
      apply cPairLe2.
    + replace (codeTerms  (Tcons t0 t1)) 
        with
        (S (cPair (codeTerm t0) (codeTerms t1))); 
        [ idtac | reflexivity ].
      simpl; rewrite cPairProjections1; apply Nat.lt_succ_r.
      apply cPairLe1.
    + replace
        (codeTerms 
           (Tcons (substT t0 v (var w))
              (substTs t1 v (var w)))) 
        with
        (S
           (cPair (codeTerm (substT t0 v (var w)))
              (codeTerms (substTs t1 v (var w)))));
        [ idtac | reflexivity ].
      simpl; rewrite cPairProjections2; apply Nat.lt_succ_r.
      apply cPairLe2.
    + replace
        (codeTerms
           (Tcons (substT t0 v (var w))
              (substTs t1 v (var w)))) 
        with
        (S
           (cPair (codeTerm (substT t0 v (var w)))
              (codeTerms (substTs t1 v (var w)))));
        [ idtac | reflexivity ].
      simpl; rewrite cPairProjections1; apply Nat.lt_succ_r, cPairLe1.
Qed.

Lemma ReplaceTermsTermSub :
 forall (n : nat) (ts : fol.Terms L n) (v w s2 : nat),
 ReplaceTermsTerm (codeTerms  (substTs ts v (var w))) s2 =
 ReplaceTermsTerm (codeTerms ts) s2.
Proof.
  intros n ts; unfold ReplaceTermTerm, ReplaceTermsTerm, ReplaceTermTermsTerm.
  set
    (A :=
       fun t0 recs s0 : nat =>
         cPair
           (switchPR (car t0)
              (cPair (car t0) (cdr (codeNth (t0 - S (cdr t0)) recs)))
              (cPair 0 s0))
           (switchPR t0
              (S
                 (cPair (car (codeNth (t0 - S (car (pred t0))) recs))
                    (cdr (codeNth (t0 - S (cdr (pred t0))) recs)))) 0))
    in *.
  assert
    (H: forall n m : nat,
        m < n ->
        extEqual 1
          (evalComposeFunc 1 1 (Vector.cons _ 
                                  (evalStrongRecHelp 1 A n) 0 (Vector.nil _))
             (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 A m)).
  { intros n0 m ?; now apply (evalStrongRecHelp2 1). }
  simpl in H;  induction ts as [| n t ts Hrects]; simpl in |- *. 
  - reflexivity.
  - intros v w s2; unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList;
      repeat rewrite computeEvalStrongRecHelp; unfold compose2;
      unfold evalComposeFunc, evalOneParamList, evalList;
      simpl in |- *; repeat rewrite cPairProjections1.
    unfold A at 3 1; repeat rewrite cPairProjections2; repeat rewrite H.
    + replace
        (codeTerms
           (Tcons (substT t v (var w))
              (substTs ts v (var w)))) 
        with
        (S
           (cPair (codeTerm (substT t v (var w)))
              (codeTerms  (substTs ts v (var w)))));
        [ idtac | reflexivity ].
      replace (codeTerms  (Tcons t ts)) 
        with
        (S (cPair (codeTerm t) (codeTerms ts))); 
        [ idtac | reflexivity ].
      simpl; repeat rewrite cPairProjections2.
      replace
        (car
           (evalStrongRec 1 A
              (car (cPair (codeTerm t) (codeTerms ts))) s2)) 
        with
        (car
           (evalStrongRec 1 A
              (car
                 (cPair (codeTerm (substT t v (var w)))
                    (codeTerms (substTs ts v (var w))))) s2)).
      * replace (cdr (evalStrongRec 1 A (codeTerms ts) s2)) 
          with
          (cdr
             (evalStrongRec 1 A
                (codeTerms  (substTs ts v (var w))) s2)).
        -- reflexivity.
        -- apply (Hrects v w s2).
      * repeat rewrite cPairProjections1.
        apply (ReplaceTermTermSub t v w s2).
    + replace (codeTerms  (Tcons t ts)) 
        with
        (S (cPair (codeTerm t) (codeTerms ts))); 
        [ idtac | reflexivity ].
      simpl; rewrite cPairProjections2.
      apply Nat.lt_succ_r, cPairLe2.
    + replace (codeTerms (Tcons t ts)) 
        with
        (S (cPair (codeTerm t) (codeTerms ts))); 
        [ idtac | reflexivity ].
      simpl; rewrite cPairProjections1; apply Nat.lt_succ_r, cPairLe1.
    + replace
        (codeTerms 
           (Tcons (substT t v (var w))
              (substTs ts v (var w)))) with
        (S
           (cPair (codeTerm (substT t v (var w)))
              (codeTerms (substTs ts v (var w)))));
        [ idtac | reflexivity ].
      simpl; rewrite cPairProjections2; apply Nat.lt_succ_r, cPairLe2.
    + replace
        (codeTerms 
           (Tcons (substT t v (var w))
              (substTs ts v (var w)))) 
        with
        (S
           (cPair (codeTerm (substT t v (var w)))
              (codeTerms (substTs ts v (var w)))));
        [ idtac | reflexivity ].
      simpl; rewrite cPairProjections1; apply Nat.lt_succ_r, cPairLe1.
Qed.

Definition ReplaceFormulaTerm : nat -> nat -> nat :=
  evalStrongRec 1
    (fun f recs s : nat =>
     switchPR (car f)
       (switchPR (pred (car f))
          (switchPR (pred (pred (car f)))
             (switchPR (pred (pred (pred (car f))))
                (cPair (car f) (ReplaceTermsTerm (cdr f) s))
                (cPair 3
                   (cPair s (codeNth (f - S (cdr (cdr f))) recs))))
             (cPair 2 (codeNth (f - S (cdr f)) recs)))
          (cPair 1
             (cPair (codeNth (f - S (car (cdr f))) recs)
                (codeNth (f - S (cdr (cdr f))) recs))))
       (cPair 0
          (cPair (ReplaceTermTerm (car (cdr f)) s)
             (ReplaceTermTerm (cdr (cdr f)) s)))).

Lemma ReplaceFormulaTermIsPR : isPR 2 ReplaceFormulaTerm.
Proof.
  unfold ReplaceFormulaTerm; apply evalStrongRecIsPR.
  apply
    compose3_3IsPR
    with
    (f1 := fun f recs s : nat => car f)
    (f2 := fun f recs s : nat =>
             switchPR (pred (car f))
               (switchPR (pred (pred (car f)))
                  (switchPR (pred (pred (pred (car f))))
                     (cPair (car f) (ReplaceTermsTerm (cdr f) s))
                     (cPair 3
                        (cPair s (codeNth (f - S (cdr (cdr f))) recs))))
                  (cPair 2 (codeNth (f - S (cdr f)) recs)))
               (cPair 1
                  (cPair (codeNth (f - S (car (cdr f))) recs)
                     (codeNth (f - S (cdr (cdr f))) recs))))
    (f3 := fun f recs s : nat =>
             cPair 0
               (cPair (ReplaceTermTerm (car (cdr f)) s)
                  (ReplaceTermTerm (cdr (cdr f)) s))).
  - apply filter100IsPR.
    apply cPairPi1IsPR.
  - apply compose3_3IsPR with
      (f1 := fun f recs s : nat => pred (car f))
      (f2 := fun f recs s : nat =>
               switchPR (pred (pred (car f)))
                 (switchPR (pred (pred (pred (car f))))
                    (cPair (car f) (ReplaceTermsTerm (cdr f) s))
                    (cPair 3
                       (cPair s (codeNth (f - S (cdr (cdr f))) recs))))
                 (cPair 2 (codeNth (f - S (cdr f)) recs)))
      (f3 := fun f recs s : nat =>
               cPair 1
                 (cPair (codeNth (f - S (car (cdr f))) recs)
                    (codeNth (f - S (cdr (cdr f))) recs))).
    + apply filter100IsPR with (g := fun f : nat => pred (car f)).
      apply compose1_1IsPR.
      * apply cPairPi1IsPR.
      * apply predIsPR.
    + apply compose3_3IsPR with
        (f1 := fun f recs s : nat => pred (pred (car f)))
        (f2 := fun f recs s : nat =>
                 switchPR (pred (pred (pred (car f))))
                   (cPair (car f) (ReplaceTermsTerm (cdr f) s))
                   (cPair 3
                      (cPair s (codeNth (f - S (cdr (cdr f))) recs))))
        (f3 := fun f recs s : nat => cPair 2 (codeNth (f - S (cdr f)) recs)).
      * apply filter100IsPR with (g := fun f : nat => pred (pred (car f))).
        apply compose1_1IsPR with (f := fun f : nat => pred (car f)).
        -- apply compose1_1IsPR.
           ++ apply cPairPi1IsPR.
           ++ apply predIsPR.
        -- apply predIsPR.
      * apply compose3_3IsPR with
          (f1 := fun f recs s : nat => pred (pred (pred (car f))))
          (f2 := fun f recs s : nat =>
                   cPair (car f) (ReplaceTermsTerm (cdr f) s))
          (f3 := fun f recs s : nat =>
                   cPair 3 (cPair s (codeNth (f - S (cdr (cdr f))) recs))).
        -- apply filter100IsPR with (g := fun f : nat => pred (pred (pred (car f)))).
           apply compose1_1IsPR with (f := fun f : nat => pred (pred (car f))).
           ++ apply compose1_1IsPR with (f := fun f : nat => pred (car f)).
              ** apply compose1_1IsPR.
                 apply cPairPi1IsPR.
                 apply predIsPR.
              ** apply predIsPR.
           ++ apply predIsPR.
        -- apply  filter101IsPR with
             (g := fun f s : nat =>
                     cPair (car f) (ReplaceTermsTerm (cdr f) s)).
           apply
             compose2_2IsPR
             with
             (f := fun f s : nat => car f)
             (g := fun f s : nat => ReplaceTermsTerm (cdr f) s).
           ++ apply filter10IsPR.
              apply cPairPi1IsPR.
           ++ apply  compose2_2IsPR with 
                (f := fun f s : nat => cdr f) (g := fun f s : nat => s).
              ** apply filter10IsPR.
                 apply cPairPi2IsPR.
              ** apply pi2_2IsPR.
              ** apply ReplaceTermsTermIsPR.
           ++ apply cPairIsPR.
        -- apply compose3_2IsPR with
             (f1 := fun f recs s : nat => 3)
             (f2 := fun f recs s : nat =>
                      cPair s (codeNth (f - S (cdr (cdr f))) recs)).
           ++ apply filter100IsPR with (g := fun _ : nat => 3).
              apply const1_NIsPR.
           ++ apply  compose3_2IsPR with
                (f1 := fun f recs s : nat => s)
                (f2 := fun f recs s : nat => codeNth (f - S (cdr (cdr f))) recs).
              ** apply pi3_3IsPR.
              ** apply filter110IsPR with
                   (g := fun f recs : nat => codeNth (f - S (cdr (cdr f))) recs).
                 apply compose2_2IsPR with
                   (f := fun f recs : nat => f - S (cdr (cdr f)))
                   (g := fun f recs : nat => recs).
                 apply filter10IsPR with (g := fun f : nat => f - S (cdr (cdr f))).
                 apply
                   compose1_2IsPR
                   with
                   (f := fun f : nat => f)
                   (f' := fun f : nat => S (cdr (cdr f))).
                 apply idIsPR.
                 apply compose1_1IsPR with (f := fun f : nat => cdr (cdr f)).
                 apply compose1_1IsPR.
                 apply cPairPi2IsPR.
                 apply cPairPi2IsPR.
                 apply succIsPR.
                 apply minusIsPR.
                 apply pi2_2IsPR.
                 apply codeNthIsPR.
              ** apply cPairIsPR.
           ++ apply cPairIsPR.
        -- apply switchIsPR.
      * apply filter110IsPR  with 
          (g := fun f recs : nat => cPair 2 (codeNth (f - S (cdr f)) recs)).
        apply
          compose2_2IsPR
          with
          (f := fun f recs : nat => 2)
          (g := fun f recs : nat => codeNth (f - S (cdr f)) recs).
        -- apply filter10IsPR with (g := fun _ : nat => 2).
           apply const1_NIsPR.
        -- apply compose2_2IsPR with
             (f := fun f recs : nat => f - S (cdr f))
             (g := fun f recs : nat => recs).
           ++ apply filter10IsPR with (g := fun f : nat => f - S (cdr f)).
              apply
                compose1_2IsPR
                with (f := fun f : nat => f) (f' := fun f : nat => S (cdr f)).
              ** apply idIsPR.
              ** apply compose1_1IsPR.
                 apply cPairPi2IsPR.
                 apply succIsPR.
              ** apply minusIsPR.
           ++ apply pi2_2IsPR.
           ++ apply codeNthIsPR.
        -- apply cPairIsPR.
      * apply switchIsPR.
    + apply filter110IsPR with
             (g := fun f recs : nat =>
                     cPair 1
                       (cPair (codeNth (f - S (car (cdr f))) recs)
                          (codeNth (f - S (cdr (cdr f))) recs))).
      apply
        compose2_2IsPR
        with
        (f := fun f recs : nat => 1)
        (g := fun f recs : nat =>
                cPair (codeNth (f - S (car (cdr f))) recs)
                  (codeNth (f - S (cdr (cdr f))) recs)).
      * apply filter10IsPR with (g := fun _ : nat => 1).
        apply const1_NIsPR.
      * apply compose2_2IsPR with
          (f := fun f recs : nat => codeNth (f - S (car (cdr f))) recs)
          (g := fun f recs : nat => codeNth (f - S (cdr (cdr f))) recs).
        -- apply compose2_2IsPR with
             (f := fun f recs : nat => f - S (car (cdr f)))
             (g := fun f recs : nat => recs).
           ++ apply filter10IsPR with (g := fun f : nat => f - S (car (cdr f))).
              apply compose1_2IsPR with
                (f := fun f : nat => f)
                (f' := fun f : nat => S (car (cdr f))).
              ** apply idIsPR.
              ** apply compose1_1IsPR with (f := fun f : nat => car (cdr f)).
                 apply compose1_1IsPR.
                 apply cPairPi2IsPR.
                 apply cPairPi1IsPR.
                 apply succIsPR.
              ** apply minusIsPR.
           ++ apply pi2_2IsPR.
           ++ apply codeNthIsPR.
        -- apply compose2_2IsPR with
             (f := fun f recs : nat => f - S (cdr (cdr f)))
             (g := fun f recs : nat => recs).
           ++ apply filter10IsPR with (g := fun f : nat => f - S (cdr (cdr f))).
              apply compose1_2IsPR with
                (f := fun f : nat => f)
                (f' := fun f : nat => S (cdr (cdr f))).
              ** apply idIsPR.
              ** apply compose1_1IsPR with (f := fun f : nat => cdr (cdr f)).
                 apply compose1_1IsPR.
                 apply cPairPi2IsPR.
                 apply cPairPi2IsPR.
                 apply succIsPR.
              ** apply minusIsPR.
           ++ apply pi2_2IsPR.
           ++ apply codeNthIsPR.
        -- apply cPairIsPR.
      * apply cPairIsPR.
    + apply switchIsPR.
  - apply filter101IsPR with
      (g := fun f s : nat =>
              cPair 0
                (cPair (ReplaceTermTerm (car (cdr f)) s)
                   (ReplaceTermTerm (cdr (cdr f)) s))).
    apply
      compose2_2IsPR
      with
      (f := fun f s : nat => 0)
      (g := fun f s : nat =>
              cPair (ReplaceTermTerm (car (cdr f)) s)
                (ReplaceTermTerm (cdr (cdr f)) s)).
    + apply filter10IsPR with (g := fun _ : nat => 0).
      apply const1_NIsPR.
    + apply compose2_2IsPR with
        (f := fun f s : nat => ReplaceTermTerm (car (cdr f)) s)
        (g := fun f s : nat => ReplaceTermTerm (cdr (cdr f)) s).
      * apply compose2_2IsPR with
          (f := fun f s : nat => car (cdr f))
          (g := fun f s : nat => s).
        -- apply filter10IsPR with (g := fun f : nat => car (cdr f)).
           apply compose1_1IsPR.
           ++ apply cPairPi2IsPR.
           ++ apply cPairPi1IsPR.
        -- apply pi2_2IsPR.
        -- apply ReplaceTermTermIsPR.
      * apply compose2_2IsPR with
          (f := fun f s : nat => cdr (cdr f))
          (g := fun f s : nat => s).
        -- apply filter10IsPR with (g := fun f : nat => cdr (cdr f)).
           apply compose1_1IsPR.
           ++ apply cPairPi2IsPR.
           ++ apply cPairPi2IsPR.
        -- apply pi2_2IsPR.
        -- apply ReplaceTermTermIsPR.
      * apply cPairIsPR.
    + apply cPairIsPR.
  - apply switchIsPR.
Qed.

Lemma ReplaceFormulaTermMonotone :
  forall a s1 s2 : nat,
    s1 <= s2 -> ReplaceFormulaTerm a s1 <= ReplaceFormulaTerm a s2.
Proof.
  assert
    (H: forall a s1 s2 n : nat,
        n < a -> s1 <= s2 -> ReplaceFormulaTerm n s1 <= ReplaceFormulaTerm n s2).
  { unfold ReplaceFormulaTerm in |- *.
    set
      (A :=
         fun f recs s : nat =>
           switchPR (car f)
             (switchPR (pred (car f))
                (switchPR (pred (pred (car f)))
                   (switchPR (pred (pred (pred (car f))))
                      (cPair (car f) (ReplaceTermsTerm (cdr f) s))
                      (cPair 3
                         (cPair s (codeNth (f - S (cdr (cdr f))) recs))))
                   (cPair 2 (codeNth (f - S (cdr f)) recs)))
                (cPair 1
                   (cPair (codeNth (f - S (car (cdr f))) recs)
                      (codeNth (f - S (cdr (cdr f))) recs))))
             (cPair 0
                (cPair (ReplaceTermTerm (car (cdr f)) s)
                   (ReplaceTermTerm (cdr (cdr f)) s)))).
    assert
      (H: forall n m : nat,
          m < n ->
          extEqual 1
            (evalComposeFunc 1 1 (Vector.cons _ 
                                    (evalStrongRecHelp 1 A n) 0 (Vector.nil _))
               (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 A m)).
    { intros n m H; now apply (evalStrongRecHelp2 1). }
    simpl in H; simple induction a.
    - intros s1 s2 n H0 H1; elim (Nat.nlt_0_r _ H0).
    - intros n H0 s1 s2 n0 H1 H2.
      assert (H1': n0 <= n) by lia.
      rewrite  Nat.lt_eq_cases in H1'; destruct H1' as [H3 | H3 ].
      + apply H0. 
        * apply H3. 
        * apply H2. 
      + unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
        repeat rewrite computeEvalStrongRecHelp.
        unfold compose2, evalComposeFunc, evalOneParamList, evalList.
        simpl; repeat rewrite cPairProjections1.
        unfold A at 3 1 in |- *; destruct n0.
        * simpl; apply cPairLe3.
          apply le_n.
          apply cPairLe3; apply ReplaceTermTermMonotone; assumption.
        * assert (H4: cPair (car (S n0)) (cdr (S n0)) = S n0) by
            apply cPairProjections.
          destruct (car (S n0)).
          -- simpl; apply cPairLe3.
             ++ apply le_n.
             ++ apply cPairLe3; apply ReplaceTermTermMonotone; assumption.
          -- assert (H5: cdr (S n0) < S n0).
             { apply Nat.lt_le_trans with (cPair (S n1) (cdr (S n0))).
               - apply cPairLt2.
               - rewrite H4; apply le_n.
             } 
             assert (H6: car (cdr (S n0)) < S n0).
             { apply Nat.le_lt_trans with (cdr (S n0)).
               - apply Nat.le_trans with 
                   (cPair (car (cdr (S n0))) (cdr (cdr (S n0)))).
                 + apply cPairLe1.
                 + rewrite cPairProjections; apply le_n.
               - assumption.
             } 
             assert (H7: cdr (cdr (S n0)) < S n0).
             { apply Nat.le_lt_trans with (cdr (S n0)).
               - apply Nat.le_trans with 
                   (cPair (car (cdr (S n0))) (cdr (cdr (S n0)))).
                 + apply cPairLe2.
                 + rewrite cPairProjections; apply le_n.
               - assumption.
             } 
             destruct n1.
          ++ repeat rewrite H with (m := car (cdr (S n0))); try assumption.
             repeat rewrite H with (m := cdr (cdr (S n0))); try assumption.
             simpl; apply cPairLe3.
             ** apply le_n.
             ** apply cPairLe3.
                apply H0.
                rewrite <- H3.
                assumption.
                assumption.
                apply H0.
                rewrite <- H3.
                assumption.
                assumption.
          ++ destruct n1.
             ** repeat rewrite H with (m := cdr (S n0)); try assumption.
                simpl; apply cPairLe3.
                apply le_n.
                apply H0.
                rewrite <- H3.
                assumption.
                assumption.
             ** destruct n1.
                repeat rewrite H with (m := cdr (cdr (S n0))); try assumption.
                simpl; apply cPairLe3.
                apply le_n.
                apply cPairLe3.
                assumption.
                apply H0.
                rewrite <- H3.
                assumption.
                assumption.
                simpl; apply cPairLe3.
                apply le_n.
                apply ReplaceTermsTermMonotone.
                assumption.
  }  
  intros a s1 s2 H0; apply (H (S a)); auto.
Qed.

Fixpoint varFormula (f : fol.Formula L) : list nat :=
  match f with
  | equal t s => freeVarT t ++ freeVarT s
  | atomic r ts => freeVarTs ts
  | impH A B => varFormula A ++ varFormula B
  | notH A => varFormula A
  | forallH v A => v :: varFormula A
  end.


Lemma ReplaceFormulaTermSub :
  forall (f : fol.Formula L) (v w s2 : nat),
    ReplaceFormulaTerm (codeFormula (substF f v (var w))) s2 =
      ReplaceFormulaTerm (codeFormula f) s2.
Proof.
  intro f; unfold ReplaceFormulaTerm;
    set
      (A :=
         fun f0 recs s0 : nat =>
           switchPR (car f0)
             (switchPR (pred (car f0))
                (switchPR (pred (pred (car f0)))
                   (switchPR (pred (pred (pred (car f0))))
                      (cPair (car f0) (ReplaceTermsTerm (cdr f0) s0))
                      (cPair 3
                         (cPair s0 (codeNth (f0 - S (cdr (cdr f0))) recs))))
                   (cPair 2 (codeNth (f0 - S (cdr f0)) recs)))
                (cPair 1
                   (cPair (codeNth (f0 - S (car (cdr f0))) recs)
                      (codeNth (f0 - S (cdr (cdr f0))) recs))))
             (cPair 0
                (cPair (ReplaceTermTerm (car (cdr f0)) s0)
                   (ReplaceTermTerm (cdr (cdr f0)) s0)))).
  assert
    (H: forall n m : nat,
        m < n ->
        extEqual 1
          (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 A n) 0 (Vector.nil _))
             (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 A m)).
  { intros n m H; apply (evalStrongRecHelp2 1); assumption. }
  simpl in H; elim f using Formula_depth_ind2; clear f.  
  - intros t t0 v w s2; simpl; unfold evalStrongRec, evalComposeFunc, 
      evalOneParamList, evalList. 
    repeat rewrite computeEvalStrongRecHelp.
    unfold compose2, evalComposeFunc, evalOneParamList, evalList in |- *.
    simpl; repeat rewrite cPairProjections1.
    unfold A at 3 1;
      repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    simpl; repeat rewrite ReplaceTermTermSub.
    reflexivity.
  - intros r t v w s2; simpl; unfold evalStrongRec in |- *.
    unfold evalComposeFunc, evalOneParamList, evalList in |- *.
    repeat rewrite computeEvalStrongRecHelp.
    unfold compose2 in |- *.
    unfold evalComposeFunc, evalOneParamList, evalList in |- *.
    simpl in |- *.
    repeat rewrite cPairProjections1.
    unfold A at 3 1 in |- *.
    repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    simpl in |- *.
    rewrite ReplaceTermsTermSub.
    reflexivity.
  -  intros f H0 f0 H1 v w s2; simpl in |- *.
     unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
     repeat rewrite computeEvalStrongRecHelp.
     unfold compose2, evalComposeFunc, evalOneParamList, evalList.
     simpl; repeat rewrite cPairProjections1.
     repeat rewrite subFormulaImp.
     simpl; unfold A at 3 1.
     repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
     rewrite H with (m := codeFormula (substF f v (var w))).
     + rewrite H with (m := codeFormula (substF f0 v (var w))).
       * rewrite H with (m := codeFormula f).
         -- rewrite H with (m := codeFormula f0).
            ++ simpl; rewrite H0.
               rewrite H1; reflexivity.
            ++ apply Nat.le_lt_trans with (cPair (codeFormula f) (codeFormula f0)).
               ** apply cPairLe2.
               ** apply cPairLt2.
         -- apply Nat.le_lt_trans with (cPair (codeFormula f) (codeFormula f0)).
            ++ apply cPairLe1.
            ++ apply cPairLt2.
       * apply Nat.le_lt_trans with
           (cPair (codeFormula (substF f v (var w)))
              (codeFormula (substF f0 v (var w)))).
         -- apply cPairLe2.
         -- apply cPairLt2.
     + apply Nat.le_lt_trans with
         (cPair (codeFormula (substF f v (var w)))
            (codeFormula (substF f0 v (var w)))).
       * apply cPairLe1.
       * apply cPairLt2.
  - intros f H0 v w s2; simpl.
    unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
    repeat rewrite computeEvalStrongRecHelp.
    unfold compose2, evalComposeFunc, evalOneParamList, evalList.
    simpl; repeat rewrite cPairProjections1.
    repeat rewrite subFormulaNot.
    simpl; unfold A at 3 1;
      repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    rewrite H with (m := codeFormula (substF f v (var w))).
    rewrite H with (m := codeFormula f).
    simpl; rewrite H0.
    reflexivity.
    apply cPairLt2.
    apply cPairLt2.
  - intros v a H0 v0 w s2; rewrite subFormulaForall.
    induction (eq_nat_dec v v0) as [a0 | ?].
    + reflexivity.
    + induction (In_dec eq_nat_dec v (freeVarT (var w))) as [a0 | ?].
      * simpl; unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
        repeat rewrite computeEvalStrongRecHelp.
        unfold compose2, evalComposeFunc, evalOneParamList, evalList.
        simpl; repeat rewrite cPairProjections1.
        simpl; unfold A at 3 1 in |- *.
        repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
        rewrite
          H
          with
          (m := 
             codeFormula
               (substF 
                  (substF a v
                     (var
                        (newVar (v0 :: freeVarT (L:=L) (var w) ++ freeVarF a))))
                  v0 (var w))).
        -- rewrite H with (m := codeFormula a).
           simpl; rewrite H0.
           rewrite H0.
           reflexivity.
           apply depthForall.
           apply eqDepth with a.
           symmetry  in |- *.
           apply subFormulaDepth.
           apply depthForall.
           apply Nat.le_lt_trans with (cPair v (codeFormula a)).
           apply cPairLe2.
           apply cPairLt2.
        -- apply Nat.le_lt_trans with
             (cPair (newVar (v0 :: freeVarT (L:=L) (var w) ++ freeVarF a))
                (codeFormula
                   (substF 
                      (substF a v
                         (var
                            (newVar
                               (v0 :: freeVarT (L:=L) (var w) ++ freeVarF a))))
                      v0 (var w)))).
           ++ apply cPairLe2.
           ++ apply cPairLt2.
      * simpl;
          unfold evalStrongRec,  evalComposeFunc, evalOneParamList, evalList.
        repeat rewrite computeEvalStrongRecHelp.
        unfold compose2, evalComposeFunc, evalOneParamList, evalList.
        simpl; repeat rewrite cPairProjections1.
        simpl; unfold A at 3 1;
          repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
        rewrite H with (m := codeFormula (substF a v0 (var w))).
        -- rewrite H with (m := codeFormula a).
           ++ simpl; rewrite H0. 
              ** reflexivity.
              ** apply depthForall.
           ++ apply Nat.le_lt_trans with (cPair v (codeFormula a)).
              ** apply cPairLe2.
              ** apply cPairLt2.
        -- apply Nat.le_lt_trans with
             (cPair v (codeFormula (substF a v0 (var w)))).
           ++ apply cPairLe2.
           ++ apply cPairLt2.
Qed.

Remark codeTermFreeVar :
 forall s : fol.Term L, fold_right Nat.max 0 (freeVarT s) <= codeTerm s.
Proof.
  intros s; elim s using
              Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             fold_right Nat.max 0 (freeVarTs ts) <= 
               codeTerms ts);
    simpl.
  - intros n; apply Nat.max_case.
    + unfold codeTerm, code.codeTerm; apply cPairLe2.
    + apply Nat.le_0_l.
  - intros f t H; apply Nat.le_trans with (codeTerms  t).
    + assumption.
    + unfold codeTerm,  code.codeTerm; apply cPairLe2.
  - apply Nat.le_0_l. 
  - intros n t H t0 H0; replace (freeVarTs (Tcons t t0)) 
      with
      (freeVarT t ++ freeVarTs t0); [ idtac | reflexivity ].
    replace (codeTerms  (Tcons t t0))
      with
      (S (cPair (codeTerm t) (codeTerms t0))); 
      [ idtac | reflexivity ].
    induction (maxApp (freeVarT t) (freeVarTs t0)) as [a | b].
    + rewrite a.
      eapply Nat.le_trans.
      * apply H.
      * apply le_S.
        apply cPairLe1.
    + rewrite b.
      eapply Nat.le_trans.
      * apply H0.
      * apply le_S.
        apply cPairLe2.
Qed.

Remark maxVarFreeVar :
 forall f : fol.Formula L,
   fold_right Nat.max 0 (freeVarF f) <=
     fold_right Nat.max 0 (varFormula f).
Proof.
  intros f;
    induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
    simpl.
  - apply le_n.
  - apply le_n.
  - induction (maxApp (freeVarF f1) (freeVarF f0)).
    + rewrite a.
      eapply Nat.le_trans.
      * apply Hrecf1.
      * apply maxLemma2.
    + rewrite b.
      eapply Nat.le_trans.
      * apply Hrecf0.
      * apply maxLemma3.
  - assumption.
  - apply Nat.le_trans with (fold_right Nat.max 0 (freeVarF f)).
    + clear Hrecf.
      induction (freeVarF f).
      * simpl in |- *.
        apply Nat.le_0_l.
      * simpl in |- *.
        induction (eq_nat_dec n a).
        -- eapply Nat.le_trans.
           ++ apply IHl.
           ++ apply Nat.le_max_r.
        -- simpl in |- *.
           apply maxLemma.
           ++ apply le_n.
           ++ assumption.
    + eapply Nat.le_trans.
      * apply Hrecf.
      * apply Nat.le_max_r.
Qed.

Remark maxSubTerm (t : fol.Term L) (v : nat) (s : fol.Term L):
  fold_right Nat.max 0 (freeVarT (substT t v s)) <=
    fold_right Nat.max 0 (freeVarT s ++ freeVarT t).
Proof.
  elim t using Term_Terms_ind with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             fold_right Nat.max 0 (freeVarTs (substTs ts v s)) <=
               fold_right Nat.max 0 (freeVarT s ++ freeVarTs ts));
    simpl; intros.
  - induction (eq_nat_dec v n) as [a | ?].
    + apply maxLemma2.
    + apply maxLemma3.
  - apply H.
  - apply Nat.le_0_l.
  - replace
      (freeVarTs 
         (Tcons (substT t0 v s) (substTs t1 v s))) 
      with
      (freeVarT (substT t0 v s) ++
         freeVarTs (substTs t1 v s)).
    + replace (freeVarTs  (Tcons t0 t1)) 
        with
        (freeVarT t0 ++ freeVarTs  t1).
      * induction
          (maxApp (freeVarT (substT t0 v s))
             (freeVarTs (substTs t1 v s))) as [a | b].
        -- rewrite a; eapply Nat.le_trans.
           ++ apply H.
           ++ induction (maxApp (freeVarT s) (freeVarT t0)) 
                as [a0 | b].
              ** rewrite a0.
                 apply maxLemma2.
              ** rewrite b; 
                   apply Nat.le_trans with 
                   (fold_right Nat.max 0 (freeVarT t0 ++ 
                                            freeVarTs t1)).
                 apply maxLemma2.
                 apply maxLemma3.
        -- rewrite b.
           eapply Nat.le_trans.
           ++ apply H0.
           ++ induction (maxApp (freeVarT s) (freeVarTs t1)) 
                as [a | b0].
              ** rewrite a.
                 apply maxLemma2.
              ** rewrite b0.
                 apply Nat.le_trans with 
                   (fold_right Nat.max 0 (freeVarT t0 ++ 
                                            freeVarTs t1)).
                 apply maxLemma3.
                 apply maxLemma3.
      * reflexivity.
    + reflexivity.
Qed.

Remark maxSubTerms (n : nat) (ts : fol.Terms L n) (v : nat) (s : fol.Term L):
  fold_right Nat.max 0 (freeVarTs  (substTs ts v s)) <=
    fold_right Nat.max 0 (freeVarT s ++ freeVarTs ts).
Proof.
  induction ts as [| n t ts Hrects]; simpl in |- *. 
  - apply Nat.le_0_l.
  - replace
      (freeVarTs  (Tcons (substT t v s) (substTs ts v s))) 
      with
      (freeVarT (substT t v s) ++
         freeVarTs  (substTs ts v s)).
    + replace (freeVarTs (Tcons t ts)) 
        with
        (freeVarT t ++ freeVarTs  ts).
      * induction
          (maxApp (freeVarT (substT t v s))
             (freeVarTs (substTs ts v s))) as [a | b].
        -- rewrite a; eapply Nat.le_trans.
           ++ apply maxSubTerm.
           ++ induction (maxApp (freeVarT s) (freeVarT t)) 
                as [a0 | b].
              ** rewrite a0; apply maxLemma2.
              ** rewrite b; apply Nat.le_trans 
                   with (fold_right Nat.max 0 (freeVarT t ++ 
                                                 freeVarTs ts)).
                 apply maxLemma2.
                 apply maxLemma3.
        -- rewrite b; eapply Nat.le_trans.
           ++ apply Hrects.
           ++ induction (maxApp (freeVarT s) (freeVarTs ts)) 
                as [a | b0].
              ** rewrite a; apply maxLemma2.
              ** rewrite b0; apply  Nat.le_trans with 
                   (fold_right Nat.max 0 (freeVarT t ++ 
                                            freeVarTs ts)).
                 apply maxLemma3.
                 apply maxLemma3.
      * reflexivity.
    + reflexivity.
Qed.

(* To  move ??? *)
(** [3 ^ n] *)
Definition pow3 : nat -> nat :=
  nat_rec (fun _ => nat) 1 (fun _ rec : nat => rec + (rec + rec)).



Lemma pow3IsPR : isPR 1 pow3.
Proof.
  unfold pow3; apply indIsPR with (g := 1) (f := fun _ rec : nat => rec + (rec + rec)).
  apply filter01IsPR with (g := fun rec : nat => rec + (rec + rec)).
  apply compose1_2IsPR with 
    (f := fun rec : nat => rec) (f' := fun rec : nat => rec + rec).
  - apply idIsPR.
  - apply compose1_2IsPR with 
      (f := fun rec : nat => rec) (f' := fun rec : nat => rec).
    + apply idIsPR.
    + apply idIsPR.
    + apply plusIsPR.
  - apply plusIsPR.
Qed.

Lemma pow3Monotone : forall a b : nat, a <= b -> pow3 a <= pow3 b.
Proof.
  intros a b H; induction b as [| b Hrecb].
  - simpl;  replace a with 0 by lia.
    apply le_n.
  - simpl; rewrite Nat.lt_eq_cases in H; case H.  
    + intro H0; apply Nat.le_trans with (pow3 b).
      * apply Hrecb; now apply Compat815.lt_n_Sm_le.
      * apply Nat.le_add_r.
    + intro H0; rewrite H0; apply le_n.
Qed.

Lemma pow3Min : forall a : nat, 1 <= pow3 a.
Proof.
  induction a as [| a Hreca].
  - apply le_n.
  - simpl; eapply Nat.le_trans.
    + apply Hreca.
    + apply Nat.le_add_r.
Qed.

Remark mapListLemma :
  forall l : list nat,
    fold_right Nat.max 0 (map S l) <= S (fold_right Nat.max 0 l).
Proof.
  induction l as [| a l Hrecl].
  - simpl; auto.
  - simpl; induction (fold_right Nat.max 0 (map S l)).
    + apply le_n_S.
      apply Nat.le_max_l.
    + apply le_n_S, maxLemma.
      * apply le_n.
      * now apply le_S_n.
Qed.
                      
Remark boundSubFormulaHelp2  (a : fol.Formula L) (v0 : nat) (s : fol.Term L):
  newVar (v0 :: freeVarT s ++ freeVarF a) <=
    S
      (fold_right Nat.max 0
         (v0 :: fold_right Nat.max 0 (freeVarT s) :: varFormula a)).
Proof. 
  unfold newVar; apply Nat.le_trans with 
    (S (fold_right Nat.max 0 (v0 :: freeVarT s ++ freeVarF a))).
  - apply mapListLemma.
  - apply le_n_S; simpl; apply maxLemma.
    + apply le_n.
    + induction (maxApp (freeVarT s) (freeVarF a)) as [a0 | b]. 
      * rewrite a0; apply Nat.le_max_l.
      * rewrite b; eapply Nat.le_trans.
        -- apply maxVarFreeVar.
        -- apply Nat.le_max_r.
Qed.
      
Remark boundSubFormulaHelp1 :
  forall (b a : fol.Formula L) (v0 v : nat) (s : fol.Term L),
    fold_right Nat.max 0
      (varFormula
         (substF b v
            (var (newVar (v0 :: freeVarT s ++ freeVarF a))))) <=
      pow3 (depth L b) + pow3 (depth L b) +
        Nat.max v0
          (Nat.max (fold_right Nat.max 0 (freeVarT s))
             (Nat.max v
                (Nat.max (fold_right Nat.max 0 (varFormula b))
                   (fold_right Nat.max 0 (varFormula a))))).
Proof.
  intro b; elim b using Formula_depth_ind2.
  - intros t t0 a v0 v s;
      set (nv := newVar (v0 :: freeVarT s ++ freeVarF a)).
    simpl; apply le_S.
     induction
       (maxApp (freeVarT (substT t v (var nv)))
          (freeVarT (substT t0 v (var nv)))) as [a0 | b0].
    + rewrite a0; eapply Nat.le_trans.
      * apply maxSubTerm.
      * simpl; apply (Nat.max_case nv (fold_right Nat.max 0 (freeVarT t))).
        -- eapply Nat.le_trans.
           ++ apply (boundSubFormulaHelp2 a v0 s).
           ++ apply le_n_S.
              simpl; repeat apply maxLemma; try apply le_n.
              eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
              apply Nat.le_max_r.
        -- apply le_S.
           do 3 (eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ]).
           eapply Nat.le_trans; [ idtac | apply Nat.le_max_l ].
           apply maxLemma2.
    + rewrite b0; eapply Nat.le_trans.
      * apply maxSubTerm.
      * simpl; apply (Nat.max_case nv (fold_right Nat.max 0 (freeVarT t0))).
        -- eapply Nat.le_trans.
           ++ apply (boundSubFormulaHelp2 a v0 s).
           ++ apply le_n_S.
              simpl; repeat apply maxLemma; try apply le_n.
              eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
              apply Nat.le_max_r.
        -- apply le_S.
           do 3 (eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ]).
           eapply Nat.le_trans; [ idtac | apply Nat.le_max_l ].
           apply maxLemma3.
  -  intros r t a v0 v s;
       set (nv := newVar (v0 :: freeVarT s ++ freeVarF a));
       eapply Nat.le_trans.
     + simpl; apply maxSubTerms.
     + simpl; apply le_S.
       apply
         (Nat.max_case nv
            (fold_right max 0 
               (freeVarTs t))).
       * eapply Nat.le_trans.
         -- apply (boundSubFormulaHelp2 a v0 s).
         -- apply le_n_S.
            simpl; repeat apply maxLemma; try apply le_n.
            eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
            apply Nat.le_max_r.
       * apply le_S.
         do 3 (eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ]).
         eapply Nat.le_trans; [ idtac | apply Nat.le_max_l ].
         apply le_n.
  - intros f H f0 H0 a v0 v s;
      set (nv := newVar (v0 :: freeVarT s ++ freeVarF a)).
    rewrite subFormulaImp; simpl. 
    induction
      (maxApp (varFormula (substF f v (var nv)))
         (varFormula (substF f0 v (var nv)))) as [a0 | b0].
    + rewrite a0; eapply Nat.le_trans.
      * apply (H a v0 v s).
      * apply Nat.add_le_mono. 
        -- eapply Nat.le_trans; [ idtac | apply Nat.le_add_r ].
           assert (H1: pow3 (depth L f) <= pow3 (Nat.max (depth L f) (depth L f0)))
           by (apply pow3Monotone; apply Nat.le_max_l). 
           apply Nat.add_le_mono.
           ++ assumption.
           ++ eapply Nat.le_trans; [ idtac | apply Nat.le_add_r ].
              assumption.
        -- repeat apply maxLemma; try apply le_n.
           apply maxLemma2.
    + rewrite b0; eapply Nat.le_trans.
      * apply (H0 a v0 v s).
      * apply  Nat.add_le_mono.
        -- eapply Nat.le_trans; [ idtac | apply Nat.le_add_r ].
           assert (H1: pow3 (depth L f0) <= pow3 (Nat.max (depth L f) (depth L f0))) by
           (apply pow3Monotone; apply Nat.le_max_r).
           apply  Nat.add_le_mono.
           ++ assumption.
           ++ eapply Nat.le_trans; [ idtac | apply Nat.le_add_r ].
              assumption.
        -- repeat apply maxLemma; try apply le_n.
           apply maxLemma3.
  - intros f H a v0 v s;
      set (nv := newVar (v0 :: freeVarT s ++ freeVarF a)).
    rewrite subFormulaNot; eapply Nat.le_trans.
    + apply (H a v0 v s).
    + apply  Nat.add_le_mono.
      * simpl; eapply Nat.le_trans; [ idtac | apply Nat.le_add_r ].
        apply Compat815.le_plus_r.
      * apply le_n.
  - intros v a H a0 v0 v1 s;
      set (nv := newVar (v0 :: freeVarT s ++ freeVarF a));
      clear nv.
    rewrite subFormulaForall; induction (eq_nat_dec v v1) as [a1 | b0].
    +  eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
       do 3 (eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ]).
       apply Nat.le_max_l.
    + induction
      (In_dec eq_nat_dec v
         (freeVarT (var (newVar (v0 :: freeVarT s ++ freeVarF a0)))))
        as [a1 | b1].
      * simpl; apply (Nat.max_case
                        (newVar
                           (v1
                              :: newVar (v0 :: freeVarT s ++
                                           freeVarF a0)
                              :: freeVarF a))
                        (fold_right Nat.max 0
                           (varFormula
                              (substF 
                                 (substF a v
                                    (var
                                       (newVar
                                          (v1
                                             :: newVar
                                             (v0 :: freeVarT s ++ 
                                                freeVarF a0)
                                             :: freeVarF a)))) v1
                                 (var
                                    (newVar (v0 :: freeVarT s ++ 
                                               freeVarF a0))))))).
    -- unfold newVar at 1; eapply Nat.le_trans.
       ++ apply mapListLemma.
       ++ apply Nat.le_trans with
            (1 + 1 +
               Nat.max v0
                 (Nat.max (fold_right Nat.max 0 (freeVarT s))
                    (Nat.max v1
                       (Nat.max (Nat.max v (fold_right Nat.max 0 (varFormula a)))
                          (fold_right Nat.max 0 (varFormula a0)))))).
    ** simpl; apply le_n_S.
       apply
         (Nat.max_case v1
            (Nat.max (newVar (v0 :: freeVarT s ++ freeVarF a0))
               (fold_right Nat.max 0 (freeVarF a)))).
       apply le_S.
       do 2 (eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ]).
       apply Nat.le_max_l.
       apply
         (Nat.max_case (newVar (v0 :: freeVarT s ++ freeVarF a0))
            (fold_right max 0 (freeVarF a))).
       eapply Nat.le_trans.
       apply boundSubFormulaHelp2.
       apply le_n_S.
       simpl; repeat apply maxLemma; try apply le_n.
       eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
       apply Nat.le_max_r.
       apply le_S.
       do 3 (eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ]).
       eapply Nat.le_trans; [ idtac | apply Nat.le_max_l ].
       eapply Nat.le_trans.
       apply maxVarFreeVar.
       apply Nat.le_max_r.
    ** apply  Nat.add_le_mono.
       eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
       apply  Nat.add_le_mono.
       apply pow3Min.
       simpl; eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
       apply pow3Min.
       apply le_n.
    --  eapply Nat.le_trans.
        ++ apply H.
           eapply eqDepth.
           ** symmetry  in |- *.
              apply subFormulaDepth.
           ** apply depthForall.
        ++  rewrite subFormulaDepth.
            rewrite (Nat.add_assoc (pow3 (depth L a)) 
                       (pow3 (depth L a)) (pow3 (depth L a))).
            repeat rewrite <- (Nat.add_assoc  (pow3 (depth L a) + pow3 (depth L a))).
            apply  Nat.add_le_mono.
            ** apply le_n.
            ** apply
                (Nat.max_case v0
                   (Nat.max (fold_right Nat.max 0 (freeVarT s))
                      (Nat.max v1
                         (Nat.max
                            (fold_right Nat.max 0
                               (varFormula
                                  (substF a v
                                     (var
                                        (newVar
                                           (v1
                                              :: newVar
                                              (v0
                                                 :: freeVarT s ++ 
                                                 freeVarF a0)
                                              :: freeVarF a))))))
                            (fold_right Nat.max 0 (varFormula a0)))))).
               eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
               apply Nat.le_max_l.
               apply
                 (Nat.max_case (fold_right Nat.max 0 (freeVarT s))
                    (Nat.max v1
                       (Nat.max
                          (fold_right Nat.max 0
                             (varFormula
                                (substF a v
                                   (var
                                      (newVar
                                         (v1
                                            :: newVar
                                            (v0 :: freeVarT s 
                                               ++ freeVarF a0)
                                            :: freeVarF a))))))
                          (fold_right Nat.max 0 (varFormula a0))))).
               eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
               eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
               apply Nat.le_max_l.
               apply
                 (Nat.max_case v1
                    (Nat.max
                       (fold_right Nat.max 0
                          (varFormula
                             (substF a v
                                (var
                                   (newVar
                                      (v1
                                         :: newVar
                                         (v0 :: freeVarT s ++ freeVarF a0)
                                         :: freeVarF a))))))
                       (fold_right Nat.max 0 (varFormula a0)))).
               eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
               do 2 (eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ]).
               apply Nat.le_max_l.
               apply
                 (Nat.max_case
                    (fold_right Nat.max 0
                       (varFormula
                          (substF a v
                             (var
                                (newVar
                                   (v1
                                      :: newVar (v0 :: freeVarT s ++ 
                                                   freeVarF a0)
                                      :: freeVarF a))))))
                    (fold_right Nat.max 0 (varFormula a0))).
               eapply Nat.le_trans.
               apply H with
                 (b := a)
                 (v := v)
                 (v0 := v1)
                 (a := a)
                 (s := var (newVar (v0 :: freeVarT s ++ freeVarF a0))).
               apply depthForall.
               rewrite
                 (Nat.add_comm (pow3 (depth L a))
                    (pow3 (depth L a) + pow3 (depth L a) + pow3 (depth L a))).
               repeat rewrite <- (Nat.add_assoc (pow3 (depth L a) + pow3 (depth L a))).
               apply  Nat.add_le_mono.
               apply le_n.
               apply
                 (Nat.max_case v1
                    (Nat.max
                       (fold_right Nat.max 0
                          (freeVarT 
                             (var (newVar (v0 :: freeVarT s ++ 
                                             freeVarF a0)))))
                       (Nat.max v
                          (Nat.max (fold_right Nat.max 0 (varFormula a))
                             (fold_right Nat.max 0 (varFormula a)))))).
               eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
               do 2 (eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ]).
               apply Nat.le_max_l.
               apply
                 (Nat.max_case
                    (fold_right Nat.max 0
                       (freeVarT 
                          (var (newVar (v0 :: freeVarT s ++ freeVarF a0)))))
                    (Nat.max v
                       (Nat.max (fold_right Nat.max 0 (varFormula a))
                          (fold_right Nat.max 0 (varFormula a))))).
               simpl;
                 apply (Nat.max_case (newVar (v0 :: freeVarT s ++ 
                                                freeVarF a0)) 0).
               eapply Nat.le_trans.
               apply boundSubFormulaHelp2.
               apply
                 Nat.le_trans
                 with
                 (1 +
                    Nat.max v0
                      (Nat.max (fold_right Nat.max 0 (freeVarT s))
                         (Nat.max v1
                            (Nat.max (Nat.max v (fold_right Nat.max 0 (varFormula a)))
                               (fold_right Nat.max 0 (varFormula a0)))))).
               simpl; apply le_n_S.
               repeat apply maxLemma; try apply le_n.
               repeat (eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ]).
               apply le_n.
               apply Nat.add_le_mono.
               eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
               apply pow3Min.
               apply le_n.
               apply Nat.le_0_l.
               eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
               do 3 (eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ]).
               apply
                 (Nat.max_case v
                    (Nat.max (fold_right Nat.max 0 (varFormula a)) 
                       (fold_right Nat.max 0 (varFormula a)))).
               eapply Nat.le_trans; [ idtac | apply Nat.le_max_l ].
               apply Nat.le_max_l.
               apply
                 (Nat.max_case (fold_right Nat.max 0 (varFormula a))
                    (fold_right Nat.max 0 (varFormula a)));
                 (eapply Nat.le_trans; [ idtac | apply Nat.le_max_l ];
                  apply Nat.le_max_r).
               eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
               repeat (eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ]).
               apply le_n.
      * simpl;
          apply
            (Nat.max_case v
               (fold_right Nat.max 0
                  (varFormula
                     (substF a v1
                        (var
                           (newVar (v0 :: freeVarT s ++ 
                                      freeVarF a0))))))).
        -- eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
           do 3 (eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ]).
           eapply Nat.le_trans; [ idtac | apply Nat.le_max_l ].
           apply Nat.le_max_l.
        -- eapply Nat.le_trans.
           ++ apply H.
              apply depthForall.
           ++ apply Nat.add_le_mono.
              ** eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
                 apply Nat.add_le_mono.
                 apply le_n.
                 apply Nat.le_add_r.
              ** repeat apply maxLemma; try apply le_n.
                 apply Nat.le_max_r.
Qed.
  
Remark boundSubFormulaHelp :
 forall (f : fol.Formula L) (v : nat) (s : fol.Term L),
 codeFormula (substF f v s) <=
 ReplaceFormulaTerm (codeFormula f)
   (Nat.max (codeTerm s)
      (pow3 (depth L f) +
       fold_right Nat.max 0 (v :: freeVarT s ++ varFormula f))).
Proof.
  intro f; unfold ReplaceFormulaTerm;
    set
      (A :=
         fun f0 recs s0 : nat =>
           switchPR (car f0)
             (switchPR (pred (car f0))
                (switchPR (pred (pred (car f0)))
                   (switchPR (pred (pred (pred (car f0))))
                      (cPair (car f0) (ReplaceTermsTerm (cdr f0) s0))
                      (cPair 3
                         (cPair s0 (codeNth (f0 - S (cdr (cdr f0))) recs))))
                   (cPair 2 (codeNth (f0 - S (cdr f0)) recs)))
                (cPair 1
                   (cPair (codeNth (f0 - S (car (cdr f0))) recs)
                      (codeNth (f0 - S (cdr (cdr f0))) recs))))
             (cPair 0
                (cPair (ReplaceTermTerm (car (cdr f0)) s0)
                   (ReplaceTermTerm (cdr (cdr f0)) s0)))).
  assert
    (H:forall n m : nat,
        m < n ->
        extEqual 1
          (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 A n) 0 (Vector.nil _))
             (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 A m)) by
    (intros;  apply (evalStrongRecHelp2 1); assumption). 
  simpl in H; elim f using Formula_depth_ind2.
  - intros; unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
    repeat rewrite computeEvalStrongRecHelp.
    unfold compose2, evalComposeFunc, evalOneParamList, evalList.
    set
      (C :=
         Nat.max (codeTerm s)
           (pow3 (depth L (equal t t0)) +
              fold_right Nat.max 0 (v :: freeVarT s ++ varFormula (equal t t0)))).
    simpl; repeat rewrite cPairProjections1.
    unfold A at 1; 
      repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    simpl; apply cPairLe3.
    + apply le_n.
    + apply cPairLe3.
      * apply Nat.le_trans with
          (ReplaceTermTerm (codeTerm t)
             (fold_right Nat.max 0 (codeTerm s :: freeVarT t))).
        -- apply boundSubTerm.
        -- apply ReplaceTermTermMonotone.
           unfold C; simpl; apply maxLemma.
           ++ apply le_n.
           ++ apply le_S.
              eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
              eapply Nat.le_trans; [ idtac | apply maxLemma3 ].
              apply maxLemma2.
      * apply  Nat.le_trans with
          (ReplaceTermTerm (codeTerm t0)
             (fold_right Nat.max 0 (codeTerm s :: freeVarT t0))).
        -- apply boundSubTerm.
        -- apply ReplaceTermTermMonotone.
           unfold C; simpl; apply maxLemma.
           ++ apply le_n.
           ++ apply le_S.
              eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
              eapply Nat.le_trans; [ idtac | apply maxLemma3 ].
              apply maxLemma3.
  - intros; unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
    repeat rewrite computeEvalStrongRecHelp.
    unfold compose2, evalComposeFunc, evalOneParamList, evalList.
    set
      (C :=
         Nat.max (codeTerm s)
           (pow3 (depth L (atomic r t)) +
              fold_right Nat.max 0 (v :: freeVarT s ++ varFormula (atomic r t)))).
    simpl; repeat rewrite cPairProjections1.
    unfold A at 1; 
      repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    simpl; apply cPairLe3.
    + apply le_n.
    + apply Nat.le_trans  with
        (ReplaceTermsTerm (codeTerms t)
           (fold_right Nat.max 0 (codeTerm s :: freeVarTs  t))).
      * apply boundSubTerms.
      * apply ReplaceTermsTermMonotone.
        unfold C; simpl; apply maxLemma.
        -- apply le_n.
        -- apply le_S.
           eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
           apply maxLemma3.
  - intros f0 H0 f1 H1 v s; rewrite subFormulaImp.
    set
      (C :=
         Nat.max (codeTerm s)
           (pow3 (depth L (impH f0 f1)) +
              fold_right Nat.max 0 (v :: freeVarT s ++ varFormula (impH  f0 f1)))).
    unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
    repeat rewrite computeEvalStrongRecHelp.
    unfold compose2, evalComposeFunc, evalOneParamList, evalList.
    simpl; repeat rewrite cPairProjections1.
    unfold A at 1;
      repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    rewrite H with (m := codeFormula f0).
    + rewrite H with (m := codeFormula f1).
      * simpl; apply cPairLe3.
        -- apply le_n.
        -- apply cPairLe3.
           ++ apply  Nat.le_trans  with
                (evalStrongRec 1 A (codeFormula f0)
                   (Nat.max (codeTerm s)
                      (pow3 (depth L f0) +
                         fold_right Nat.max 0 (v :: freeVarT s ++ varFormula f0)))).
              ** auto.
              ** apply ReplaceFormulaTermMonotone.
                 unfold C; apply maxLemma.
                 apply le_n.
                 apply Nat.add_le_mono.
                 apply pow3Monotone.
                 simpl; apply le_S.
                 apply Nat.le_max_l.
                 simpl; apply maxLemma.
                 apply le_n.
                 rewrite ass_app.
                 apply maxLemma2.
           ++ apply Nat.le_trans with
                (evalStrongRec 1 A (codeFormula f1)
                   (Nat.max (codeTerm s)
                      (pow3 (depth L f1) +
                         fold_right Nat.max 0 (v :: freeVarT s ++ varFormula f1)))).
              ** auto.
              ** apply ReplaceFormulaTermMonotone.
                 unfold C; apply maxLemma.
                 apply le_n.
                 apply Nat.add_le_mono.
                 apply pow3Monotone.
                 simpl; apply le_S.
                 apply Nat.le_max_r.
                 simpl; apply maxLemma.
                 apply le_n.
                 induction (maxApp (freeVarT s) (varFormula f1)) as [a | b].
                 --- rewrite a; apply maxLemma2.
                 --- rewrite b; eapply Nat.le_trans; [ idtac | apply maxLemma3 ].
                     apply maxLemma3.
      * eapply Nat.le_lt_trans; [ idtac | apply cPairLt2 ].
        apply cPairLe2.
    + eapply Nat.le_lt_trans; [ idtac | apply cPairLt2 ].
      apply cPairLe1.
  - intros f0 H0 v s; rewrite subFormulaNot.
    set
      (C :=
         Nat.max (codeTerm s)
           (pow3 (depth L (notH f0)) +
              fold_right Nat.max 0 (v :: freeVarT s ++ varFormula (notH f0)))). 
    unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
    repeat rewrite computeEvalStrongRecHelp.
    unfold compose2, evalComposeFunc, evalOneParamList, evalList; simpl. 
    repeat rewrite cPairProjections1.
    unfold A at 1; 
      repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    rewrite H with (m := codeFormula f0).
    + simpl; apply cPairLe3.
      * apply le_n.
      * apply Nat.le_trans with
          (evalStrongRec 1 A (codeFormula f0)
             (Nat.max (codeTerm s)
                (pow3 (depth L f0) +
                   fold_right Nat.max 0 (v :: freeVarT s ++ varFormula f0)))).
        -- auto.
        -- apply ReplaceFormulaTermMonotone.
           unfold C; apply maxLemma.
           ++ apply le_n.
           ++ apply Nat.add_le_mono.
              ** apply pow3Monotone.
                 simpl; apply Nat.le_succ_diag_r.
              ** apply le_n.
    + apply cPairLt2.
  - intros v a H0 v0 s; set
                          (C :=
                             Nat.max (codeTerm s)
                               (pow3 (depth L (forallH v a)) +
                                  fold_right Nat.max 0 
                                    (v0 :: freeVarT s ++ 
                                       varFormula (forallH v a)))).
    unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList;
      repeat rewrite computeEvalStrongRecHelp.
    unfold compose2, evalComposeFunc, evalOneParamList, evalList.
    simpl; repeat rewrite cPairProjections1.
    unfold A at 1;
      repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
    rewrite H with (m := codeFormula a).
    + simpl; rewrite subFormulaForall.
      induction (eq_nat_dec v v0) as [a0 |b].
      * simpl; apply cPairLe3.
        apply le_n.
        -- apply cPairLe3.
           ++ unfold C; rewrite a0.
              eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
              eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
              simpl; apply Nat.le_max_l.
           ++ apply Nat.le_trans with (codeFormula (substF a 0 (var 0))).
              ** rewrite (subFormulaId L).
                 apply le_n.
              ** apply Nat.le_trans with
                   (evalStrongRec 1 A (codeFormula a)
                      (Nat.max (codeTerm (var 0))
                         (pow3 (depth L a) +
                            fold_right Nat.max 0 (0 :: freeVarT (L:=L)(var 0) ++ 
                                                    varFormula a)))).
                 apply H0.
                 apply depthForall.
                 apply ReplaceFormulaTermMonotone.
                 unfold C; apply maxLemma.
                 apply Nat.le_0_l.
                 apply Nat.add_le_mono.
                 apply pow3Monotone.
                 simpl; apply Nat.le_succ_diag_r.
                 simpl; eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
                 eapply Nat.le_trans; [ idtac | apply maxLemma3 ].
                 simpl; apply Nat.le_max_r.
      * induction (In_dec eq_nat_dec v (freeVarT s)) as [a0 | b0]. 
        -- simpl; apply cPairLe3.
           apply le_n.
           set (nv := newVar (v0 :: freeVarT s ++ freeVarF a)).
           apply cPairLe3.
           ++ unfold C; eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
              simpl; apply  Nat.le_trans with 
                (1 + Nat.max v0 (fold_right Nat.max 0 
                                   (freeVarT s ++ v :: varFormula a))).
              ** simpl; unfold nv, newVar.
                 eapply Nat.le_trans.
                 apply mapListLemma.
                 apply le_n_S.
                 simpl; apply maxLemma.
                 apply le_n.
                 induction (maxApp (freeVarT s) (freeVarF a)) as [a1 | b1].
                 --- rewrite a1.
                     apply maxLemma2.
                 --- rewrite b1; eapply Nat.le_trans; [ idtac | apply maxLemma3 ].
                     simpl; eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
                     apply maxVarFreeVar.
              ** apply Nat.add_le_mono.
                 eapply Nat.le_trans; [ idtac | apply Nat.le_add_r ].
                 apply pow3Min.
                 apply le_n.
           ++ set (B := substF a v (var nv)).
              apply Nat.le_trans with
                (evalStrongRec 1 A (codeFormula B)
                   (Nat.max (codeTerm s)
                      (pow3 (depth L B) +
                         fold_right Nat.max 0 (v0 :: freeVarT s ++ varFormula B)))).
              ** apply H0.
                 unfold B; eapply eqDepth.
                 symmetry; apply subFormulaDepth.
                 apply depthForall.
              ** unfold B at 1; rewrite ReplaceFormulaTermSub.
                 apply ReplaceFormulaTermMonotone.
                 simpl; unfold B at 1 2; rewrite subFormulaDepth.
                 unfold C; simpl; apply maxLemma.
                 apply le_n.
                 rewrite <- Nat.add_assoc.
                 apply Nat.add_le_mono_l.
                 apply
                   (Nat.max_case v0
                      (fold_right Nat.max 0
                         (freeVarT s ++
                            varFormula (substF a v (var nv))))).
                 eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
                 apply Nat.le_max_l.
                 induction
                   (maxApp (freeVarT s)
                      (varFormula (substF a v (var nv)))) as [a1 | b1].
                 --- rewrite a1.
                     eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
                     eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
                     apply maxLemma2.
                 --- rewrite b1; clear b1.
                     clear H0 C B.
                     unfold nv; clear nv.
                     eapply Nat.le_trans.
                     apply boundSubFormulaHelp1.
                     apply Nat.add_le_mono.
                     apply le_n.
                     repeat apply maxLemma.
                     apply le_n.
                     apply Nat.max_case.
                     apply maxLemma2.
                     eapply Nat.le_trans; [ idtac | apply maxLemma3 ].
                     simpl; apply maxLemma.
                     apply le_n.
                     apply Nat.max_case; apply le_n.
        -- simpl; apply cPairLe3.
           ++ apply le_n.
           ++ apply cPairLe3.
              unfold C; simpl.
              ** eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
                 eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
                 eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
                 eapply Nat.le_trans; [ idtac | apply maxLemma3 ].
                 simpl; apply Nat.le_max_l.
              ** eapply Nat.le_trans.
                 apply H0.
                 apply depthForall.
                 apply ReplaceFormulaTermMonotone.
                 unfold C; apply maxLemma.
                 apply le_n.
                 apply Nat.add_le_mono.
                 simpl; apply Nat.le_add_r.
                 simpl; apply maxLemma.
                 apply le_n.
                 induction (maxApp (freeVarT s) (varFormula a)) as [a0 | b1].
                 --- rewrite a0; apply maxLemma2.
                 --- rewrite b1; eapply Nat.le_trans; [ idtac | apply maxLemma3 ].
                     simpl; apply Nat.le_max_r.
    + eapply Nat.le_lt_trans; [ idtac | apply cPairLt2 ].
      apply cPairLe2.
Qed.

Definition boundComputation (d p1 p2 : nat) : nat :=
  nat_rec (fun _ => nat) (cTriple p1 p2 0)
    (fun _ rec : nat => cTriple p1 p2 (cPair rec rec)) d.

Lemma boundComputationIsPR : isPR 3 boundComputation.
Proof.
  unfold boundComputation;
    apply
      ind2ParamIsPR
    with
    (f := fun _ rec p1 p2 : nat => cTriple p1 p2 (cPair rec rec))
    (g := fun p1 p2 : nat => cTriple p1 p2 0).
  - apply compose4_3IsPR with
      (f1 := fun _ rec p1 p2 : nat => p1)
      (f2 := fun _ rec p1 p2 : nat => p2)
      (f3 := fun _ rec p1 p2 : nat => cPair rec rec).
    + apply pi3_4IsPR.
    + apply pi4_4IsPR.
    + apply filter1100IsPR with (g := fun _ rec : nat => cPair rec rec).
      apply filter01IsPR with (g := fun rec : nat => cPair rec rec).
      apply compose1_2IsPR with
        (f := fun rec : nat => rec) (f' := fun rec : nat => rec).
      * apply idIsPR.
      * apply idIsPR.
      * apply cPairIsPR.
    + apply cTripleIsPR.
  - apply compose2_3IsPR with
      (f1 := fun p1 p2 : nat => p1)
      (f2 := fun p1 p2 : nat => p2)
      (f3 := fun p1 p2 : nat => 0).
    + apply pi1_2IsPR.
    + apply pi2_2IsPR.
    + apply filter10IsPR with (g := fun _ : nat => 0).
      apply const1_NIsPR.
    + apply cTripleIsPR.
Qed.

Lemma boundComputationMonotone :
 forall a1 a2 b1 b2 c1 c2 : nat,
 a1 <= a2 ->
 b1 <= b2 ->
 c1 <= c2 -> boundComputation a1 b1 c1 <= boundComputation a2 b2 c2.
Proof.
intros a1 a2; revert a1; unfold boundComputation.
induction a2 as [| a2 Hreca2]; simpl.
- intros a1 b1 b2 c1 c2 H H0 H1; rewrite Nat.le_0_r in H;  rewrite H. 
  simpl; unfold cTriple; apply cPairLe3.
  + assumption.
  + apply cPairLe3.
    * assumption.
    * apply le_n.
-   intros a1 b1 b2 c1 c2 H H0 H1; generalize H ; intro  H'; 
      rewrite Nat.lt_eq_cases in H'. 
    destruct H' as [H2 | H2].
    + eapply Nat.le_trans.
      * apply (Hreca2 a1 b1 b2 c1 c2); try assumption.
        apply Compat815.lt_n_Sm_le.
        assumption.
      * unfold cTriple at 3; 
          eapply Nat.le_trans; [ idtac | apply cPairLe2 ].
        eapply Nat.le_trans; [ idtac | apply cPairLe2 ].
        apply cPairLe2.
    + rewrite H2; simpl; unfold cTriple at 6 1.
      apply cPairLe3.
      * assumption.
      * apply cPairLe3.
        -- assumption.
        -- apply cPairLe3; apply Hreca2; apply le_n || assumption.
Qed.

Lemma boundMakeTrace :
 forall (f : fol.Formula L) (v : nat) (s : fol.Term L),
 let C :=
   Nat.max (codeTerm s)
     (cPair 0
        (pow3 (depth L f) +
         fold_right Nat.max 0 (v :: freeVarT s ++ varFormula f))) in
 makeTrace f (v, s) <=
 boundComputation (depth L f)
   (cTriple C C (ReplaceFormulaTerm (codeFormula f) C))
   (ReplaceFormulaTerm (codeFormula f) C).
Proof.
  set
    (A :=
       fun f2 recs s0 : nat =>
         switchPR (car f2)
           (switchPR (pred (car f2))
              (switchPR (pred (pred (car f2)))
                 (switchPR (pred (pred (pred (car f2))))
                    (cPair (car f2) (ReplaceTermsTerm (cdr f2) s0))
                    (cPair 3
                       (cPair s0 (codeNth (f2 - S (cdr (cdr f2))) recs))))
                 (cPair 2 (codeNth (f2 - S (cdr f2)) recs)))
              (cPair 1
                 (cPair (codeNth (f2 - S (car (cdr f2))) recs)
                    (codeNth (f2 - S (cdr (cdr f2))) recs))))
           (cPair 0
              (cPair (ReplaceTermTerm (car (cdr f2)) s0)
                 (ReplaceTermTerm (cdr (cdr f2)) s0)))).
  assert
    (E :
      forall (f : fol.Formula L) (v : nat) (s : fol.Term L),
        codeFormula (substF f v s) <=
          ReplaceFormulaTerm (codeFormula f)
            (Nat.max (codeTerm s)
               (cPair 0
                  (pow3 (depth L f) +
                     fold_right Nat.max 0 (v :: freeVarT s ++ varFormula f))))).
  { intros f v s; eapply Nat.le_trans.
    - apply boundSubFormulaHelp.
    - apply ReplaceFormulaTermMonotone,  maxLemma.
      + apply le_n.
      + apply cPairLe2.
  }
  assert
    (D :
      forall n m : nat,
        m < n ->
        extEqual 1
          (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 A n) 0 (Vector.nil _))
             (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 A m)) 
    by (intros n m H; apply (evalStrongRecHelp2 1); assumption).
  simpl in D; intro f.
  assert (H: forall w v n s : nat, v <= Nat.max s (cPair 0 (w + Nat.max v n))).
  { intros w v n s;
      eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
    eapply Nat.le_trans; [ idtac | apply cPairLe2 ].
    eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
    apply Nat.le_max_l.
  } 
  assert
    (H0 :forall (f : fol.Formula L) (v : nat) (s : fol.Term L),
        codeFormula f <=
          ReplaceFormulaTerm (codeFormula f)
            (Nat.max (codeTerm s)
               (cPair 0
                  (pow3 (depth L f) +
                     fold_right Nat.max 0 (v :: freeVarT s ++ varFormula f))))).
  { intros f0 v s;
      apply Nat.le_trans with (codeFormula (substF f0 0 (var 0))).
    - rewrite (subFormulaId L); apply le_n.
    - eapply Nat.le_trans.
      + apply E.
      + apply ReplaceFormulaTermMonotone.
        apply maxLemma.
        apply Nat.le_0_l.
        apply cPairLe3.
        apply le_n.
        apply Nat.add_le_mono.
        apply le_n.
        simpl; eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
        apply maxLemma3.
  } 
  elim f using Formula_depth_ind2.
  - intros t t0 v s C; simpl.
    unfold Formula_depth_rec2, Formula_depth_rec; simpl.
    unfold cTriple, C; simpl; repeat apply cPairLe3.
    + apply  (H 1 v
                (fold_right Nat.max 0
                   (freeVarT s ++ freeVarT  t ++ freeVarT t0)) 
                (codeTerm s)).
    + apply Nat.le_max_l.
    + apply (H0 (equal t t0) v s).
    + apply (E (equal t t0) v s).
    + apply le_n.
  - intros r t v s C; simpl; unfold makeTrace in |- *.
    unfold Formula_depth_rec2, Formula_depth_rec; simpl.
    unfold cTriple, C; simpl.  
    repeat apply cPairLe3.
    + apply
        (H 1 v
           (fold_right Nat.max 0
              (freeVarT s ++ freeVarTs t))
           (codeTerm s)).
    + apply Nat.le_max_l.
    + apply (H0 (atomic r t) v s).
    + apply (E (atomic r t) v s).
    + apply le_n.
  - intros f0 H1 f1 H2 v s C; simpl; 
      replace (makeTrace (impH f0 f1) (v, s)) with
      (cTriple (cTriple v (codeTerm s) (codeFormula (impH f0 f1)))
         (codeFormula (substF (impH f0 f1) v s))
         (cPair (makeTrace f0 (v, s)) (makeTrace f1 (v, s)))).
    + unfold cTriple; repeat apply cPairLe3.
      * unfold C; simpl.
        apply
          (H
             (pow3 (Nat.max (depth L f0) (depth L f1)) +
                (pow3 (Nat.max (depth L f0) (depth L f1)) +
                   pow3 (Nat.max (depth L f0) (depth L f1)))) v
             (fold_right Nat.max 0 (freeVarT s ++ varFormula f0 ++ varFormula f1))
             (codeTerm s)).
      * unfold C; simpl; apply Nat.le_max_l.
      * apply (H0 (impH f0 f1) v s).
      * apply (E (impH f0 f1) v s).
      * eapply Nat.le_trans.
        -- apply H1.
        -- assert
            (H3 : Nat.max (codeTerm s)
                    (cPair 0
                       (pow3 (depth L f0) +
                          fold_right Nat.max 0 (v :: freeVarT s ++ varFormula f0)))
                  <= C).
           { unfold C; apply maxLemma.
             - apply le_n.
             - apply cPairLe3.
               + apply le_n.
               + apply Nat.add_le_mono.
                 * apply pow3Monotone.
                   simpl; apply le_S.
                   apply Nat.le_max_l.
                 * simpl; apply Nat.max_case.
                   -- apply Nat.le_max_l.
                   -- eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
                      induction (maxApp (freeVarT s) (varFormula f0)) as [a | b].
                      ++ rewrite a; apply maxLemma2.
                      ++ rewrite b; eapply Nat.le_trans; [ idtac | apply maxLemma3 ].
                         apply maxLemma2.
           } 
           assert
             (H4: ReplaceFormulaTerm (codeFormula f0)
                    (Nat.max (codeTerm s)
                       (cPair 0
                          (pow3 (depth L f0) +
                             fold_right Nat.max 0 
                               (v :: freeVarT s ++ varFormula f0)))) <=
                    ReplaceFormulaTerm (cPair 1 (cPair (codeFormula f0) 
                                                   (codeFormula f1))) C).
           { unfold ReplaceFormulaTerm at 2; fold A; unfold evalStrongRec.
             unfold evalComposeFunc, evalOneParamList, evalList.
             repeat rewrite computeEvalStrongRecHelp.
             unfold compose2, evalComposeFunc, evalOneParamList, evalList.
             simpl; unfold A at 1. 
             repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
             rewrite D with (m := codeFormula f0).
             - simpl; eapply Nat.le_trans; [ idtac | apply cPairLe2 ].
               eapply Nat.le_trans; [ idtac | apply cPairLe1 ].
               apply ReplaceFormulaTermMonotone.
               apply H3.
             - eapply Nat.le_lt_trans; [ idtac | apply cPairLt2 ].
               apply cPairLe1.
           } 
           apply boundComputationMonotone.
           ++  apply Nat.le_max_l.
           ++ unfold cTriple; repeat apply cPairLe3.
              ** apply H3.
              ** apply H3.
              ** apply H4.
           ++ apply H4.
      * eapply Nat.le_trans.
        -- apply H2.
        -- assert
            (H3: Nat.max (codeTerm s)
                   (cPair 0
                      (pow3 (depth L f1) +
                         fold_right Nat.max 0 (v :: freeVarT s ++ varFormula f1))) 
                 <= C).
           { unfold C; apply maxLemma.
             - apply le_n.
             - apply cPairLe3.
               + apply le_n.
               + apply Nat.add_le_mono.
                 * apply pow3Monotone.
                   simpl; apply le_S.
                   apply Nat.le_max_r.
                 * simpl; apply Nat.max_case.
                   -- apply Nat.le_max_l.
                   -- eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
                      induction (maxApp (freeVarT s) (varFormula f1)) as [a | b].
                      ++ rewrite a.
                         apply maxLemma2.
                      ++ rewrite b; 
                           eapply Nat.le_trans; [ idtac | apply maxLemma3 ].
                         apply maxLemma3.
           } 
           assert
             (H4: ReplaceFormulaTerm (codeFormula f1)
                    (Nat.max (codeTerm s)
                       (cPair 0
                          (pow3 (depth L f1) +
                             fold_right Nat.max 0
                               (v :: freeVarT s ++ varFormula f1)))) <=
                    ReplaceFormulaTerm (cPair 1 (cPair (codeFormula f0)
                                                   (codeFormula f1))) C).
           { unfold ReplaceFormulaTerm at 2; fold A; unfold evalStrongRec.
             unfold evalComposeFunc, evalOneParamList, evalList;
               repeat rewrite computeEvalStrongRecHelp.
             unfold compose2, evalComposeFunc, evalOneParamList, evalList;
               simpl; unfold A at 1;
               repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
             rewrite D with (m := codeFormula f1).
             - simpl; eapply Nat.le_trans; [ idtac | apply cPairLe2 ].
               eapply Nat.le_trans; [ idtac | apply cPairLe2 ].
               apply ReplaceFormulaTermMonotone.
               apply H3.
             - eapply Nat.le_lt_trans; [ idtac | apply cPairLt2 ].
               apply cPairLe2.
           } 
           apply boundComputationMonotone.
           ++ apply Nat.le_max_r.
           ++ unfold cTriple in |- *.
              ** repeat apply cPairLe3.
                 apply H3.
                 apply H3.
                 apply H4.
           ++ apply H4.
    + unfold makeTrace;
        rewrite
          (Formula_depth_rec2_imp L)
        with
        (Q := 
           fun _ : fol.Formula L =>
             (nat * fol.Term L)%type)
        (P := fun _ : fol.Formula L => nat).
      * unfold makeTraceImp at 1; reflexivity.
      * apply makeTraceImpNice.
      * apply makeTraceNotNice.
      * apply makeTraceForallNice.
  - intros f0 H1 v s C; simpl;  replace (makeTrace (notH  f0) (v, s)) 
      with
      (cTriple (cTriple v (codeTerm s) (codeFormula (notH  f0)))
         (codeFormula (substF (notH  f0) v s)) 
         (makeTrace f0 (v, s))).
    + unfold cTriple in |- *.
      repeat apply cPairLe3.
      * unfold C ; simpl.
        apply
          (H (pow3 (depth L f0) + (pow3 (depth L f0) + pow3 (depth L f0))) v
             (fold_right Nat.max 0 (freeVarT s ++ varFormula f0)) 
             (codeTerm s)).
      * unfold C; simpl; apply Nat.le_max_l.
      * apply (H0 (notH f0) v s).
      * apply (E (notH f0) v s).
      * eapply Nat.le_trans.
        -- apply H1.
-- assert
    (H2: Nat.max (codeTerm s)
          (cPair 0
             (pow3 (depth L f0) +
                fold_right Nat.max 0 (v :: freeVarT s ++ varFormula f0))) <= C).
   unfold C; simpl; apply maxLemma.
   ++ apply le_n.
   ++ apply cPairLe3.
      apply le_n.
      apply Nat.add_le_mono.
      apply Nat.le_add_r.
      apply le_n.
   ++ assert
       (H3: ReplaceFormulaTerm (codeFormula f0)
              (Nat.max (codeTerm s)
                 (cPair 0
                    (pow3 (depth L f0) +
                       fold_right Nat.max 0 (v :: freeVarT s ++ varFormula f0))))
            <=
              ReplaceFormulaTerm (cPair 2 (codeFormula f0)) C).
      { unfold ReplaceFormulaTerm at 2; fold A; unfold evalStrongRec,
          evalComposeFunc, evalOneParamList, evalList.
        repeat rewrite computeEvalStrongRecHelp.
        unfold compose2, evalComposeFunc, evalOneParamList, evalList; simpl.
        unfold A at 1;
          repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
        rewrite D with (m := codeFormula f0).
        - simpl; eapply Nat.le_trans; [ idtac | apply cPairLe2 ].
          apply ReplaceFormulaTermMonotone.
          apply H2.
        - apply cPairLt2.
      } 
      eapply Nat.le_trans; [ idtac | apply cPairLe1 ].
      apply boundComputationMonotone.
      ** apply le_n.
      ** unfold cTriple; repeat apply cPairLe3.
         apply H2.
         apply H2.
         apply H3.
      ** apply H3.
    + unfold makeTrace.
      rewrite
        (Formula_depth_rec2_not L)
        with
        (Q := 
           fun _ : fol.Formula L =>
             (nat * fol.Term L)%type)
        (P := fun _ : fol.Formula L => nat).
      * unfold makeTraceNot at 1; reflexivity.
      * apply makeTraceImpNice.
      * apply makeTraceNotNice.
      * apply makeTraceForallNice.
  - intros v a H1 v0 s C; replace (makeTrace (forallH v a) (v0, s)) 
      with
      (makeTraceForall v a (fun (b : fol.Formula L) _ => makeTrace b) (v0, s)).
    unfold makeTraceForall; simpl.  
    induction (eq_nat_dec v v0) as [a0 | b0]; simpl in |- *.
    + unfold cTriple; repeat apply cPairLe3.
      * unfold C; simpl;
          apply
            (H (pow3 (depth L a) + (pow3 (depth L a) + pow3 (depth L a))) v0
               (fold_right Nat.max 0 (freeVarT s ++ v :: varFormula a)) 
               (codeTerm s)).
      * unfold C; simpl; apply Nat.le_max_l.
      * apply (H0 (forallH v a) v0 s).
      * apply (E (forallH v a) v0 s).
      * apply Nat.le_0_l.
    + induction (In_dec eq_nat_dec v (freeVarT s)) as [a0 | b1]; simpl in |- *.
      * unfold cTriple; repeat apply cPairLe3.
        -- unfold C; simpl.
           apply
             (H (pow3 (depth L a) + (pow3 (depth L a) + pow3 (depth L a))) v0
                (fold_right Nat.max 0 (freeVarT s ++ v :: varFormula a)) 
                (codeTerm s)).
        -- unfold C; simpl; apply Nat.le_max_l.
        -- apply (H0 (forallH v a) v0 s).
        -- apply (E (forallH v a) v0 s).
        -- eapply Nat.le_trans.
           ++ apply H1.
              apply depthForall.
           ++ assert
               (H2: Nat.max (codeTerm (var (newVar (v0 :: freeVarT (L:=L) s ++ 
                                                      freeVarF a))))
                      (cPair 0
                         (pow3 (depth L a) +
                            fold_right Nat.max 0
                              (v
                                 :: freeVarT  (L:=L)
                                 (var (newVar (v0 :: freeVarT (L:=L) s ++ 
                                                 freeVarF a))) ++
                                 varFormula a))) <= C).
              { assert
                  (H2: newVar (v0 :: freeVarT s ++ freeVarF a) <=
                         pow3 (depth L a) +
                           fold_right Nat.max 0 (v0 :: freeVarT s ++ 
                                                   varFormula (forallH v a))).
                { apply Nat.le_trans with
                    (1 +
                       fold_right Nat.max 0
                         (v0 :: fold_right Nat.max 0 (freeVarT s) :: varFormula a)).
                  - apply boundSubFormulaHelp2 with (a := a) (v0 := v0) (s := s).
                  - apply Nat.add_le_mono.
                    + apply pow3Min.
                    + simpl; apply Nat.max_case.
                      * apply Nat.le_max_l.
                      * eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
                        apply Nat.max_case.
                        -- apply maxLemma2.
                        -- eapply Nat.le_trans; [ idtac | apply maxLemma3 ].
                           simpl; apply Nat.le_max_r.
                } 
                apply Nat.max_case.
                - replace
                    (codeTerm (var (newVar (v0 :: freeVarT s ++ 
                                              freeVarF a)))) 
                    with
                    (cPair 0 (newVar (v0 :: freeVarT s ++ freeVarF a)));
                    [ idtac | reflexivity ].
                  unfold C; eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
                  apply cPairLe3.
                  + apply le_n.
                  + eapply Nat.le_trans.
                    apply H2.
                    apply Nat.add_le_mono_r.
                    simpl; apply Nat.le_add_r.
                - unfold C; eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
                  apply cPairLe3.
                  + apply le_n.
                  + simpl; rewrite <- Nat.add_assoc.
                    apply Nat.add_le_mono_l.
                    apply Nat.max_case.
                    * eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
                      eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
                      eapply Nat.le_trans; [ idtac | apply maxLemma3 ].
                      simpl; apply Nat.le_max_l.
                    * apply Nat.max_case.
                      -- rewrite <- Nat.add_assoc.
                         eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
                         apply H2.
                      -- eapply Nat.le_trans; 
                           [ idtac | apply Compat815.Compat815.le_plus_r ].
                         eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
                         eapply Nat.le_trans; [ idtac | apply maxLemma3 ].
                         simpl; apply Nat.le_max_r.
              } 
              assert
                (H3: ReplaceFormulaTerm (codeFormula a)
                       (Nat.max
                          (codeTerm (var (newVar (v0 :: freeVarT (L:=L) s ++ 
                                                    freeVarF a))))
                          (cPair 0
                             (pow3 (depth L a) +
                                fold_right Nat.max 0
                                  (v
                                     :: freeVarT  (L:=L)
                                     (var
                                        (newVar (v0 :: freeVarT s ++ 
                                                   freeVarF a))) ++
                                     varFormula a)))) <=
                       ReplaceFormulaTerm (cPair 3 (cPair v (codeFormula a))) C).
              { unfold ReplaceFormulaTerm at 2; fold A;
                  unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
                repeat rewrite computeEvalStrongRecHelp.
                unfold compose2, evalComposeFunc, evalOneParamList, evalList;
                  simpl; unfold A at 1.
                repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
                rewrite D with (m := codeFormula a).
                -- simpl; eapply Nat.le_trans; [ idtac | apply cPairLe2 ].
                   eapply Nat.le_trans; [ idtac | apply cPairLe2 ].
                   apply ReplaceFormulaTermMonotone.
                   simpl in H2.
                   apply H2.
                -- eapply Nat.le_lt_trans; [ idtac | apply cPairLt2 ].
                   apply cPairLe2.
                   } 
                   apply boundComputationMonotone.
    ** apply le_n.
    ** unfold cTriple in |- *.
       repeat apply cPairLe3.
       apply H2.
       apply H2.
       apply H3.
    ** apply H3.
        -- eapply Nat.le_trans.
           ++ apply H1.
              eapply eqDepth.
              symmetry; apply subFormulaDepth.
              apply depthForall.
           ++  rewrite subFormulaDepth.
               assert
                 (H2: Nat.max (codeTerm s)
                        (cPair 0
                           (pow3 (depth L a) +
                              fold_right Nat.max 0
                                (v0
                                   :: freeVarT s ++
                                   varFormula
                                   (substF a v
                                      (var
                                         (newVar (v0 :: freeVarT s ++ 
                                                    freeVarF  a))))))) 
                      <=
                        C).
               { 
                 unfold C; apply maxLemma.
                 - apply le_n.
                 - apply cPairLe3.
                   + apply le_n.
                   + simpl; rewrite <- Nat.add_assoc.
                     apply Nat.add_le_mono_l.
                     apply Nat.max_case.
                     * eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
                       apply Nat.le_max_l.
                     * induction
                         (maxApp (freeVarT s)
                            (varFormula
                               (substF a v
                                  (var (newVar (v0 :: freeVarT s ++ 
                                                  freeVarF a)))))) as [a1 | b1].
                       -- rewrite a1.
                          eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
                          eapply Nat.le_trans; [ idtac | apply Nat.le_max_r ].
                          apply maxLemma2.
                       -- rewrite b1.
                          clear b0.
                          eapply Nat.le_trans.
                          ++ apply boundSubFormulaHelp1.
                          ++ apply Nat.add_le_mono_l.
                             apply maxLemma.
                             apply le_n.
                             apply Nat.max_case.
                             apply maxLemma2.
                             eapply Nat.le_trans; [ idtac | apply maxLemma3 ].
                             simpl; apply maxLemma.
                             apply le_n.
                             apply Nat.max_case; apply le_n.
               } 
               assert
                 (H3: ReplaceFormulaTerm
                        (codeFormula
                           (substF a v
                              (var (newVar (v0 :: freeVarT s ++ 
                                              freeVarF a)))))
                        (Nat.max (codeTerm s)
                           (cPair 0
                              (pow3 (depth L a) +
                                 fold_right Nat.max 0
                                   (v0
                                      :: freeVarT s ++
                                      varFormula
                                      (substF  a v
                                         (var
                                            (newVar
                                               (v0 :: freeVarT s ++ 
                                                  freeVarF a)))))))) 
                      <=
                        ReplaceFormulaTerm (cPair 3 (cPair v (codeFormula a))) C).
               { unfold ReplaceFormulaTerm at 2; fold A.
                 unfold evalStrongRec, evalComposeFunc, evalOneParamList, evalList.
                 repeat rewrite computeEvalStrongRecHelp.
                 unfold compose2, evalComposeFunc, evalOneParamList, evalList.
                 simpl; unfold A at 1;
                   repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
                 rewrite D with (m := codeFormula a).
                 - simpl; eapply Nat.le_trans; [ idtac | apply cPairLe2 ].
                   eapply Nat.le_trans; [ idtac | apply cPairLe2 ].
                   rewrite ReplaceFormulaTermSub.
                   apply ReplaceFormulaTermMonotone.
                   apply H2.
                 - eapply Nat.le_lt_trans; [ idtac | apply cPairLt2 ].
                   apply cPairLe2.
                   } 
                   apply boundComputationMonotone.
   ** apply le_n.
   ** unfold cTriple in |- *.
      repeat apply cPairLe3.
      apply H2.
      apply H2.
      apply H3.
   ** apply H3.
      *  unfold cTriple in |- *.
        repeat apply cPairLe3.
        -- unfold C; simpl.
        apply
          (H (pow3 (depth L a) + (pow3 (depth L a) + pow3 (depth L a))) v0
             (fold_right Nat.max 0 (freeVarT s ++ v :: varFormula a)) 
             (codeTerm s)).
        -- unfold C in |- *; simpl in |- *. 
           apply Nat.le_max_l.
        -- apply (H0 (forallH v a) v0 s).
        -- apply (E (forallH v a) v0 s).
        -- eapply Nat.le_trans.
           ++ apply H1.
              apply depthForall.
           ++ assert
               (H2: Nat.max (codeTerm s)
                      (cPair 0
                         (pow3 (depth L a) +
                            fold_right Nat.max 0 (v0 :: freeVarT s ++ 
                                                    varFormula a))) <= C).
              { unfold C in |- *.
                apply maxLemma.
                - apply le_n.
                - apply cPairLe3.
                  + apply le_n.
                  + apply Nat.add_le_mono.
                    * simpl in |- *.
                      apply Nat.le_add_r.
                    * simpl; apply maxLemma.
                      -- apply le_n.
                      -- induction (maxApp (freeVarT s) (varFormula a)) 
                           as [a0 | b2].
                         ++ rewrite a0.
                            apply maxLemma2.
                         ++ rewrite b2.
                            eapply Nat.le_trans; [ idtac | apply maxLemma3 ].
                            simpl; apply Nat.le_max_r.
              } 
              assert
                (H4: ReplaceFormulaTerm (codeFormula a)
                       (Nat.max (codeTerm s)
                          (cPair 0
                             (pow3 (depth L a) +
                                fold_right Nat.max 0 (v0 :: freeVarT s ++ 
                                                        varFormula a)))) 
                     <=
                       ReplaceFormulaTerm (cPair 3 (cPair v (codeFormula a))) C).
              { unfold ReplaceFormulaTerm at 2; fold A; unfold evalStrongRec,
                  evalComposeFunc, evalOneParamList, evalList.
                repeat rewrite computeEvalStrongRecHelp.
                unfold compose2, evalComposeFunc, evalOneParamList, evalList.
                simpl; unfold A at 1.
                repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
                rewrite D with (m := codeFormula a).
                - simpl; eapply Nat.le_trans; [ idtac | apply cPairLe2 ].
                  eapply Nat.le_trans; [ idtac | apply cPairLe2 ].
                  apply ReplaceFormulaTermMonotone.
                  apply H2.
                - eapply Nat.le_lt_trans; [ idtac | apply cPairLt2 ].
                  apply cPairLe2.
              } 
              eapply Nat.le_trans; [ idtac | apply cPairLe1 ].
              apply boundComputationMonotone.
        ** apply le_n.
        ** unfold cTriple in |- *.
           repeat apply cPairLe3.
           apply H2.
           apply H2.
           apply H4.
        ** apply H4.
    + unfold makeTrace in |- *.
      rewrite
        (Formula_depth_rec2_forall L)
        with
        (Q := 
           fun _ : fol.Formula L =>
             (nat * fol.Term L)%type)
        (P := fun _ : fol.Formula L => nat).
      * unfold makeTraceForall at 1 in |- *.
        reflexivity.
      * apply makeTraceImpNice.
      * apply makeTraceNotNice.
      * apply makeTraceForallNice.
Qed.

Definition codeSubFormula (f v s : nat) : nat :=
  let C := cPair 0 (pow3 f + (v + (s + f))) in
  car
    (boundedSearch
       (fun p x : nat =>
        ltBool 0 (checkSubFormulaTrace (cPair (car p) x)))
       (cPair (cTriple v s f)
          (S
             (boundComputation f (cTriple C C (ReplaceFormulaTerm f C))
                (ReplaceFormulaTerm f C))))).

Lemma codeSubFormulaCorrect (f : Formula) (v : nat) (s : Term):
 codeSubFormula (codeFormula f) v (codeTerm s) =
 codeFormula (substF f v s).
Proof.
  unfold codeSubFormula; 
    set
      (P :=
         fun p x : nat => ltBool 0 (checkSubFormulaTrace (cPair (car p) x))).
  set
    (b :=
       boundComputation (codeFormula f)
         (cTriple
            (cPair 0 (pow3 (codeFormula f) + (v + (codeTerm s + codeFormula f))))
            (cPair 0 (pow3 (codeFormula f) + (v + (codeTerm s + codeFormula f))))
            (ReplaceFormulaTerm (codeFormula f)
               (cPair 0
                  (pow3 (codeFormula f) + (v + (codeTerm s + codeFormula f))))))
         (ReplaceFormulaTerm (codeFormula f)
            (cPair 0 (pow3 (codeFormula f) + (v + (codeTerm s + codeFormula f)))))).
  induction
    (boundedSearch2 P (cPair (cTriple v (codeTerm s) (codeFormula f)) (S b))) as [H | ?].
  - assert
      (H0: P (cPair (cTriple v (codeTerm s) (codeFormula f)) (S b))
             (cdr (makeTrace f (v, s))) = true).
    { unfold P; rewrite cPairProjections1.
      replace
        (cPair (cTriple v (codeTerm s) (codeFormula f))
           (cdr (makeTrace f (v, s)))) 
        with 
        (makeTrace f (v, s)).
      - rewrite makeTraceCorrect.
        unfold ltBool in |- *.
        induction (le_lt_dec 1 0) as [a | b0].
        + now lia. 
        +  reflexivity.
      - transitivity
          (cPair (car (makeTrace f (v, s))) (cdr (makeTrace f (v, s)))).
        + symmetry  in |- *.
          apply cPairProjections.
        + rewrite makeTrace1.
          reflexivity.
    } 
    assert
      (H1: P (cPair (cTriple v (codeTerm s) (codeFormula f)) (S b))
             (cdr (makeTrace f (v, s))) = false).
    { apply boundedSearch1.
      rewrite H.
      eapply Nat.lt_le_trans; [ idtac | apply cPairLe2 ].
      apply Nat.lt_succ_r.
      eapply
        Nat.le_trans
        with
        (cPair (car (makeTrace f (v, s)))
           (cdr (makeTrace f (v, s)))).
      + apply cPairLe2.
      + rewrite cPairProjections.
        eapply Nat.le_trans.
        * apply boundMakeTrace.
        * unfold b in |- *.
          assert (H1: depth L f <= codeFormula f).
          { clear H0 H b P s v.
            induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
              simpl in |- *.
            - apply Nat.le_0_l.
            - apply Nat.le_0_l.
            - apply Compat815.lt_n_Sm_le.
              rewrite <-  Nat.succ_lt_mono.
              eapply Nat.le_lt_trans; [ idtac | apply cPairLt2 ].
              apply Nat.max_case.
              eapply Nat.le_trans.
              + apply Hrecf1.
              + apply cPairLe1.
              + eapply Nat.le_trans.
                * apply Hrecf0.
                * apply cPairLe2.
            - apply Compat815.lt_n_Sm_le.
              rewrite <-  Nat.succ_lt_mono.
              eapply Nat.le_lt_trans; [ idtac | apply cPairLt2 ].
              assumption.
            - apply Compat815.lt_n_Sm_le.
              rewrite <- Nat.succ_lt_mono. 
              eapply Nat.le_lt_trans; [ idtac | apply cPairLt2 ].
              eapply Nat.le_trans.
              + apply Hrecf.
              + apply cPairLe2.
          } 
          assert
            (H2: Nat.max (codeTerm s)
                   (cPair 0
                      (pow3 (depth L f) +
                         fold_right Nat.max 0 (v :: freeVarT s ++ varFormula f))) 
                 <=
                   cPair 0 (pow3 (codeFormula f) + (v + (codeTerm s + codeFormula f)))).
          { apply Nat.max_case.
            - eapply Nat.le_trans; [ idtac | apply cPairLe2 ].
              eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
              eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
              apply Nat.le_add_r.
            - apply cPairLe3.
              + apply le_n.
              + apply Nat.add_le_mono.
                * apply pow3Monotone.
                  assumption.
                * simpl in |- *.
                  apply Nat.max_case.
                  -- apply Nat.le_add_r.
                  -- eapply Nat.le_trans; [ idtac | apply Compat815.le_plus_r ].
                     induction (maxApp (freeVarT s) (varFormula f)) as [a | b0].
                     ++ rewrite a; eapply Nat.le_trans.
                        ** apply codeTermFreeVar.
                        ** apply Nat.le_add_r.
                     ++ rewrite b0.
                        eapply Nat.le_trans with (codeFormula f).
                        ** clear b0 H1 H0 H b P s v.
                           induction f as 
                             [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
                             simpl in |- *.
                           --- eapply Nat.le_trans; [ idtac | apply cPairLe2 ].
                               induction (maxApp (freeVarT t) (freeVarT t0))
                                 as [a | b].
                               +++ rewrite a.
                                   eapply Nat.le_trans.
                                   *** apply codeTermFreeVar.
                                   *** apply cPairLe1.
                               +++ rewrite b; eapply Nat.le_trans.
                                   *** apply codeTermFreeVar.
                                   *** apply cPairLe2.
                           --- eapply Nat.le_trans; [ idtac | apply cPairLe2 ].
                               induction t as [| n t t0 Hrect].
                               +++ simpl in |- *.
                                   apply Nat.le_0_l.
                               +++ replace (freeVarTs (Tcons t t0)) 
                                     with
                                     (freeVarT t ++ freeVarTs t0);
                                     [ idtac | reflexivity ].
                                   replace (codeTerms (Tcons t t0)) 
                                     with
                                     (S (cPair (codeTerm t) (codeTerms t0))); 
                                     [ idtac | reflexivity ].
                                   apply le_S.
                                   induction (maxApp (freeVarT t) 
                                                (freeVarTs  t0)) as [a | b].
                                   *** rewrite a; eapply Nat.le_trans.
                                       apply codeTermFreeVar.
                                       apply cPairLe1.
                                   *** rewrite b; eapply Nat.le_trans.
                                       apply Hrect.
                                       apply cPairLe2.
                           --- eapply Nat.le_trans; [ idtac | apply cPairLe2 ].
                               induction (maxApp (varFormula f1) (varFormula f0)) 
                                 as [a | b].
                               +++ rewrite a; eapply Nat.le_trans.
                                   *** apply Hrecf1.
                                   *** apply cPairLe1.
                               +++ rewrite b.
                                   eapply Nat.le_trans.
                                   *** apply Hrecf0.
                                   *** apply cPairLe2.
                           --- eapply Nat.le_trans.
                               +++ apply Hrecf.
                               +++ apply cPairLe2.
                           --- eapply Nat.le_trans; [ idtac | apply cPairLe2 ].
                               apply Nat.max_case.
                               +++ apply cPairLe1.
                               +++ eapply Nat.le_trans.
                                   *** apply Hrecf.
                                   *** apply cPairLe2.
                        ** rewrite Nat.add_comm. 
                           apply Nat.le_add_r.
                           }  
                           apply boundComputationMonotone.
          --  assumption.
          -- unfold cTriple in |- *.
             repeat apply cPairLe3.
             assumption.
             assumption.
             apply ReplaceFormulaTermMonotone.
             assumption.
          -- apply ReplaceFormulaTermMonotone.
             assumption.
    } 
    rewrite H0 in H1.
    discriminate H1.
  - unfold P at 1 in H.
    rewrite cPairProjections1 in H.
    symmetry; apply checkTraceCorrect
      with
      (m := cdr
              (boundedSearch P
                 (cPair (cTriple v (codeTerm s) (codeFormula f)) (S b)))).
   intros H0; unfold cTriple at 1 in H0.
   rewrite cPairProjections in H0.
   rewrite H0 in H; cbn in H; discriminate.
Qed.

Lemma codeSubFormulaIsPR : isPR 3 codeSubFormula.
Proof.
  unfold codeSubFormula; apply  compose3_1IsPR  with
    (f := fun f v s : nat =>
            boundedSearch
              (fun p x : nat =>
                 ltBool 0 (checkSubFormulaTrace (cPair (car p) x)))
              (cPair (cTriple v s f)
                 (S
                    (boundComputation f
                       (cTriple (cPair 0 (pow3 f + (v + (s + f))))
                          (cPair 0 (pow3 f + (v + (s + f))))
                          (ReplaceFormulaTerm f
                             (cPair 0 (pow3 f + (v + (s + f))))))
                       (ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f))))))))).
  apply
    compose3_1IsPR
    with
    (f := fun f v s : nat =>
            cPair (cTriple v s f)
              (S
                 (boundComputation f
                    (cTriple (cPair 0 (pow3 f + (v + (s + f))))
                       (cPair 0 (pow3 f + (v + (s + f))))
                       (ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f))))))
                    (ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f)))))))).
  - apply
      compose3_2IsPR
      with
      (f1 := fun f v s : nat => cTriple v s f)
      (f2 := fun f v s : nat =>
               S
                 (boundComputation f
                    (cTriple (cPair 0 (pow3 f + (v + (s + f))))
                       (cPair 0 (pow3 f + (v + (s + f))))
                       (ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f))))))
                    (ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f))))))).
    + apply compose3_3IsPR with
        (f1 := fun f v s : nat => v)
        (f2 := fun f v s : nat => s)
        (f3 := fun f v s : nat => f).
      * apply pi2_3IsPR.
      * apply pi3_3IsPR.
      * apply pi1_3IsPR.
      * apply cTripleIsPR.
    + apply compose3_1IsPR with
        (f := fun f v s : nat =>
                boundComputation f
                  (cTriple (cPair 0 (pow3 f + (v + (s + f))))
                     (cPair 0 (pow3 f + (v + (s + f))))
                     (ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f))))))
                  (ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f)))))).
      assert (H: isPR 3 (fun f v s : nat => cPair 0 (pow3 f + (v + (s + f))))).
      { apply compose3_2IsPR with
          (f1 := fun f v s : nat => 0)
          (f2 := fun f v s : nat => pow3 f + (v + (s + f))).
        - apply filter100IsPR with (g := fun _ : nat => 0).
          apply const1_NIsPR.
        - apply compose3_2IsPR with
            (f1 := fun f v s : nat => pow3 f)
            (f2 := fun f v s : nat => v + (s + f)).
          + apply filter100IsPR.
            apply pow3IsPR.
          + apply compose3_2IsPR with 
              (f1 := fun f v s : nat => v) (f2 := fun f v s : nat => s + f).
            * apply pi2_3IsPR.
            * apply filter101IsPR with (g := fun f s : nat => s + f).
              apply swapIsPR.
              apply plusIsPR.
            * apply plusIsPR.
          + apply plusIsPR.
        - apply cPairIsPR.
      } 
      assert
        (H0: isPR 3
               (fun f v s : nat =>
                  ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f)))))).
      { apply compose3_2IsPR with
          (f1 := fun f v s : nat => f)
          (f2 := fun f v s : nat => cPair 0 (pow3 f + (v + (s + f)))).
        - apply pi1_3IsPR.
        - assumption.
        - apply ReplaceFormulaTermIsPR.
      } 
      apply compose3_3IsPR with
        (f1 := fun f v s : nat => f)
        (f2 := fun f v s : nat =>
                 cTriple (cPair 0 (pow3 f + (v + (s + f))))
                   (cPair 0 (pow3 f + (v + (s + f))))
                   (ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f))))))
        (f3 := fun f v s : nat =>
                 ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f))))).
  * apply pi1_3IsPR.
  * apply compose3_3IsPR with
      (f1 := fun f v s : nat => cPair 0 (pow3 f + (v + (s + f))))
      (f2 := fun f v s : nat => cPair 0 (pow3 f + (v + (s + f))))
      (f3 := fun f v s : nat =>
               ReplaceFormulaTerm f (cPair 0 (pow3 f + (v + (s + f)))));
      try assumption.
    apply cTripleIsPR.
  * assumption.
  * apply boundComputationIsPR.
  * apply succIsPR.
    + apply cPairIsPR.
  - apply boundSearchIsPR with
      (P := fun p x : nat =>
              ltBool 0 (checkSubFormulaTrace (cPair (car p) x))).
    unfold isPRrel in |- *.
    apply
      compose2_2IsPR
      with
      (f := fun p x : nat => 0)
      (g := fun p x : nat => checkSubFormulaTrace (cPair (car p) x))
      (h := charFunction 2 ltBool).
    + apply filter10IsPR with (g := fun _ : nat => 0).
      apply const1_NIsPR.
    + apply compose2_1IsPR with (f := fun p x : nat => cPair (car p) x).
      * apply compose2_2IsPR with 
          (f := fun p x : nat => car p) (g := fun p x : nat => x).
        -- apply filter10IsPR.
           apply cPairPi1IsPR.
        -- apply pi2_2IsPR.
        -- apply cPairIsPR.
      * apply checkTraceIsPR.
    + apply ltIsPR.
  - apply cPairPi1IsPR.
Qed.

End Code_Substitute_Formula.


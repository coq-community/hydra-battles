Require Import Arith.
Require Import Coq.Lists.List.
Require Import ListExt.
Require Import folProp.
Require Import subProp.
Require Import extEqualNat.
Require Import LNN.

Section RepresentableExpressible.

Variable T : System.
Hypothesis closedT1: (ClosedSystem LNN T).

Lemma closedT : forall v : nat, ~ In_freeVarSys LNN v T.
Proof.
  intros v [x H]; elim closedT1 with v x; tauto.
Qed.

Fixpoint RepresentableHalf1 (n : nat) :
  naryFunc n -> Formula -> Prop :=
  match n return (naryFunc n -> Formula -> Prop) with
  | O =>
      fun (f : naryFunc 0) (A : Formula) =>
      SysPrf T (impH A (equal (var 0) (natToTerm f)))
  | S m =>
      fun (f : naryFunc (S m)) (A : Formula) =>
      forall a : nat,
      RepresentableHalf1 m (f a)
        (substituteFormula LNN A (S m) (natToTerm a))
  end.

Fixpoint RepresentableHalf2 (n : nat) : naryFunc n -> Formula -> Prop :=
  match n return (naryFunc n -> Formula -> Prop) with
  | O =>
      fun (f : naryFunc 0) (A : Formula) =>
      SysPrf T (impH (equal (var 0) (natToTerm f)) A)
  | S m =>
      fun (f : naryFunc (S m)) (A : Formula) =>
      forall a : nat,
      RepresentableHalf2 m (f a)
        (substituteFormula LNN A (S m) (natToTerm a))
  end.

Lemma RepresentableHalf1Alternate :
 forall (n : nat) (f : naryFunc n) (A B : Formula),
 SysPrf T (impH A B) -> RepresentableHalf1 n f B -> 
 RepresentableHalf1 n f A.
Proof.
  induction n as [| n Hrecn]; intros f A B H H0.
  -  simpl in H0 |- *.
     now apply impTrans with B.
  - simpl in H0 |- *.
    intros a; 
      apply Hrecn with (substituteFormula LNN B (S n) (natToTerm a)).
    + rewrite <- (subFormulaImp LNN).
      apply forallE, forallI. 
      * apply closedT.
      * apply H. 
    + apply H0.
Qed.

Lemma RepresentableHalf2Alternate :
 forall (n : nat) (f : naryFunc n) (A B : Formula),
   SysPrf T (impH A B) -> RepresentableHalf2 n f A -> 
   RepresentableHalf2 n f B.
Proof.
  induction n as [| n Hrecn]; intros.
  - simpl in H0 |- *.
    apply impTrans with A; [assumption| apply H].
   - simpl in H0 |- *; intro a. 
     apply Hrecn with (substituteFormula LNN A (S n) (natToTerm a)).
     + rewrite <- (subFormulaImp LNN); apply forallE.
       apply forallI.  
       * apply closedT.
       * auto.
     + apply H0.
Qed.

Fixpoint RepresentableHelp (n : nat) : naryFunc n -> Formula -> Prop :=
  match n return (naryFunc n -> Formula -> Prop) with
  | O =>
      fun (f : naryFunc 0) (A : Formula) =>
      SysPrf T (iffH A (equal (var 0) (natToTerm f)))
  | S m =>
      fun (f : naryFunc (S m)) (A : Formula) =>
      forall a : nat,
      RepresentableHelp m (f a) 
        (substituteFormula LNN A (S m) (natToTerm a))
  end.

Lemma RepresentableHalfHelp :
 forall (n : nat) (f : naryFunc n) (A : Formula),
 RepresentableHalf1 n f A ->
 RepresentableHalf2 n f A -> RepresentableHelp n f A.
Proof.
  induction n as [| n Hrecn]; simpl in |- *; intros.
  - apply iffI; auto.
  - apply Hrecn; auto.
Qed.

Definition Representable (n : nat) (f : naryFunc n) 
  (A : Formula) : Prop :=
  (forall v : nat, In v (freeVarFormula LNN A) -> v <= n) /\
  RepresentableHelp n f A.

Lemma RepresentableAlternate :
 forall (n : nat) (f : naryFunc n) (A B : Formula),
 SysPrf T (iffH A B) -> RepresentableHelp n f A -> 
 RepresentableHelp n f B.
Proof.
  induction n as [| n Hrecn]; intros.
  - simpl in H0 |- *; apply iffTrans with A.
    +  now apply iffSym.
    + auto.
  - simpl in H0 |- *; intro a.
    apply Hrecn with (substituteFormula LNN A (S n) (natToTerm a)).
    + rewrite <- (subFormulaIff LNN).
      apply forallE, forallI. 
      * apply closedT.
      * auto.
    + apply H0.
Qed.

Lemma Representable_ext :
 forall (n : nat) (f g : naryFunc n) (A : Formula),
   extEqual n f g -> RepresentableHelp n f A -> 
   RepresentableHelp n g A.
Proof.
  induction n as [| n Hrecn].
  - simpl in |- *.
    intros f g A H H0; now rewrite <- H.
  - simpl in |- *; intros f g A H H0 a; eapply Hrecn.
    + apply H.
    + auto.
Qed.

Fixpoint ExpressibleHelp (n : nat) : naryRel n -> Formula -> Prop :=
  match n return (naryRel n -> Formula -> Prop) with
  | O =>
      fun (R : naryRel 0) (A : Formula) =>
      match R with
      | true => SysPrf T A
      | false => SysPrf T (notH A)
      end
  | S m =>
      fun (R : naryRel (S m)) (A : Formula) =>
      forall a : nat,
      ExpressibleHelp m (R a)
        (substituteFormula LNN A (S m) (natToTerm a))
  end.

Definition Expressible (n : nat) (R : naryRel n) (A : Formula) : Prop :=
  (forall v : nat, In v (freeVarFormula LNN A) -> 
                   v <= n /\ v <> 0) /\
  ExpressibleHelp n R A.

Lemma expressibleAlternate :
  forall (n : nat) (R : naryRel n) (A B : Formula),
    SysPrf T (iffH A B) -> ExpressibleHelp n R A -> 
    ExpressibleHelp n R B.
Proof.
  induction n as [| n Hrecn]; intros.
  - induction R.
    + simpl in H0 |- *.
      apply impE with A.
      * apply iffE1, H.
      * apply H0. 
    + simpl in H0 |- *.
      apply impE with (notH A).
      * apply cp2.
        now apply iffE2.
      * apply H0. 
  - simpl in H0 |- *. 
  intros a;
    apply (Hrecn (R a)) with 
    (substituteFormula LNN A (S n) (natToTerm a)).
  + rewrite <- (subFormulaIff LNN).
    apply forallE.
    apply forallI.
    * now apply closedT. 
    * auto. 
  + apply H0.
Qed.

Hypothesis nn1:(SysPrf T (notH (equal (natToTerm 1) (natToTerm 0)))).

Lemma Representable2Expressible :
 forall (n : nat) (R : naryRel n) (A : Formula),
 Representable n (charFunction n R) A ->
 Expressible n R (substituteFormula LNN A 0 (natToTerm 1)).
Proof.
  intros n R A [H H0]; split.
  - intros v H1; induction (freeVarSubFormula3 _ _ _ _ _ H1).
    split.
   + apply H.
     eapply In_list_remove1.
     apply H2.
   + eapply In_list_remove2.
     apply H2.
   + elim H2.
  - clear H.
    generalize H0 as H.
    generalize A; clear H0 A.
      induction n as [| n Hrecn]; intros.
      + simpl in H |- *.
        induction R.
        * simpl in H.
          apply impE with
            (substituteFormula LNN (equal (var 0) (Succ Zero))
               0 (Succ Zero)).
          -- apply iffE2.
            rewrite <- (subFormulaIff LNN).
            apply forallE.
            apply forallI.
            ++ apply closedT.
            ++  apply H.
          -- rewrite (subFormulaEqual LNN).
             simpl in |- *.
             apply eqRefl.
        * simpl in H.
          apply  impE with
            (notH (substituteFormula LNN (equal (var 0) Zero) 
          0 (Succ Zero))).
          -- apply cp2.
             apply iffE1.
             rewrite <- (subFormulaIff LNN).
             apply forallE.
             apply forallI.
            ++ apply closedT.
            ++ apply H.
          -- rewrite (subFormulaEqual LNN); simpl in |- *.
             replace (@apply LNN Languages.Zero (Tnil LNN)) with
              (natToTerm 0) by reflexivity. 
            replace (Succ Zero) with (natToTerm 1) by reflexivity.
            simpl; apply nn1.
      + simpl in H |- *.
        intros a; 
          apply expressibleAlternate with
          (substituteFormula LNN 
             (substituteFormula LNN A (S n) (natToTerm a)) 0
             (Succ Zero)).
        * apply (subFormulaExch LNN).
          -- discriminate.
          -- apply closedNatToTerm.
          -- auto.
        * apply Hrecn; apply H.
Qed.

End RepresentableExpressible.

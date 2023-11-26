(**  expressible.v 

     Original file by Russel O'Connor
*)


From Coq Require Import Arith List.
From hydras.Ackermann 
  Require Import ListExt folProp subProp extEqualNat Languages LNN
  NewNotations.
Import NNnotations.

#[local] Arguments apply _ _ _ : clear implicits.

Section RepresentableExpressible.

Variable T : System.

Hypothesis closedT1: (ClosedSystem LNN T).

Remark closedT : forall v : nat, ~ In_freeVarSys LNN v T.
Proof.
  intros v [x [? ?]]; now destruct (closedT1 v x).  
Qed.

Fixpoint RepresentableHalf1 (n : nat) :
  naryFunc n -> Formula -> Prop :=
  match n return (naryFunc n -> Formula -> Prop) with
  | O =>
      fun (f : naryFunc 0) (A : Formula) =>
      SysPrf T (A -> v#0 = natToTerm f)%fol
  | S m =>
      fun (f : naryFunc (S m)) (A : Formula) =>
      forall a : nat,
      RepresentableHalf1 m (f a)
        (substF A (S m) (natToTerm a))
  end.

Fixpoint RepresentableHalf2 (n : nat) : naryFunc n -> Formula -> Prop :=
  match n return (naryFunc n -> Formula -> Prop) with
  | O =>
      fun (f : naryFunc 0) (A : Formula) =>
      SysPrf T (v#0 = natToTerm f -> A)%fol
  | S m =>
      fun (f : naryFunc (S m)) (A : Formula) =>
      forall a : nat,
      RepresentableHalf2 m (f a)
        (substF A (S m) (natToTerm a))
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
      apply Hrecn with (substF B (S n) (natToTerm a)).
    + rewrite <- (subFormulaImp LNN).
      apply forallE, forallI. 
      * apply closedT.
      * apply H. 
    + apply H0.
Qed.

Lemma RepresentableHalf2Alternate :
 forall (n : nat) (f : naryFunc n) (A B : Formula),
   SysPrf T (A -> B)%fol -> RepresentableHalf2 n f A -> 
   RepresentableHalf2 n f B.
Proof.
  induction n as [| n Hrecn]; intros.
  - simpl in H0 |- *.
    apply impTrans with A; [assumption| apply H].
   - simpl in H0 |- *; intro a. 
     apply Hrecn with (substF A (S n) (natToTerm a)).
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
      SysPrf T (A <-> v#0 = natToTerm f)%fol
  | S m =>
      fun (f : naryFunc (S m)) (A : Formula) =>
      forall a : nat,
      RepresentableHelp m (f a) 
        (substF A (S m) (natToTerm a))
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
  (forall v : nat, In v (freeVarF A) -> v <= n) /\
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
    apply Hrecn with (substF A (S n) (natToTerm a)).
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
      | false => SysPrf T ( ~ A)%fol
      end
  | S m =>
      fun (R : naryRel (S m)) (A : Formula) =>
      forall a : nat,
      ExpressibleHelp m (R a)
        (substF A (S m) (natToTerm a))
  end.

Definition Expressible (n : nat) (R : naryRel n) (A : Formula) : Prop :=
  (forall v : nat, In v (freeVarF A) -> 
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
      apply impE with (~ A)%fol.
      * apply cp2.
        now apply iffE2.
      * apply H0. 
  - simpl in H0 |- *. 
  intros a;
    apply (Hrecn (R a)) with 
    (substF A (S n) (natToTerm a)).
  + rewrite <- (subFormulaIff LNN).
    apply forallE.
    apply forallI.
    * now apply closedT. 
    * auto. 
  + apply H0.
Qed.

Hypothesis nn1: SysPrf T (natToTerm 1 <> natToTerm 0)%fol.

Lemma Representable2Expressible :
 forall (n : nat) (R : naryRel n) (A : Formula),
 Representable n (charFunction n R) A ->
 Expressible n R (substF A 0 (natToTerm 1)).
Proof.
  intros n R A [H H0]; split.
  - intros v H1; induction (freeVarSubFormula3 _ _ _ _ _ H1).
    split.
   + apply H.
     eapply in_remove.
     apply H2.
   + eapply in_remove_neq.
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
            (substF (v#0 = Succ Zero)%fol  0 (Succ Zero)).
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
            (~ (substF (v#0 = Zero) 0 (Succ Zero)))%fol.
          -- apply cp2.
             apply iffE1.
             rewrite <- (subFormulaIff LNN).
             apply forallE.
             apply forallI.
            ++ apply closedT.
            ++ apply H.
          -- rewrite (subFormulaEqual LNN); simpl in |- *.
             replace (apply LNN Languages.Zero_ (Tnil)) with
              (natToTerm 0) by reflexivity. 
            replace (Succ Zero) with (natToTerm 1) by reflexivity.
            simpl; apply nn1.
      + simpl in H |- *.
        intros a; 
          apply expressibleAlternate with
          (substF  
             (substF A (S n) (natToTerm a)) 0
             (Succ Zero)).
        * apply (subFormulaExch LNN).
          -- discriminate.
          -- apply closedNatToTerm.
          -- auto.
        * apply Hrecn; apply H.
Qed.

End RepresentableExpressible.

Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Peano_dec.

Require Import ListExt.
Require Import folProof.
Require Import folLogic.
Require Import folProp.

Section Replacement.

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
Let impH := impH L.
Let notH := notH L.
Let forallH := forallH L.
Let orH := orH L.
Let andH := andH L.
Let existH := existH L.
Let iffH := iffH L.
Let ifThenElseH := ifThenElseH L.
Let SysPrf := SysPrf L.

Lemma reduceImp :
  forall (f1 f2 f3 f4 : Formula) (T : System),
    SysPrf T (iffH f1 f3) ->
    SysPrf T (iffH f2 f4) -> 
    SysPrf T (iffH (impH f1 f2) (impH f3 f4)).
Proof.
  assert
    (H: forall (f1 f2 f3 f4 : Formula) (T : System),
        SysPrf T (iffH f1 f3) ->
        SysPrf T (iffH f2 f4) -> 
        SysPrf T (impH (impH f1 f2) (impH f3 f4))).
  { 
    intros f1 f2 f3 f4 T H H0; repeat apply (impI L);
      apply impE with f2.
    - repeat apply sysWeaken.
      apply (iffE1 L), H0. 
    - apply impE with f1.
      apply sysWeaken.
      apply Axm; right; constructor.
      apply impE with f3.
      + repeat apply sysWeaken.
        apply (iffE2 L).
        apply H.
      + apply Axm; right; constructor.
  } 
  intros f1 f2 f3 f4 T H0 H1; apply (iffI L).
  - apply H; auto.
  - apply H; apply (iffSym L); auto.
Qed.

Lemma reduceNot (f1 f2 : Formula) (T : System):
 SysPrf T (iffH f1 f2) -> SysPrf T (iffH (notH f1) (notH f2)).
Proof.
  assert
    (H: forall (f1 f2 : Formula) (T : System),
        SysPrf T (iffH f1 f2) -> SysPrf T (impH (notH f1) (notH f2)))
    by (intros f0 f3 T0 H; apply (cp2 L), (iffE2 L), H).
  intros H0; apply (iffI L).
  - now apply H.
  - apply H; now apply (iffSym L).
Qed.

Lemma impForall (f1 f2 : Formula) (v : nat) (T : System):
  ~ In_freeVarSys _ v T ->
  SysPrf T (impH f1 f2) -> SysPrf T (impH (forallH v f1) (forallH v f2)).
Proof.
  intros H H0; apply (impI L), (forallI L).
  - intros [x [H1 H2]]; destruct H2 as [x H2| x H2]; [ idtac | induction H2 ].
    + apply H; exists x; now split.
    + apply (In_list_remove2 _ _ _ _ _ H1); easy. 
  - apply impE with f1.
    + apply sysWeaken, H0. 
    + eapply forallSimp.
      apply Axm; right; constructor.
Qed.

Lemma reduceForall (f1 f2 : Formula) (v : nat) (T : System):
 ~ In_freeVarSys _ v T ->
 SysPrf T (iffH f1 f2) -> SysPrf T (iffH (forallH v f1) (forallH v f2)).
Proof.
intros H H0; apply (iffI L).
- apply impForall; [assumption |]; apply (iffE1 L), H0. 
- apply impForall; [assumption |]; apply (iffE2 L), H0.
Qed.

Lemma reduceOr (f1 f2 f3 f4 : Formula) (T : System):
 SysPrf T (iffH f1 f3) ->
 SysPrf T (iffH f2 f4) -> SysPrf T (iffH (orH f1 f2) (orH f3 f4)).
Proof.
  revert f1 f2 f3 f4 T;
    assert
      (H: forall f1 f2 f3 f4 T,
          SysPrf T (iffH f1 f3) ->
          SysPrf T (iffH f2 f4) -> SysPrf T (impH (orH f1 f2) (orH f3 f4))).
  { intros f1 f2 f3 f4 T H H0; apply impI, orSys.
    + apply (orI1 L).
      apply impE with f1.
      * apply sysWeaken, iffE1, H.
      * apply Axm; right; constructor.
    + apply orI2; apply impE with f2.
      * apply sysWeaken, iffE1, H0.
      * apply Axm; right; constructor.
  }
  intros; apply iffI. 
  + apply H;  assumption. 
  + apply H; apply iffSym; auto.
Qed.

Lemma reduceAnd (f1 f2 f3 f4 : Formula) (T : System):
    SysPrf T (iffH f1 f3) ->
    SysPrf T (iffH f2 f4) -> SysPrf T (iffH (andH f1 f2) (andH f3 f4)).
Proof.
  revert f1 f2 f3 f4 T;assert
    (H: forall (f1 f2 f3 f4 : Formula) (T : System),
        SysPrf T (iffH f1 f3) ->
        SysPrf T (iffH f2 f4) -> SysPrf T (impH (andH f1 f2) (andH f3 f4))).
  { intros f1 f2 f3 f4 T H H0; apply impI, andI.
    + apply impE with f1.
      * apply sysWeaken, iffE1, H.  
      * eapply andE1; apply Axm; right; constructor.
    + apply impE with f2.
      * apply sysWeaken, iffE1, H0. 
      * eapply andE2; apply Axm; right; constructor.
  } 
  intros ? ? ? ? ? ? ?; apply (iffI L).
  - apply H; auto.
  - apply H; apply (iffSym L); auto.
Qed.

Lemma iffExist (f1 f2 : Formula) (v : nat) (T : System):
 ~ In_freeVarSys _ v T ->
 SysPrf T (impH f1 f2) -> SysPrf T (impH (existH v f1) (existH v f2)).
Proof.
  intros H H0; apply cp2, impForall; [apply H| apply cp2, H0 ]. 
Qed.

Lemma reduceExist (f1 f2 : Formula) (v : nat) (T : System):
  ~ In_freeVarSys _ v T ->
  SysPrf T (iffH f1 f2) -> SysPrf T (iffH (existH v f1) (existH v f2)).
Proof.
  intros H H0; apply reduceNot.
  apply reduceForall; [easy | apply reduceNot, H0 ].  
Qed.

Lemma reduceIff (f1 f2 f3 f4 : Formula) (T : System):
 SysPrf T (iffH f1 f3) ->
 SysPrf T (iffH f2 f4) -> SysPrf T (iffH (iffH f1 f2) (iffH f3 f4)).
Proof.
  revert f1 f2 f3 f4 T; 
    assert (H: 
        forall (f1 f2 f3 f4 : Formula) (T : System),
          SysPrf T (iffH f1 f3) ->
          SysPrf T (iffH f2 f4) -> 
          SysPrf T (impH (iffH f1 f2) (iffH f3 f4))).
  { intros f1 f2 f3 f4 T H H0; apply impI; apply iffTrans with f2.
    - apply iffTrans with f1.
      + apply sysWeaken, iffSym, H.
      + apply Axm; right; constructor.
    - apply sysWeaken, H0.
  } 
  intros ? ? ? ? ? ? ?; apply iffI.
  - apply H; auto.
  - apply H; apply iffSym; assumption.  
Qed.

Lemma reduceIfThenElse (f1 f2 f3 f4 f5 f6 : Formula) (T : System):
 SysPrf T (iffH f1 f4) ->
 SysPrf T (iffH f2 f5) ->
 SysPrf T (iffH f3 f6) ->
 SysPrf T (iffH (ifThenElseH f1 f2 f3) (ifThenElseH f4 f5 f6)).
Proof.
intros; apply reduceAnd; apply reduceImp.
- assumption. 
- assumption. 
- apply reduceNot; assumption. 
- assumption. 
Qed. 


Lemma reduceSub  (T : System) (v : nat) (s : Term) (f g : Formula):
 ~ In_freeVarSys L v T ->
 SysPrf T (iffH f g) ->
 SysPrf T (iffH (substituteFormula L f v s) (substituteFormula L g v s)).
Proof.
  revert T v s f g;
  assert
    (H: forall (T : System) (v : nat) (s : Term) (f g : Formula),
        ~ In_freeVarSys L v T ->
        SysPrf T (iffH f g) ->
        SysPrf T (impH (substituteFormula L f v s)
                    (substituteFormula L g v s))).
  { intros T v s f g H H0; rewrite <- (subFormulaImp  L).
    apply forallE; apply forallI. 
    - apply H. 
    - apply (iffE1 L), H0. 
  }
  intros t v s f g H0 H1; apply iffI.
   - apply H. 
     + apply H0.   
     + apply H1. 
   - apply H; [assumption| now apply iffSym ]. 
Qed.

Lemma reduceCloseList (l : list nat) (f1 f2 : Formula) (T : System):
 (forall v : nat, In v l -> ~ In_freeVarSys _ v T) ->
 SysPrf T (iffH f1 f2) ->
 SysPrf T (iffH (closeList L l f1) (closeList L l f2)).
Proof.
  revert T f1 f2; induction l as [| a l Hrecl]; simpl in |- *; intros.
  - apply H0.
  - apply reduceForall.
    + apply H; now left.
    + apply Hrecl; auto.
Qed.

End Replacement.

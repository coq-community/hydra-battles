Require Import Ensembles.
Require Import Coq.Lists.List.

Require Import ListExt.
Require Import folProof.
Require Import folProp.
Require Import Deduction.

Section Logic_Rules.

Variable L : Language.
Let Formula := Formula L.
Let Formulas := Formulas L.
Let System := System L.
Let Term := Term L.
Let Terms := Terms L.
Let Prf := Prf L.
Let SysPrf := SysPrf L.

Lemma Axm T f: mem _ T f -> SysPrf T f.
Proof.
  exists (f :: nil); exists (AXM L f).
  intros g [H0 | H0].
  - rewrite H0 in H; assumption.
  - elim H0.
Qed.

Lemma sysExtend  (T U : System) (f : Formula): 
 Included _ T U -> SysPrf T f -> SysPrf U f.
Proof.
  intros H [x [p H0]]; exists x, p.
  intros g H1.
  apply H, H0, H1. 
Qed.

Lemma sysWeaken  (T : System) (f g : Formula):
  SysPrf T f -> SysPrf (Ensembles.Add _ T g) f.
Proof.
  intros H; apply sysExtend with T.
  - unfold Included in |- *.
    intros f0 Hf0;  now left. 
  - assumption.
Qed.

Lemma impI (T : System) (f g : Formula):
 SysPrf (Ensembles.Add _ T g) f -> SysPrf T (impH g f).
Proof. intros ?; now apply (DeductionTheorem L). Qed.

Lemma impE (T : System) (f g : Formula):
 SysPrf T (impH g f) -> SysPrf T g -> SysPrf T f.
Proof. 
  intros (x, (px, Hx)) (x1, (px1, Hx1)).
  set (A1 := MP L _ _ _ _ px px1) in *.
  exists (x ++ x1), A1.
  intros g0 H; case (in_app_or _ _ _ H); auto.
Qed.

Lemma contradiction (T : System) (f g : Formula):
 SysPrf T f -> SysPrf T (notH f) -> SysPrf T g.
Proof.
  intros H H0; eapply impE with f.
  - eapply impE with (impH (notH g) (notH f)).
    + exists (nil (A:=Formula)).
      exists (CP L g f).
      contradiction.
    + apply impI; apply sysWeaken.
      assumption.
  - assumption.
Qed.

Lemma nnE (T : System) (f : Formula):
  SysPrf T (notH (notH f)) -> SysPrf T f.
Proof.
  intros H; apply impE with (notH (notH f)).
  - apply impE with (impH (notH f) (notH (notH (notH f)))).
    + exists (nil (A:=Formula)).
      exists (CP L f (notH (notH f))).
      contradiction.
    + apply impI.
      apply contradiction with (notH f).
      apply Axm.
      right; constructor.
      apply sysWeaken; assumption.
  - assumption.
Qed.

Lemma noMiddle  (T : System) (f : Formula):
  SysPrf T (orH (notH f) f).
Proof.
  unfold orH in |- *.
  apply impI, nnE, Axm; right; constructor.
Qed.

Lemma nnI (T : System) (f : Formula):
  SysPrf T f -> SysPrf T (notH (notH f)).
Proof.
  intros H; apply impE with f; [ | apply H].
  apply impE with (impH (notH (notH (notH f))) (notH f)).
  - exists (nil (A:=Formula)).
    exists (CP L (notH (notH f)) f); contradiction.
  - apply impI; apply contradiction with f.
    + apply sysWeaken; assumption.
    + apply nnE, Axm; right; constructor.
Qed.

(* contraposition *)
Lemma cp1 (T : System) (f g : Formula) :
 SysPrf T (impH (notH f) (notH g)) -> SysPrf T (impH g f).
Proof.
  intros H; apply impE with (impH (notH f) (notH g)).
  - exists (nil (A:=Formula)).
    exists (CP L f g); contradiction.
  - assumption.
Qed.

Lemma cp2 (T : System) (f g : Formula):
 SysPrf T (impH g f) -> SysPrf T (impH (notH f) (notH g)).
Proof.
  intros H.
  apply impE with (impH (notH (notH g)) (notH (notH f))).
  - exists (nil (A:=Formula)).
    exists (CP L (notH g) (notH f)); contradiction.
  - apply impI, nnI. 
    apply impE with g.
    + apply sysWeaken; assumption.
    + apply nnE, Axm; right; constructor.
Qed.

Lemma orI1 (T : System) (f g : Formula):
  SysPrf T f -> SysPrf T (orH f g).
Proof.
  intros H; unfold orH in |- *.
  apply impI.
  apply contradiction with f.
  apply sysWeaken; assumption.
  apply Axm; right; constructor.
Qed.

Lemma orI2 (T : System) (f g : Formula):
  SysPrf T g -> SysPrf T (orH f g).
Proof.
  intros h; unfold orH in |- *.
  apply impI, sysWeaken; assumption.
Qed.

Lemma orE (T : System) (f g h : Formula):
 SysPrf T (orH f g) ->
 SysPrf T (impH f h) -> SysPrf T (impH g h) -> SysPrf T h.
Proof.
  intros H H0 H1; unfold orH in H.
  apply impE with (impH h h).
  - apply cp1.
    apply impE with (impH (notH h) h).
    + apply impI.
      apply impI.
      apply contradiction with h.
      apply impE with (notH h).
      apply Axm; left; right; constructor.
      apply Axm; right; constructor.
      apply Axm; right; constructor.
    + apply impI.
      apply impE with g.
      apply sysWeaken; assumption.
      apply impE with (notH f).
      apply sysWeaken; assumption.
      apply impE with (notH h).
      * apply cp2.
        apply sysWeaken; assumption.
      * apply Axm; right; constructor.
  - apply impI, Axm; right; constructor.
Qed.

Lemma orSys (T : System) (f g h : Formula):
 SysPrf (Ensembles.Add _ T f) h -> SysPrf (Ensembles.Add _ T g) h -> 
 SysPrf (Ensembles.Add _ T (orH f g)) h.
Proof.
  intros H H0; eapply orE.
   - apply Axm; right; constructor.
   - apply sysWeaken, impI; assumption.
   - apply sysWeaken, impI; assumption. 
Qed.

Lemma andI (T : System) (f g : Formula):
 SysPrf T f -> SysPrf T g -> SysPrf T (andH f g).
Proof.
  intros H H0; unfold andH in |- *.
  apply orE with (notH (orH (notH f) (notH g))) (orH (notH f) (notH g)).
  - apply noMiddle.
  - apply impI, Axm; right; constructor.
  - apply impI; apply orE with (notH f) (notH g).
    + apply Axm; right; constructor.
    + apply cp2; apply impI.
      repeat apply sysWeaken; assumption.
    + apply cp2; apply impI.
      repeat apply sysWeaken; assumption.
Qed.

Lemma andE1 (T : System) (f g : Formula):
  SysPrf T (andH f g) -> SysPrf T f.
Proof.
  intros H; apply nnE.
  apply impE with (andH f g).
  unfold andH in |- *; apply cp2.
  apply impI, orI1. 
  apply Axm; right; constructor.
  assumption.
Qed.

Lemma andE2  (T : System) (f g : Formula):
  SysPrf T (andH f g) -> SysPrf T g.
Proof.
  intros H; apply nnE.
  apply impE with (andH f g).
  - apply cp2, impI, orI2, Axm; right; constructor.
  - assumption.
Qed.

Lemma iffI  (T : System) (f g : Formula) :
 SysPrf T (impH f g) -> SysPrf T (impH g f) -> SysPrf T (iffH f g).
Proof. intros H H0; apply andI; auto. Qed.

Lemma iffE1 (T : System) (f g : Formula):
  SysPrf T (iffH f g) -> SysPrf T (impH f g).
Proof. intros H; eapply andE1. eexact H. Qed.

Lemma iffE2  (T : System) (f g : Formula):
  SysPrf T (iffH f g) -> SysPrf T (impH g f).
Proof. intros H; eapply andE2, H. Qed.

Lemma forallI (T : System) (f : Formula) (v : nat):
 ~ In_freeVarSys L v T -> SysPrf T f -> SysPrf T (forallH v f).
Proof.
  intros H [x [x0 H0]]; exists x. 
  assert (~ In v (freeVarListFormula L x)).
  { intro H1; apply H. 
    destruct  (In_freeVarListFormulaE _ _ _ H1) as [x1 H2].
    exists x1; split. 
    - tauto.
    - apply H0; tauto.
  }
  exists (GEN L _ _ _ H1 x0); apply H0.
Qed.

Lemma forallE  (T : System) (f : Formula) (v : nat) (t : Term):
 SysPrf T (forallH v f) -> SysPrf T (substituteFormula L f v t).
Proof.
  intro H; apply impE with (forallH v f); [| exact H]. 
   - exists (nil (A:=Formula)), (FA1 L f v t); contradiction.
Qed.

Lemma forallSimp (T : System) (f : Formula) (v : nat):
 SysPrf T (forallH v f) -> SysPrf T f.
Proof.
  intros H; rewrite <- subFormulaId with L f v;  now apply forallE.
Qed.

Lemma existI (T : System) (f : Formula) (v : nat) (t : Term):
  SysPrf T (substituteFormula L f v t) -> SysPrf T (existH v f).
Proof.
  intros H; unfold existH, fol.existH in |- *;
  apply impE with (notH (notH (substituteFormula L f v t))).
  - apply cp2, impI; rewrite <- (subFormulaNot L).
    apply forallE, Axm; right; constructor.
  - now apply nnI.
Qed.

Lemma existE (T : System) (f g : Formula) (v : nat):
 ~ In_freeVarSys L v T ->
 ~ In v (freeVarFormula L g) ->
 SysPrf T (existH v f) -> SysPrf T (impH f g) -> SysPrf T g.
Proof.
  intros H H0 H1 H2. apply nnE. 
  apply impE with (notH (forallH v (notH f))).
  - apply cp2, impI.
    apply impE with (forallH v (notH g)).
    + apply impE with (forallH v (impH (notH g) (notH f))).
      * exists (nil (A:=Formula)).
        exists (FA3 L (notH g) (notH f) v).
        contradiction.
      * apply sysWeaken.
        apply forallI. 
        -- apply H.
        -- now apply cp2.
    + apply impE with (notH g).
      * exists (nil (A:=Formula)).
        exists (FA2 L (notH g) v H0).
        contradiction.
      * apply Axm; right; constructor.
  - apply H1. 
Qed.

Lemma existSimp  (T : System) (f : Formula) (v : nat) :
 SysPrf T f -> SysPrf T (existH v f).
Proof.
  intros H; eapply existI; now rewrite subFormulaId.
Qed.

Lemma existSys (T : System) (f g : Formula) (v : nat):
 ~ In_freeVarSys L v T ->
 ~ In v (freeVarFormula L g) ->
 SysPrf (Ensembles.Add _ T f) g -> 
 SysPrf (Ensembles.Add _ T (existH v f)) g.
Proof.
  intros H H0 H1; eapply existE.
  - intros [x H2]; destruct H.
    exists x.
    destruct H2 as [H2 H3]; split. 
    + apply H2.
    + destruct H3 as [x H3| x H3].
      * assumption.
      * induction H3; simpl in H2; absurd (v = v).
        -- eapply In_list_remove2.
           apply H2.
        -- reflexivity. 
  - assumption.
  - apply Axm; right; constructor.
  - apply sysWeaken; now apply impI.
Qed.

Section Not_Rules.

Lemma absurd1  (T : System) (f : Formula) :
 SysPrf T (impH f (notH f)) -> SysPrf T (notH f).
Proof. 
  intros H; apply orE with (notH f) f.
  - apply noMiddle.
  - apply impI; apply Axm; right; constructor.
  - assumption.
Qed.

Lemma nImp  (T : System) (f g : Formula) :
 SysPrf T (andH f (notH g)) -> SysPrf T (notH (impH f g)).
Proof.
  intros H; apply absurd1.
  apply impI; apply contradiction with g.
  - apply impE with f.
    + apply Axm; right; constructor.
    + eapply andE1.
      apply sysWeaken, H. 
  - apply sysWeaken; eapply andE2; apply H.
Qed.

Lemma nOr (T : System) (f g : Formula):
 SysPrf T (andH (notH f) (notH g)) -> SysPrf T (notH (orH f g)).
Proof.
  intros H; apply absurd1, impI, orSys.
  - apply contradiction with f.
    + apply Axm; right; constructor.
    + apply sysWeaken; eapply andE1; apply H.
  - apply contradiction with g.
    + apply Axm; right; constructor.
    + apply sysWeaken; eapply andE2; apply H.
Qed.

Lemma nAnd (T : System) (f g : Formula):
 SysPrf T (orH (notH f) (notH g)) -> SysPrf T (notH (andH f g)).
Proof.
  intros H; unfold andH; apply nnI, H. 
Qed.

Lemma nForall  (T : System) (f : Formula) (v : nat) :
 SysPrf T (existH v (notH f)) -> SysPrf T (notH (forallH v f)).
Proof.
  intros H; apply impE with (existH v (notH f)).
  - apply sysExtend with (Empty_set Formula).
    intros g H0. destruct H0. 
    apply impI; apply existSys.
    intros [x [H0 H1]]; destruct H1. 
    simpl in |- *; intro H0. 
    absurd (v = v).
    + eapply In_list_remove2.
      apply H0.
    + reflexivity.
    + apply impE with (notH f).
      * apply cp2, sysWeaken, impI.
        eapply forallSimp.
        apply Axm; right; constructor.
      * apply Axm; right; constructor.
  - assumption.
Qed.

Lemma nExist (T : System) (f : Formula) (v : nat):
 SysPrf T (forallH v (notH f)) -> SysPrf T (notH (existH v f)).
Proof.
  intros H;  now apply nnI.
Qed.

End Not_Rules.

Section Other_Rules.

Lemma impRefl (T : System) (f : Formula):  SysPrf T (impH f f).
Proof.
  apply impI, Axm ; right. constructor. 
Qed.

Lemma impTrans (T : System) (f g h : Formula):
 SysPrf T (impH f g) -> SysPrf T (impH g h) -> 
 SysPrf T (impH f h).
Proof.
  intros H H0; apply impI; apply impE with g.
  - apply sysWeaken, H0. 
  - apply impE with f.
   + apply sysWeaken, H. 
   + apply Axm; right; constructor.
Qed.

Lemma orSym (T : System) (f g : Formula):
 SysPrf T (orH f g) -> SysPrf T (orH g f).
Proof.
  intros H; eapply orE.
  - apply H.
  - apply impI, orI2, Axm; right; constructor.
  - apply impI, orI1, Axm; right; constructor. 
Qed.

Lemma andSym (T : System) (f g : Formula):
  SysPrf T (andH f g) -> SysPrf T (andH g f).
Proof.
  intros H; apply andI.
  - eapply andE2; apply H.
  - eapply andE1; apply H.
Qed.

Lemma iffRefl (T : System) (f : Formula) :
  SysPrf T (iffH f f).
Proof. apply iffI; apply impRefl. Qed.

Lemma iffSym (T : System) (f g : Formula) :
 SysPrf T (iffH f g) -> SysPrf T (iffH g f).
Proof. intro H; now apply andSym. Qed.

Lemma iffTrans (T : System) (f g h : Formula):
 SysPrf T (iffH f g) -> SysPrf T (iffH g h) -> 
 SysPrf T (iffH f h).
Proof.
  intros H H0; apply iffI.
  - eapply impTrans.
    + apply iffE1, H.
    + apply iffE1, H0. 
  - eapply impTrans.
    + apply iffE2, H0. 
    + apply iffE2, H.
Qed.

End Other_Rules.

Lemma openClosed (T : System) (f : Formula):
 SysPrf T (close L f) -> SysPrf T f.
Proof.
unfold close;
  generalize (no_dup nat Peano_dec.eq_nat_dec 
                (freeVarFormula L f)); intros l H; 
  induction l as [| a l Hrecl].
  - apply H.
  - simpl in H; apply Hrecl; eapply forallSimp; apply H.
Qed.

End Logic_Rules.

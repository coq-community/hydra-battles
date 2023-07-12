(** folLogic.v:

    Original script by Russel O'Connor *)


From Coq Require Import Ensembles List.

Require Import ListExt folProof folProp Deduction.
Import FolNotations.

Section Logic_Rules.

Variable L : Language.
Let Formula := Formula L.
Let Formulas := Formulas L.
Let System := System L.
Let Term := Term L.
Let Terms := Terms L.
Let Prf := Prf L.
Let SysPrf := SysPrf L.
Arguments Ensembles.Add {U} _ _.

(* begin snippet Axm:: no-out *)
Lemma Axm T f: mem _ T f -> SysPrf T f.
Proof.
  exists (f :: nil), (AXM L f).
  intros g [ | []]; now subst.
Qed.
(* end snippet Axm *)

(* begin snippet sysExtend:: no-out *)
Lemma sysExtend  (T U : System) (f : Formula): 
 Included _ T U -> SysPrf T f -> SysPrf U f.
Proof.
  intros H [x [p H0]]; exists x, p.
  intros g H1; apply H, H0, H1. 
Qed.

Lemma sysWeaken  (T : System) (f g : Formula):
  SysPrf T f -> SysPrf (Ensembles.Add  T g) f.
  (* ... *)
(* end snippet sysExtend:: no-out *)
Proof.
  intros H; apply sysExtend with T.
  - intros f0 Hf0; now left. 
  - assumption.
Qed.

(* begin snippet impI:: no-out *)
Lemma impI (T : System) (f g : Formula):
 SysPrf (Ensembles.Add  T g) f -> SysPrf T (g -> f)%fol.
Proof. intros ?; now apply (DeductionTheorem L). Qed.
(* end snippet impI *)

(* begin snippet impE:: no-out *)
Lemma impE (T : System) (f g : Formula):
 SysPrf T (g -> f)%fol -> SysPrf T g -> SysPrf T f.
Proof. 
  intros [x [px Hx]] [x1 [px1 Hx1]].
  set (A1 := MP L _ _ _ _ px px1); exists (x ++ x1), A1.
  (* ... *)
(* end snippet impE *)
  intros g0 H; case (in_app_or  _ _ _ H); auto.
Qed.

(* begin snippet contradiction:: no-out *)
Lemma contradiction (T : System) (f g : Formula):
 SysPrf T f -> SysPrf T (~ f)%fol -> SysPrf T g.
Proof.
  intros H H0; eapply impE with f.
  - eapply impE with (~ g -> ~ f)%fol. 
    + exists (nil (A:=Formula)).
      exists (CP L g f); contradiction.
    + apply impI; now apply sysWeaken.
  - assumption.
Qed.
(* end snippet contradiction *)

(* begin snippet nnE:: no-out *)
Lemma nnE (T : System) (f : Formula): SysPrf T (~ ~ f)%fol -> SysPrf T f.
(* end snippet nnE *)
Proof.
  intros H; apply impE with (~ ~ f)%fol.
  - apply impE with (~ f -> ~ ~ ~ f)%fol.
    + exists (nil (A:=Formula)).
      exists (CP L f (~ ~ f)%fol); contradiction.
    + apply impI.
      apply contradiction with (~ f)%fol.
      apply Axm.
      right; constructor.
      apply sysWeaken; assumption.
  - assumption.
Qed.

(* begin snippet nnI:: no-out *)
Lemma nnI (T : System) (f : Formula): SysPrf T f -> SysPrf T (~ ~ f)%fol.
(* end snippet nnI *)
Proof.
  intros H; apply impE with f; [ | apply H].
  apply impE with (~ ~ ~ f -> ~ f)%fol.
  - exists (nil (A:=Formula)).
    exists (CP L (~ ~ f)%fol f); contradiction.
  - apply impI; apply contradiction with f.
    + apply sysWeaken; assumption.
    + apply nnE, Axm; right; constructor.
Qed.

(**  contraposition *)

(* begin snippet cp1:: no-out *)
Lemma cp1 (T : System) (f g : Formula) :
 SysPrf T (~ f -> ~ g)%fol -> SysPrf T (g -> f)%fol.
(* end snippet cp1 *)
Proof.
  intros H; apply impE with (~ f -> ~g)%fol.
  - exists (nil (A:=Formula)).
    exists (CP L f g); contradiction.
  - assumption.
Qed.

(* begin snippet cp2:: no-out *)
Lemma cp2 (T : System) (f g : Formula):
 SysPrf T (g -> f)%fol -> SysPrf T (~f -> ~g)%fol.
(* end snippet cp2 *)
Proof.
  intros H; apply impE with (~ ~ g -> ~ ~ f)%fol.
  - exists (nil (A:=Formula)).
    exists (CP L (~ g)%fol (~ f)%fol); contradiction.
  - apply impI, nnI; apply impE with g.
    + apply sysWeaken; assumption.
    + apply nnE, Axm; right; constructor.
Qed.

(* begin snippet orI1 *)
Lemma orI1 (T : System) (f g : Formula): SysPrf T f -> SysPrf T (f \/ g)%fol.
      (* .no-out *)
Proof.  (* .no-out *)
  intros H; apply impI; apply contradiction with f. (* -.h#* .h#H *)
  (* ... *)  
(* end snippet orI1 *)
  - apply sysWeaken; assumption.
  - apply Axm; right; constructor.
Qed.

(* begin snippet orI2:: no-out *)
Lemma orI2 (T : System) (f g : Formula): SysPrf T g -> SysPrf T (f \/ g)%fol.
(* end snippet orI2 *)
Proof.
  intros h; unfold orH; apply impI, sysWeaken; assumption.
Qed.

(* begin snippet noMiddle:: no-out *)
Lemma noMiddle  (T : System) (f : Formula):  SysPrf T (~ f \/ f)%fol.
Proof.
   apply impI, nnE, Axm; right; constructor.
Qed.
(* end snippet noMiddle *)


Lemma orE (T : System) (f g h : Formula):
 SysPrf T (f \/ g)%fol ->
 SysPrf T (f -> h)%fol -> SysPrf T (g -> h)%fol -> SysPrf T h.
Proof.
  intros H H0 H1; unfold orH in H.
  apply impE with (h -> h)%fol.
  - apply cp1.
    apply impE with (~ h -> h)%fol.
    + do 2 apply impI; apply contradiction with h.
      apply impE with (~ h)%fol.
      apply Axm; left; right; constructor.
      apply Axm; right; constructor.
      apply Axm; right; constructor.
    + apply impI.
      apply impE with g.
      apply sysWeaken; assumption.
      apply impE with (~ f)%fol.
      apply sysWeaken; assumption.
      apply impE with (~ h)%fol.
      * apply cp2.
        apply sysWeaken; assumption.
      * apply Axm; right; constructor.
  - apply impI, Axm; right; constructor.
Qed.

Lemma orSys (T : System) (f g h : Formula):
 SysPrf (Ensembles.Add  T f) h -> SysPrf (Ensembles.Add T g) h -> 
 SysPrf (Ensembles.Add  T (f \/ g)%fol) h.
Proof.
  intros H H0; eapply orE.
   - apply Axm; right; constructor.
   - apply sysWeaken, impI; assumption.
   - apply sysWeaken, impI; assumption. 
Qed.

Lemma andI (T : System) (f g : Formula):
 SysPrf T f -> SysPrf T g -> SysPrf T (f /\ g)%fol.
Proof.
  intros H H0; unfold andH;
  apply orE with (~ (~f \/ ~g))%fol (~ f \/ ~g)%fol.
  - apply noMiddle.
  - apply impI, Axm; right; constructor.
  - apply impI; apply orE with (~ f)%fol (~ g)%fol.
    + apply Axm; right; constructor.
    + apply cp2; apply impI.
      repeat apply sysWeaken; assumption.
    + apply cp2; apply impI.
      repeat apply sysWeaken; assumption.
Qed.

Lemma andE1 (T : System) (f g : Formula):
  SysPrf T (f /\ g)%fol -> SysPrf T f.
Proof.
  intros H; apply nnE.
  apply impE with ( f /\ g)%fol.
  unfold andH in |- *; apply cp2.
  apply impI, orI1. 
  apply Axm; right; constructor.
  assumption.
Qed.

Lemma andE2  (T : System) (f g : Formula):
  SysPrf T (f /\ g)%fol -> SysPrf T g.
Proof.
  intros H; apply nnE.
  apply impE with (f /\ g)%fol.
  - apply cp2, impI, orI2, Axm; right; constructor.
  - assumption.
Qed.

Lemma iffI  (T : System) (f g : Formula) :
 SysPrf T (f -> g)%fol -> SysPrf T (g -> f)%fol -> SysPrf T (f <-> g)%fol.
Proof. intros H H0; apply andI; auto. Qed.

Lemma iffE1 (T : System) (f g : Formula):
  SysPrf T (f <-> g)%fol -> SysPrf T (f -> g)%fol.
Proof. intros H; eapply andE1. eexact H. Qed.

Lemma iffE2  (T : System) (f g : Formula):
  SysPrf T (f <-> g)%fol -> SysPrf T (g -> f)%fol.
Proof. intros H; eapply andE2, H. Qed.

Lemma forallI (T : System) (f : Formula) (v : nat):
 ~ In_freeVarSys L v T -> SysPrf T f -> SysPrf T (allH v, f)%fol.
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
 SysPrf T (allH v, f)%fol -> SysPrf T (substF L f v t).
Proof.
  intro H; apply impE with (forallH v f); [| exact H]. 
   - exists (nil (A:=Formula)), (FA1 L f v t); contradiction.
Qed.

Lemma forallSimp (T : System) (f : Formula) (v : nat):
  SysPrf T (allH v, f)%fol -> SysPrf T f.
Proof.
  intros H; rewrite <- subFormulaId with L f v;  now apply forallE.
Qed.

Lemma existI (T : System) (f : Formula) (v : nat) (t : Term):
  SysPrf T (substF L f v t) -> SysPrf T (exH v, f)%fol.
Proof.
  intros H; unfold existH, fol.existH in |- *;
  apply impE with (~ ~ (substF L f v t))%fol.
  - apply cp2, impI; rewrite <- (subFormulaNot L).
    apply forallE, Axm; right; constructor.
  - now apply nnI.
Qed.

Lemma existE (T : System) (f g : Formula) (v : nat):
 ~ In_freeVarSys L v T ->
 ~ In v (freeVarF L g) ->
 SysPrf T (exH v, f)%fol -> SysPrf T (f -> g)%fol -> SysPrf T g.
Proof.
  intros H H0 H1 H2. apply nnE. 
  apply impE with (~ (allH v, ~ f))%fol.
  - apply cp2, impI.
    apply impE with (allH v, ~ g)%fol.
    + apply impE with (allH v, ~ g -> ~ f)%fol.
      * exists (nil (A:=Formula)).
        exists (FA3 L (~g)%fol (~f)%fol v).
        contradiction.
      * apply sysWeaken.
        apply forallI. 
        -- apply H.
        -- now apply cp2.
    + apply impE with (~ g)%fol.
      * exists (nil (A:=Formula)).
        exists (FA2 L (~ g)%fol v H0); contradiction.
      * apply Axm; right; constructor.
  - apply H1. 
Qed.

Lemma existSimp  (T : System) (f : Formula) (v : nat) :
 SysPrf T f -> SysPrf T (exH v, f)%fol.
Proof.
  intros H; eapply existI; now rewrite subFormulaId.
Qed.

Lemma existSys (T : System) (f g : Formula) (v : nat):
 ~ In_freeVarSys L v T ->
 ~ In v (freeVarF L g) ->
 SysPrf (Ensembles.Add T f) g -> 
 SysPrf (Ensembles.Add  T (exH v, f)%fol) g.
Proof.
  intros H H0 H1; eapply existE.
  - intros [x H2]; destruct H.
    exists x.
    destruct H2 as [H2 H3]; split. 
    + apply H2.
    + destruct H3 as [x H3| x H3].
      * assumption.
      * induction H3; simpl in H2; absurd (v = v).
        -- eapply in_remove_neq.
           apply H2.
        -- reflexivity. 
  - assumption.
  - apply Axm; right; constructor.
  - apply sysWeaken; now apply impI.
Qed.

Section Not_Rules.

Lemma absurd1  (T : System) (f : Formula) :
 SysPrf T (f -> ~f)%fol -> SysPrf T (~f)%fol.
Proof. 
  intros H; apply orE with (~f)%fol f.
  - apply noMiddle.
  - apply impI; apply Axm; right; constructor.
  - assumption.
Qed.

Lemma nImp  (T : System) (f g : Formula) :
 SysPrf T (f /\  ~g)%fol -> SysPrf T (~ (f -> g))%fol.
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
 SysPrf T (~ f /\ ~ g)%fol -> SysPrf T (~ (f \/ g))%fol.
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
 SysPrf T (~ f \/ ~ g)%fol -> SysPrf T (~ (f /\ g))%fol.
Proof.
  intros H; unfold andH; apply nnI, H. 
Qed.

Lemma nForall  (T : System) (f : Formula) (v : nat) :
 SysPrf T (exH v, ~ f)%fol -> SysPrf T (~  (allH v, f))%fol.
Proof.
  intros H; apply impE with (exH v, ~ f)%fol.
  - apply sysExtend with (Empty_set Formula).
    intros g H0. destruct H0. 
    apply impI; apply existSys.
    intros [x [H0 H1]]; destruct H1. 
    simpl in |- *; intro H0. 
    absurd (v = v).
    + eapply in_remove_neq.
      apply H0.
    + reflexivity.
    + apply impE with (~ f)%fol.
      * apply cp2, sysWeaken, impI.
        eapply forallSimp.
        apply Axm; right; constructor.
      * apply Axm; right; constructor.
  - assumption.
Qed.

Lemma nExist (T : System) (f : Formula) (v : nat):
 SysPrf T (allH v, ~f)%fol -> SysPrf T (~ (exH v, f))%fol.
Proof.   intros H;  now apply nnI. Qed.

End Not_Rules.

Section Other_Rules.

Lemma impRefl (T : System) (f : Formula):  SysPrf T (f -> f)%fol.
Proof.  apply impI, Axm ; right; constructor. Qed.

Lemma impTrans (T : System) (f g h : Formula):
 SysPrf T (f -> g)%fol -> SysPrf T (g -> h)%fol -> SysPrf T (f -> h)%fol.
Proof.
  intros H H0; apply impI; apply impE with g.
  - apply sysWeaken, H0. 
  - apply impE with f.
   + apply sysWeaken, H. 
   + apply Axm; right; constructor.
Qed.

Lemma orSym (T : System) (f g : Formula):
 SysPrf T (f \/ g)%fol -> SysPrf T (g \/ f)%fol.
Proof.
  intros H; eapply orE.
  - apply H.
  - apply impI, orI2, Axm; right; constructor.
  - apply impI, orI1, Axm; right; constructor. 
Qed.

Lemma andSym (T : System) (f g : Formula):
  SysPrf T (f /\ g)%fol -> SysPrf T (g /\ f)%fol.
Proof.
  intros H; apply andI.
  - eapply andE2; apply H.
  - eapply andE1; apply H.
Qed.

Lemma iffRefl (T : System) (f : Formula) : SysPrf T (f <-> f)%fol.
Proof. apply iffI; apply impRefl. Qed.

Lemma iffSym (T : System) (f g : Formula) : 
  SysPrf T (f <->  g)%fol -> SysPrf T (g <-> f)%fol.
Proof. intro H; now apply andSym. Qed.

Lemma iffTrans (T : System) (f g h : Formula):
 SysPrf T (f <-> g)%fol -> SysPrf T (g <-> h)%fol -> SysPrf T (f <-> h)%fol.
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
  generalize (List.nodup Peano_dec.eq_nat_dec 
                (freeVarF L f)); intros l H; 
  induction l as [| a l Hrecl].
  - apply H.
  - simpl in H; apply Hrecl; eapply forallSimp; apply H.
Qed.

End Logic_Rules.

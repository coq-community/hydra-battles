
Require Import Arith.
Require Import Ensembles.
Require Import Coq.Lists.List.

Require Export Languages.
Require Import folProof.
Require Import folProp.
Require Import folLogic3.

(* begin snippet Instantiations *)
Definition Formula := Formula LNN.
Definition Formulas := Formulas LNN.
Definition System := System LNN.
Definition Sentence := Sentence LNN.
Definition Term := Term LNN.
Definition Terms := Terms LNN.
Definition ifThenElseH := ifThenElseH LNN.
Definition SysPrf := SysPrf LNN.

Definition Plus (x y : Term) : Term :=
  apply LNN Plus (Tcons LNN 1 x (Tcons LNN 0 y (Tnil LNN))).

Definition Times (x y : Term) : Term :=
  apply LNN Times (Tcons LNN 1 x (Tcons LNN 0 y (Tnil LNN))).

Definition Succ (x : Term) : Term :=
  apply LNN Succ (Tcons LNN 0 x (Tnil LNN)).

Definition Zero : Term := apply LNN Zero (Tnil LNN).
Search Relations. 
Check LT. 
Print LNNRelation. 
Definition LT (x y : Term) : Formula :=
  @atomic LNN LT (Tcons LNN 1 x (Tcons LNN 0 y (Tnil LNN))). 
(* end snippet Instantiations *)

Lemma LNN_dec : language_decidable LNN.
Proof. split; decide equality. Qed.

Section Free_Variables.

Lemma freeVarPlus (x y : Term) :
 freeVarTerm LNN (Plus x y) = freeVarTerm LNN x ++ freeVarTerm LNN y.
Proof. now rewrite (app_nil_end (freeVarTerm LNN y)). Qed.

Lemma freeVarTimes (x y : Term):
 freeVarTerm LNN (Times x y) = freeVarTerm LNN x ++ freeVarTerm LNN y.
Proof. now rewrite (app_nil_end (freeVarTerm LNN y)). Qed.

Lemma freeVarSucc (x : Term): 
  freeVarTerm LNN (Succ x) = freeVarTerm LNN x.
Proof.
  now rewrite (app_nil_end (freeVarTerm LNN x)).
Qed.

Lemma freeVarZero : freeVarTerm LNN Zero = nil.
Proof. reflexivity. Qed.

Lemma freeVarLT (x y : Term) :
 freeVarFormula LNN (LT x y) = freeVarTerm LNN x ++ freeVarTerm LNN y.
Proof.
  now rewrite (app_nil_end (freeVarTerm LNN y)).
Qed.

End Free_Variables.

Section Logic.

Lemma Axm (T : System) (f : Formula): mem _ T f -> SysPrf T f.
Proof. apply (Axm LNN). Qed.

Lemma sysExtend (T U : System) (f : Formula):
 Included _ T U -> SysPrf T f -> SysPrf U f.
Proof. apply (sysExtend LNN). Qed.

Lemma sysWeaken (T : System) (f g : Formula):
  SysPrf T f -> SysPrf (Ensembles.Add _ T g) f.
Proof. apply (sysWeaken LNN). Qed.

Lemma impI (T : System) (f g : Formula):
 SysPrf (Ensembles.Add _ T g) f -> SysPrf T (impH g f).
Proof. apply (impI LNN). Qed.

Lemma impE  (T : System) (f g : Formula):
  SysPrf T (impH g f) -> SysPrf T g -> SysPrf T f.
Proof. apply (impE LNN). Qed.

Lemma contradiction (T : System) (f g : Formula):
 SysPrf T f -> SysPrf T (notH f) -> SysPrf T g.
Proof. apply (contradiction LNN). Qed.

Lemma nnE (T : System) (f : Formula):
  SysPrf T (notH (notH f)) -> SysPrf T f.
Proof. apply (nnE LNN). Qed.

Lemma noMiddle (T : System) (f : Formula): SysPrf T (orH (notH f) f).
Proof. apply (noMiddle LNN). Qed.

Lemma nnI  (T : System) (f : Formula):
  SysPrf T f -> SysPrf T (notH (notH f)).
Proof. apply (nnI LNN). Qed.

Lemma cp1 (T : System) (f g : Formula) :
 SysPrf T (impH (notH f) (notH g)) -> SysPrf T (impH g f).
Proof. apply (cp1 LNN). Qed.

Lemma cp2 (T : System) (f g : Formula):
 SysPrf T (impH g f) -> SysPrf T (impH (notH f) (notH g)).
Proof. apply (cp2 LNN). Qed.

Lemma orI1 (T : System) (f g : Formula): SysPrf T f -> SysPrf T (orH f g).
Proof. apply (orI1 LNN). Qed.

Lemma orI2  (T : System) (f g : Formula): SysPrf T g -> SysPrf T (orH f g).
Proof. apply (orI2 LNN). Qed.

Lemma orE (T : System) (f g h : Formula):
  SysPrf T (orH f g) ->
  SysPrf T (impH f h) -> SysPrf T (impH g h) -> SysPrf T h.
Proof. apply (orE LNN). Qed.

Lemma orSys  (T : System) (f g h : Formula) :
 SysPrf (Ensembles.Add _ T f) h -> SysPrf (Ensembles.Add _ T g) h -> 
 SysPrf (Ensembles.Add _ T (orH f g)) h.
Proof. apply (orSys LNN). Qed.

Lemma andI (T : System) (f g : Formula):
 SysPrf T f -> SysPrf T g -> SysPrf T (andH f g).
Proof. apply (andI LNN). Qed.

Lemma andE1 (T : System) (f g : Formula): 
  SysPrf T (andH f g) -> SysPrf T f.
Proof. apply (andE1 LNN). Qed.

Lemma andE2  (T : System) (f g : Formula):
  SysPrf T (andH f g) -> SysPrf T g.
Proof. apply (andE2 LNN). Qed.

Lemma iffI (T : System) (f g : Formula):
 SysPrf T (impH f g) -> SysPrf T (impH g f) -> SysPrf T (iffH f g).
Proof. apply (iffI LNN). Qed.

Lemma iffE1 (T : System) (f g : Formula):
 SysPrf T (iffH f g) -> SysPrf T (impH f g).
Proof. apply (iffE1 LNN). Qed.

Lemma iffE2 (T : System) (f g : Formula):
 SysPrf T (iffH f g) -> SysPrf T (impH g f).
Proof. apply (iffE2 LNN). Qed.

Lemma forallI (T : System) (f : Formula) (v : nat):
 ~ In_freeVarSys LNN v T -> SysPrf T f -> SysPrf T (forallH v f).
Proof. apply (forallI LNN). Qed.

Lemma forallE  (T : System) (f : Formula) (v : nat) (t : Term):
 SysPrf T (forallH v f) -> SysPrf T (substituteFormula LNN f v t).
Proof. apply (forallE LNN). Qed.

Lemma forallSimp (T : System) (f : Formula) (v : nat) :
 SysPrf T (forallH v f) -> SysPrf T f.
Proof. apply (forallSimp LNN). Qed.

Lemma existI (T : System) (f : Formula) (v : nat) (t : Term):
 SysPrf T (substituteFormula LNN f v t) -> SysPrf T (existH v f).
Proof. apply (existI LNN). Qed.

Lemma existE (T : System) (f g : Formula) (v : nat):
  ~ In_freeVarSys LNN v T ->
  ~ In v (freeVarFormula LNN g) ->
  SysPrf T (existH v f) -> SysPrf T (impH f g) -> 
  SysPrf T g.
Proof. apply (existE LNN). Qed.

Lemma existSimp (T : System) (f : Formula) (v : nat):
  SysPrf T f -> SysPrf T (existH v f).
Proof. apply (existSimp LNN). Qed.

Lemma existSys (T : System) (f g : Formula) (v : nat):
  ~ In_freeVarSys LNN v T ->
  ~ In v (freeVarFormula LNN g) ->
  SysPrf (Ensembles.Add _ T f) g -> 
  SysPrf (Ensembles.Add _ T (existH v f)) g.
Proof. apply (existSys LNN). Qed.

Lemma absurd1  (T : System) (f : Formula):
 SysPrf T (impH f (notH f)) -> SysPrf T (notH f).
Proof. apply (absurd1 LNN). Qed.

Lemma nImp (T : System) (f g : Formula):
 SysPrf T (andH f (notH g)) -> SysPrf T (notH (impH f g)).
Proof. apply (nImp LNN). Qed.

Lemma nOr (T : System) (f g : Formula):
 SysPrf T (andH (notH f) (notH g)) -> SysPrf T (notH (orH f g)).
Proof. apply (nOr LNN). Qed.

Lemma nAnd (T : System) (f g : Formula):
 SysPrf T (orH (notH f) (notH g)) -> SysPrf T (notH (andH f g)).
Proof. apply (nAnd LNN). Qed.

Lemma nForall (T : System) (f : Formula) (v : nat):
 SysPrf T (existH v (notH f)) -> SysPrf T (notH (forallH v f)).
Proof. apply (nForall LNN). Qed.

Lemma nExist (T : System) (f : Formula) (v : nat):
 SysPrf T (forallH v (notH f)) -> SysPrf T (notH (existH v f)).
Proof. apply (nExist LNN). Qed.

Lemma impRefl (T : System) (f : Formula):  SysPrf T (impH f f).
Proof. apply (impRefl LNN). Qed.

Lemma impTrans (T : System) (f g h : Formula):
 SysPrf T (impH f g) -> SysPrf T (impH g h) -> SysPrf T (impH f h).
Proof. apply (impTrans LNN). Qed.

Lemma orSym (T : System) (f g : Formula):
 SysPrf T (orH f g) -> SysPrf T (orH g f).
Proof. apply (orSym LNN). Qed.

Lemma andSym (T : System) (f g : Formula):
 SysPrf T (andH f g) -> SysPrf T (andH g f).
Proof. apply (andSym LNN). Qed.

Lemma iffRefl (T : System) (f : Formula):  SysPrf T (iffH f f).
Proof. apply (iffRefl LNN). Qed.

Lemma iffSym  (T : System) (f g : Formula):
 SysPrf T (iffH f g) -> SysPrf T (iffH g f).
Proof. apply (iffSym LNN). Qed.

Lemma iffTrans (T : System) (f g h : Formula):
 SysPrf T (iffH f g) -> SysPrf T (iffH g h) -> SysPrf T (iffH f h).
Proof. apply (iffTrans LNN). Qed.

Lemma eqRefl (T : System) (a : Term): SysPrf T (equal a a).
Proof. apply (eqRefl LNN). Qed.

Lemma eqSym (T : System) (a b : Term):
 SysPrf T (equal a b) -> SysPrf T (equal b a).
Proof. apply (eqSym LNN). Qed.

Lemma eqTrans (T : System) (a b c : Term):
 SysPrf T (equal a b) -> SysPrf T (equal b c) -> SysPrf T (equal a c).
Proof. apply (eqTrans LNN). Qed.

(* TODO explicit inversion intro patterns *)
Lemma eqPlus (T : System) (a b c d : Term):
 SysPrf T (equal a b) ->
 SysPrf T (equal c d) -> SysPrf T (equal (Plus a c) (Plus b d)).
Proof.
  intros H H0; unfold Plus; apply (equalFunction); simpl.  
  destruct (consTerms LNN 1 (Tcons _ 1 a (Tcons _ 0 c (Tnil _))))
    as [(a0, b0) p]. 
  simpl; 
    destruct  (consTerms LNN 1 (Tcons _ 1 b (Tcons _ 0 d (Tnil _))))
    as [(a1, b1) p0].
  simpl; destruct  (consTerms LNN 0 b0) as [(a2, b2) p1].
  simpl; destruct  (consTerms LNN 0 b1) as [(a3,b3) p2].
  simpl; repeat split.
  - simpl in p; inversion p.
    simpl in p0; inversion p0.
    apply H.
  - simpl in p; inversion p.
    rewrite <- p1 in H3.
    simpl in H3; inversion H3.
    simpl in p0; inversion p0.
    rewrite <- p2 in H7.
    inversion H7.
    apply H0.
Qed.

Lemma eqTimes (T : System) (a b c d : Term):
  SysPrf T (equal a b) ->
  SysPrf T (equal c d) -> SysPrf T (equal (Times a c) (Times b d)).
Proof.
  intros H H0; unfold Times; apply (equalFunction LNN).
  simpl; 
    destruct (consTerms LNN 1 (Tcons _ 1 a (Tcons _ 0 c (Tnil _))))
    as [(a0, b0) p].
  simpl; destruct (consTerms LNN 1 (Tcons _ 1 b (Tcons _ 0 d (Tnil _))))
    as [(a1, b1) p0].
  simpl; destruct  (consTerms LNN 0 b0) as [(a2, b2) p1].
  simpl; induction (consTerms LNN 0 b1) as [(a3,b3) p2].
  repeat split.
  - simpl in p.
    inversion p.
    simpl in p0.
    inversion p0.
    apply H.
  - simpl in p.
    inversion p.
    rewrite <- p1 in H3.
    simpl in H3.
    inversion H3.
    simpl in p0.
    inversion p0.
    rewrite <- p2 in H7.
    inversion H7.
    apply H0.
Qed.

Lemma eqSucc (T : System) (a b : Term):
  SysPrf T (equal a b) -> SysPrf T (equal (Succ a) (Succ b)).
Proof.
  intro H; unfold Succ; apply (equalFunction LNN).
  simpl; destruct (consTerms LNN 0 (Tcons _ 0 a (Tnil _)))
    as [(a0, b0) p].
  simpl; destruct  (consTerms LNN 0 (Tcons LNN 0 b (Tnil LNN)))
    as [(a1, b1) p0].
  simpl; repeat split.
  simpl in p.
  inversion p.
  simpl in p0.
  inversion p0.
  apply H.
Qed.

Lemma eqLT (T : System) (a b c d : Term):
  SysPrf T (equal a b) ->
  SysPrf T (equal c d) -> SysPrf T (iffH (LT a c) (LT b d)).
Proof.
  intros H H0; unfold LT; apply (equalRelation LNN).
  simpl;  destruct  (consTerms LNN 1 (Tcons _ 1 a (Tcons _ 0 c (Tnil _))))
    as [(a0, b0) p].
  simpl; destruct (consTerms LNN 1 (Tcons _ 1 b (Tcons _ 0 d (Tnil _))))
    as [(a1, b1) p0].
  simpl; destruct (consTerms LNN 0 b0) as [(a2, b2) p1]. 

  destruct  (consTerms LNN 0 b1) as [(a3, b3) p2]. 
  simpl;repeat split.
  - simpl in p.
    inversion p.
    simpl in p0.
    inversion p0.
    apply H.
  - simpl in p.
    inversion p.
    rewrite <- p1 in H3.
    simpl in H3.
    inversion H3.
    simpl in p0.
    inversion p0.
    rewrite <- p2 in H7.
    inversion H7.
    apply H0.
Qed.

End Logic.

Fixpoint natToTerm (n : nat) : Term :=
  match n with
  | O => Zero
  | S m => Succ (natToTerm m)
  end.

Lemma closedNatToTerm :
 forall a v : nat, ~ In v (freeVarTerm LNN (natToTerm a)).
Proof.
intros a v; induction a as [| a Hreca].
 - simpl; auto. 
  - simpl; now rewrite freeVarSucc.
Qed.

(**  LNT.v : Language of Number Theory 

Original version by Russel O'Connor

*)


From Coq Require Import Arith Ensembles List.

Require Import Languages  folProof  folProp  folLogic3.

(** * Instantiations of a few generic constructs 

  _To do_ perhaps these redefinitions should be deprecated, because they cause some issues 
  in statements which mix [LNN] and [LNT] terms and formulas 
*)



Definition Formula := Formula LNT.
Definition Formulas := Formulas LNT.
Definition System := System LNT.
Definition Sentence := Sentence LNT.
Definition Term := Term LNT.
Definition Terms := Terms LNT.
Definition SysPrf := SysPrf LNT.
#[local] Arguments apply _ _ _ : clear implicits.


Definition Plus (x y : Term) : Term :=
  apply LNT Plus_ (Tcons x (Tcons y (Tnil))).


Definition Times (x y : Term) : Term :=
  apply LNT Times_ (Tcons x (Tcons y (Tnil))).

Definition Succ (x : Term) : Term :=
  apply LNT Succ_ (Tcons x (Tnil)).

Definition Zero : Term := apply LNT Zero_ (Tnil).


(** * Notations for LNT formulas: experimental and unstable *)

Declare Scope nt_scope.
Delimit Scope nt_scope with nt. 


Infix "=" := (equal _): nt_scope.
Infix "\/" := (orH): nt_scope.
Infix "/\" := (andH):nt_scope.
Infix "->" := (impH): nt_scope.
Notation "~ A" := (@notH _ A): nt_scope. 
Notation "A <-> B" := (@iffH _ A B): nt_scope.


Notation k_ t := (apply  (t:Functions _)  (Tnil)).

Notation app1 f arg := 
  (apply  (f: Functions _)  (Tcons arg (Tnil))).
About Tnil.
Notation app2 f arg1 arg2 := 
  (apply   (f: Functions _) 
     (Tcons  arg1 (Tcons  arg2 (Tnil)))).

Notation "t = u" := (@equal _ t u): nt_scope.
Notation "t <> u" := (~ t = u)%nt : nt_scope.
Notation "'v_' i" := (var i) (at level 3) : nt_scope.



Notation "'exH' x .. y , p" := (existH  x .. (existH y p) ..)
  (x at level 0, y at level 0, at level 200, right associativity) : nt_scope. 

Notation "'allH' x .. y , p" := (forallH  x .. (forallH y p) ..)
  (x at level 0, y at level 0, at level 200, right associativity) : nt_scope. 


Infix "+" := Plus :nt_scope.
Infix "*" := Times :nt_scope.


(** ** Notations for printing computed formulas/terms with derived connectives *)



Reserved Notation "x '\/'' y" (at level 85, right associativity).
Reserved Notation "x '/\'' y" (at level 80, right associativity).
Reserved Notation "x '<->'' y" (at level 95, no associativity).
Reserved Notation "x '<->''' y" (at level 95, no associativity).

Notation "x \/' y" := (~ x -> y)%nt : nt_scope. 
Notation "x /\' y" := (~ (~ x \/'  ~ y))%nt : nt_scope.
Notation "x <->'' y" := ((x -> y) /\ (y -> x))%nt:  nt_scope.
Notation "x <->' y" := (~ (~ (x -> y) \/' ~(y -> x)))%nt : nt_scope.
Notation exH' v A := (~ (forallH v (~ A)))%nt.


(** ** Examples *)

Section Examples.
Variable f : Formula. 
Check (allH 0 1 ,  (f -> v_ 0 = v_ 0 -> v_ 1 = v_ 1))%nt.

Check (exH 0 1 ,  (v_ 0 = v_ 0 -> v_ 1 = v_ 1))%nt.
End Examples.

(** * Basic properties 
*)

Lemma LNT_eqdec : language_decidable LNT.
Proof. split; decide equality. Qed.

(** ** List of free variables of a formula *)

Section Free_Variables.

Lemma freeVarPlus (x y: Term) :
 freeVarTerm LNT (Plus x y) = freeVarTerm LNT x ++ freeVarTerm LNT y.
Proof.
  now rewrite (app_nil_end (freeVarTerm LNT y)).
Qed.

Lemma freeVarTimes (x y : Term) :
 freeVarTerm LNT (Times x y) = freeVarTerm LNT x ++ freeVarTerm LNT y.
Proof.
  now rewrite (app_nil_end (freeVarTerm LNT y)).
Qed.

Lemma freeVarSucc (x : Term):
  freeVarTerm LNT (Succ x) = freeVarTerm LNT x.
Proof.
  now rewrite (app_nil_end (freeVarTerm LNT x)).
Qed.

Lemma freeVarZero : freeVarTerm LNT Zero = nil.
Proof. reflexivity. Qed.

End Free_Variables.

(** ** Basic and derived proof rules *)

Section Logic.

Lemma Axm  (T : System) (f : Formula) :  mem _ T f -> SysPrf T f.
Proof. apply (Axm LNT). Qed.

Lemma sysExtend (T U : System) (f : Formula):
  Included _ T U -> SysPrf T f -> SysPrf U f.
Proof. apply (sysExtend LNT). Qed.

Lemma sysWeaken (T : System) (f g : Formula):
  SysPrf T f -> SysPrf (Ensembles.Add _ T g) f.
Proof. apply (sysWeaken LNT). Qed.

Lemma impI (T : System) (f g : Formula):
  SysPrf (Ensembles.Add _ T g) f -> SysPrf T (g -> f)%nt.
Proof. apply (impI LNT). Qed.

Lemma impE (T : System) (f g : Formula):
 SysPrf T (g -> f)%nt -> SysPrf T g -> SysPrf T f.
Proof. apply (impE LNT). Qed.

Lemma contradiction (T : System) (f g : Formula):
 SysPrf T f -> SysPrf T (~ f)%nt -> SysPrf T g.
Proof. apply (contradiction LNT). Qed.

Lemma nnE (T : System) (f : Formula):
  SysPrf T (~ ~ f)%nt -> SysPrf T f.
Proof. apply (nnE LNT). Qed.

Lemma noMiddle (T : System) (f : Formula): SysPrf T (~ f \/ f)%nt.
Proof. apply (noMiddle LNT). Qed.

Lemma nnI (T : System) (f : Formula):
  SysPrf T f -> SysPrf T (~ ~ f)%nt.
Proof. apply (nnI LNT). Qed.

Lemma cp1 (T : System) (f g : Formula):
 SysPrf T (~ f -> ~ g)%nt -> SysPrf T (g -> f)%nt.
Proof. apply (cp1 LNT). Qed.

Lemma cp2 (T : System) (f g : Formula):
 SysPrf T (g -> f)%nt -> SysPrf T (~ f -> ~ g)%nt.
Proof. apply (cp2 LNT). Qed.

Lemma orI1 (T : System) (f g : Formula): 
  SysPrf T f -> SysPrf T (f \/ g)%nt.
Proof. apply (orI1 LNT). Qed.

Lemma orI2 (T : System) (f g : Formula):
  SysPrf T g -> SysPrf T (f \/ g)%nt.
Proof. apply (orI2 LNT). Qed.

Lemma orE (T : System) (f g h : Formula):
  SysPrf T (f \/ g)%nt -> 
  SysPrf T (f -> h)%nt -> SysPrf T (g -> h)%nt -> 
  SysPrf T h.
Proof. apply (orE LNT). Qed.

Lemma orSys (T : System) (f g h : Formula):
 SysPrf (Ensembles.Add _ T f) h -> 
 SysPrf (Ensembles.Add _ T g) h -> 
 SysPrf (Ensembles.Add _ T (f \/ g)%nt) h.
Proof. apply (orSys LNT). Qed.

Lemma andI (T : System) (f g : Formula) :
 SysPrf T f -> SysPrf T g -> SysPrf T (f /\ g)%nt.
Proof. apply (andI LNT). Qed.

Lemma andE1 (T : System) (f g : Formula) :
  SysPrf T (f /\ g)%nt -> SysPrf T f.
Proof. apply (andE1 LNT). Qed.

Lemma andE2 (T : System) (f g : Formula) :
  SysPrf T (f /\ g)%nt -> SysPrf T g.
Proof. apply (andE2 LNT). Qed.

Lemma iffI (T : System) (f g : Formula) :
 SysPrf T (f -> g)%nt -> SysPrf T (g -> f)%nt -> SysPrf T (f <-> g)%nt.
Proof. apply (iffI LNT). Qed.

Lemma iffE1 (T : System) (f g : Formula):
 SysPrf T (f <-> g)%nt -> SysPrf T (f -> g)%nt.
Proof. apply (iffE1 LNT). Qed.

Lemma iffE2 (T : System) (f g : Formula) :
 SysPrf T (f <-> g)%nt -> SysPrf T (g -> f)%nt.
Proof. apply (iffE2 LNT). Qed.

Lemma forallI (T : System) (f : Formula) (v : nat):
 ~ In_freeVarSys LNT v T -> SysPrf T f -> SysPrf T (forallH v f).
Proof. apply (forallI LNT). Qed.

Lemma forallE (T : System) (f : Formula) (v : nat) (t : Term) :
 SysPrf T (forallH v f) -> SysPrf T (substituteFormula LNT f v t).
Proof. apply (forallE LNT). Qed.

Lemma forallSimp (T : System) (f : Formula) (v : nat):
 SysPrf T (forallH v f) -> SysPrf T f.
Proof. apply (forallSimp LNT). Qed.

Lemma existI (T : System) (f : Formula) (v : nat) (t : Term):
 SysPrf T (substituteFormula LNT f v t) -> SysPrf T (existH v f).
Proof. apply (existI LNT). Qed.

Lemma existE (T : System) (f g : Formula) (v : nat):
  ~ In_freeVarSys LNT v T ->
  ~ In v (freeVarFormula LNT g) ->
  SysPrf T (existH v f) -> SysPrf T (impH f g) -> SysPrf T g.
Proof. apply (existE LNT). Qed.

Lemma existSimp (T : System) (f : Formula) (v : nat):
 SysPrf T f -> SysPrf T (existH v f).
Proof. apply (existSimp LNT). Qed.

Lemma existSys (T : System) (f g : Formula) (v : nat):
  ~ In_freeVarSys LNT v T ->
  ~ In v (freeVarFormula LNT g) ->
  SysPrf (Ensembles.Add _ T f) g -> 
  SysPrf (Ensembles.Add _ T (existH v f)) g.
Proof. apply (existSys LNT). Qed.

Lemma absurd1 (T : System) (f : Formula):
 SysPrf T (impH f (notH f)) -> SysPrf T (notH f).
Proof. apply (absurd1 LNT). Qed.

Lemma nImp (T : System) (f g : Formula):
 SysPrf T (andH f (notH g)) -> SysPrf T (notH (impH f g)).
Proof. apply (nImp LNT). Qed.

Lemma nOr (T : System) (f g : Formula):
 SysPrf T (andH (notH f) (notH g)) -> SysPrf T (notH (orH f g)).
Proof. apply (nOr LNT). Qed.

Lemma nAnd (T : System) (f g : Formula):
 SysPrf T (orH (notH f) (notH g)) -> SysPrf T (notH (andH f g)).
Proof. apply (nAnd LNT). Qed. 

Lemma nForall (T : System) (f : Formula) (v : nat) :
 SysPrf T (existH v (notH f)) -> SysPrf T (notH (forallH v f)).
Proof. apply (nForall LNT). Qed.

Lemma nExist (T : System) (f : Formula) (v : nat):
 SysPrf T (forallH v (notH f)) -> SysPrf T (notH (existH v f)).
Proof. apply (nExist LNT). Qed.

Lemma impRefl (T : System) (f : Formula): SysPrf T (impH f f).
Proof. apply (impRefl LNT). Qed.

Lemma impTrans (T : System) (f g h : Formula):
 SysPrf T (impH f g) -> SysPrf T (impH g h) -> SysPrf T (impH f h).
Proof. apply (impTrans LNT). Qed.

Lemma orSym (T : System) (f g : Formula):
 SysPrf T (orH f g) -> SysPrf T (orH g f).
Proof. apply (orSym LNT). Qed.

Lemma andSym (T : System) (f g : Formula) :
 SysPrf T (andH f g) -> SysPrf T (andH g f).
Proof. apply (andSym LNT). Qed.

Lemma iffRefl (T : System) (f : Formula) : SysPrf T (iffH f f).
Proof. apply (iffRefl LNT). Qed.

Lemma iffSym (T : System) (f g : Formula):
 SysPrf T (iffH f g) -> SysPrf T (iffH g f).
Proof. apply (iffSym LNT). Qed.

Lemma iffTrans (T : System) (f g h : Formula):
 SysPrf T (iffH f g) -> SysPrf T (iffH g h) -> SysPrf T (iffH f h).
Proof. apply (iffTrans LNT). Qed.

Lemma eqRefl  (T : System) (a : Term): SysPrf T (equal a a).
Proof. apply (eqRefl LNT). Qed.

Lemma eqSym (T : System) (a b : Term):
 SysPrf T (equal a b) -> SysPrf T (equal b a).
Proof. apply (eqSym LNT). Qed.

Lemma eqTrans (T : System) (a b c : Term):
 SysPrf T (equal a b) -> SysPrf T (equal b c) -> SysPrf T (equal a c).
Proof. apply (eqTrans LNT). Qed.

Lemma eqPlus (T : System) (a b c d : Term):
  SysPrf T (equal a b) ->
  SysPrf T (equal c d) -> SysPrf T (equal (Plus a c) (Plus b d)).
Proof.
  intros H H0; unfold Plus.
  apply (equalFunction LNT).
  simpl in |- *.
  destruct (consTerms LNT 1 (Tcons a (Tcons c (Tnil))))as [(a0,b0) p].
  simpl; destruct (consTerms LNT 1 (Tcons b (Tcons d (Tnil)))) 
    as [(a1,b1) p0]. 
  simpl in |- *.
  destruct (consTerms LNT 0 b0) as [(a2,b2) p1]. 
  simpl in |- *.
  destruct (consTerms LNT 0 b1) as [(a3,b3) p2]. 
  simpl in |- *; repeat split.
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

Lemma eqTimes  (T : System) (a b c d : Term):
 SysPrf T (a = b)%nt ->
 SysPrf T (c = d)%nt -> SysPrf T (a * c = b * d)%nt.
Proof.
  intros H H0; unfold Times in |- *.
  apply (equalFunction LNT); simpl in |- *.
  destruct (consTerms LNT 1 (Tcons a (Tcons c (Tnil))))as [(a0,b0) p].
  simpl;
  destruct (consTerms LNT 1 (Tcons b (Tcons d (Tnil)))) as [(a1,b1) p0].
  simpl; destruct (consTerms LNT 0 b0) as [(a2,b2) p1].
  simpl ; destruct (consTerms LNT 0 b1) as [(a3,b3) p2].
  simpl in |- *; repeat split.
  - simpl in p; inversion p /r; intros ? ?.
    simpl in p0; inversion p0 /r; intros ? ?; apply H.
  - simpl in p; inversion p /r ; intros H2 H3; rewrite <- p1 in H3.
    simpl in H3; inversion H3 /r; intros H4 H5.
    simpl in p0; inversion p0 /r. intros H6 H7; rewrite <- p2 in H7; 
    inversion H7; apply H0.
Qed.

Lemma eqSucc (T : System) (a b : Term):
 SysPrf T (a = b)%nt -> SysPrf T (Succ a = Succ b)%nt.
Proof.
  intros H; unfold Succ in |- *; apply (equalFunction LNT).
  simpl in |- *.
  destruct (consTerms LNT 0 (Tcons a (Tnil))) as [(a0,b0) p].
  simpl in |- *;
    destruct (consTerms LNT 0 (Tcons b (Tnil))) as [(a1,b1) p0].
  simpl in |- *; repeat split.
  - simpl in p; inversion p /r; intros ? ?.
    simpl in p0; inversion p0; apply H.
Qed.

End Logic.

Fixpoint natToTerm (n : nat) : Term :=
  match n with
  | O => Zero
  | S m => Succ (natToTerm m)
  end.

Lemma closedNatToTerm :
 forall a v : nat, ~ In v (freeVarTerm LNT (natToTerm a)).
Proof.
  intros a v; induction a as [| a Hreca].
  - cbn; auto. 
  - simpl; now rewrite freeVarSucc.
Qed.






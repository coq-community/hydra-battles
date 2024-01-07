(** LNN2LNT: 

   Translation of [LNN]-formulas and proofs into [LNT] by replacement of 
    [(t < t')%fol] subformulas with [(exists v, t + Succ v = t')%nt].

   Original file by Russel O'Connor

*)

(* begin hide *)
From Coq Require Import Ensembles List Arith.

From hydras.Ackermann 
 Require Import misc ListExt folProp folProof Languages  subAll  
 subProp  folLogic3  folReplace LNN LNT  codeNatToTerm  NewNotations.

Import FolNotations  NNnotations.

#[local] Arguments apply _ _ _ : clear implicits.
(* end hide *)


(** * Translation of terms *)

Fixpoint LNN2LNT_term (t : fol.Term LNN) : fol.Term LNT:=
  match t with
  | var v => var v
  | apply f ts => apply LNT f (LNN2LNT_terms _ ts)
  end
 
 with LNN2LNT_terms (n : nat) (ts : fol.Terms LNN n) {struct ts} : 
 Terms n :=
  match ts in (fol.Terms _ n0) return (Terms n0) with
  | Tnil => @Tnil LNT
  | Tcons m s ss => Tcons (LNN2LNT_term s) (LNN2LNT_terms m ss)
  end. 

(* begin hide *)
Lemma LNN2LNT_natToTerm (n:nat): LNN2LNT_term (natToTermLNN n) = natToTerm n.
Proof.
  induction n as [| n Hrecn].
  - reflexivity.
  - simpl; now rewrite Hrecn.
Qed.

Lemma LNN2LNT_freeVarT (t : fol.Term LNN):
 freeVarT  (LNN2LNT_term t) = freeVarT t.
Proof.
  induction t using
    Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms LNN n) =>
             freeVarTs (LNN2LNT_terms n ts) = freeVarTs ts).
  - intros; reflexivity.
  - intros; simpl; repeat rewrite freeVarTApply; now apply IHt.
  - intros; simpl; reflexivity. 
  - transitivity (freeVarT t ++ freeVarTs t0).
    + rewrite <- IHt0; rewrite <- IHt; reflexivity.
    + reflexivity.
Qed.

Lemma LNN2LNT_freeVarTs (n : nat) (ts : fol.Terms LNN n):
    freeVarTs (LNN2LNT_terms n ts) = freeVarTs ts.
Proof.
  induction ts as [| n t ts Hrects].
  - reflexivity.
  - simpl; transitivity (freeVarT t ++ freeVarTs ts).
    + rewrite <- Hrects; rewrite <- LNN2LNT_freeVarT; reflexivity.
    + reflexivity.
Qed.

Lemma LNN2LNT_subTerm (t : fol.Term LNN) (v : nat) (s : fol.Term LNN):
 LNN2LNT_term (substT t v s) =
 substT (LNN2LNT_term t) v (LNN2LNT_term s).
Proof.
  elim t using  Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms LNN n) =>
             LNN2LNT_terms n (substTs ts v s) =
               substTs (LNN2LNT_terms n ts) v 
                 (LNN2LNT_term s)).
  - intros n; simpl; destruct (eq_nat_dec v n); auto.
  - simpl in |- *; intros f t0 H; now rewrite H.
  - reflexivity.
  - intros n t0 H t1 H0; simpl; now rewrite H, H0. 
Qed.

Lemma LNN2LNT_subTerms 
  (n : nat) (ts : fol.Terms LNN n) (v : nat) (s : fol.Term LNN):
  LNN2LNT_terms n (substTs ts v s) =
    substTs (LNN2LNT_terms n ts) v (LNN2LNT_term s).
Proof.
  induction ts as [| n t ts Hrects].
  - reflexivity.
  - simpl; now rewrite Hrects,  LNN2LNT_subTerm.
Qed.

(* end hide *)

(** ** Inverse translation *)

Fixpoint LNT2LNN_term (t : Term) : fol.Term LNN :=
  match t with
  | var v => var v
  | apply f ts => apply LNN f (LNT2LNN_terms _ ts)
  end
 
 with LNT2LNN_terms (n : nat) (ts : Terms n) {struct ts} : 
 fol.Terms LNN n :=
  match ts in (fol.Terms _ n0) return (fol.Terms LNN n0) with
  | Tnil => @Tnil LNN
  | Tcons m s ss => Tcons (LNT2LNN_term s) (LNT2LNN_terms m ss)
  end.

Lemma LNT2LNN_natToTerm (n:  nat) :
  LNT2LNN_term (natToTerm n) = natToTermLNN n.
Proof.
  induction n as [| n Hrecn].
  - reflexivity.
  - simpl; now rewrite Hrecn.
Qed.

Lemma LNT2LNT_term (t : Term): LNN2LNT_term (LNT2LNN_term t) = t.
Proof.
  elim t using
    Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms LNT n) =>
             LNN2LNT_terms n (LNT2LNN_terms n ts) = ts); 
    simpl in |- *.
  - reflexivity.
  - intros f t0 H.  unfold LNNArityF. now rewrite H.
  - reflexivity.
  - intros n t0 H t1 H0. now rewrite H, H0.
Qed.

(** * Translation of formulas *)

(** ** Translation of [(v#0 < v#1)%fol] *)

Definition LTFormula := (exH 2, v#0 + LNT.Succ v#2 = v#1)%nt.

(** ** Translation of [(t < t')%fol] *)

(**  The function [translateLT] is defined by an interactive proof (omitted).
     It is specified by the lemma [translateLT1] 
*)

Definition translateLT (ts : fol.Terms LNN (arityR LNN LT_)) : Formula.
Proof.
  simpl in ts; destruct  (consTerms _ _ ts) as [(a,b) p].
  destruct  (consTerms _ _ b) as [(a0,b0) p0].
  set (x := LNN2LNT_term a) in *.
  set (y := LNN2LNT_term a0) in *.
  apply (subAllFormula LNT LTFormula).
  intro n; induction n as [| n Hrecn].
  - exact x.
  - induction n  as [| n0 HrecH0].
    + exact y.
    + exact (var n0).
Defined.

Lemma translateLT1 :
 forall a a0 b0,
 translateLT (Tcons a (Tcons a0 b0)) =
 subAllFormula LNT LTFormula
   (fun H : nat =>
    nat_rec (fun _ : nat => fol.Term LNT) (LNN2LNT_term a)
      (fun (H0 : nat) (_ : fol.Term LNT) =>
       nat_rec (fun _ : nat => fol.Term LNT) (LNN2LNT_term a0)
         (fun (H1 : nat) (_ : fol.Term LNT) => var H1) H0) H).
Proof.
  intros a a0 b0; unfold translateLT.  
  destruct (consTerms LNN 1 (Tcons a (Tcons a0 b0))) as [(a1, b) p].
  simpl; destruct (consTerms LNN 0 b) as [(a2, b1) p0].
  simpl in p; inversion p.
  assert (b = Tcons a0 b0)
    by refine (inj_pair2_eq_dec  _ eq_nat_dec _ _ _ _ H1).
  rewrite H in p0; simpl in p0; inversion p0; reflexivity.
Qed.

(** ** Translation of any [LNN]-formula 

   The translation of any [LNN]-formula is straigthforward, except for 
   the special case of [t_1 < t_2] (handled by [translateLT] )

*)

Fixpoint LNN2LNT_formula (f : fol.Formula LNN) : Formula :=
  match f with
  | (t1 = t2)%fol => (LNN2LNT_term t1 = LNN2LNT_term t2)%nt
  | atomic r ts =>
      match
        r as l return (fol.Terms LNN (arityR LNN l) -> Formula)
      with
      | LT_ => fun ts : fol.Terms LNN (arityR LNN LT_) => translateLT ts
      end ts
  | (A -> B)%fol => (LNN2LNT_formula A -> LNN2LNT_formula B)%nt
  | (~ A)%fol =>  (~ LNN2LNT_formula A)%nt
  | (allH v, A)%fol => (allH v, LNN2LNT_formula A)%nt
  end.

(** *** Helpful rewriting lemmas *)

Lemma LNN2LNT_or (a b : fol.Formula LNN):
  LNN2LNT_formula (orH a b) =
    orH (LNN2LNT_formula a) (LNN2LNT_formula b).
Proof. reflexivity. Qed.

Lemma LNN2LNT_and (a b : fol.Formula LNN):
 LNN2LNT_formula (andH a b) =
 andH (LNN2LNT_formula a) (LNN2LNT_formula b).
Proof. reflexivity. Qed.

Lemma LNN2LNT_iff (a b : fol.Formula LNN):
 LNN2LNT_formula (iffH a b) =
   iffH (LNN2LNT_formula a) (LNN2LNT_formula b).
Proof. reflexivity. Qed.

Lemma LNN2LNT_exist (v : nat) (a : fol.Formula LNN) :
 LNN2LNT_formula (existH  v a) = existH v (LNN2LNT_formula a).
Proof. reflexivity. Qed.


Lemma LNN2LNT_freeVarF (f : fol.Formula LNN) (v : nat):
  In v (freeVarF (LNN2LNT_formula f)) <-> In v (freeVarF f).
Proof.
  induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf].
  - simpl; repeat rewrite LNN2LNT_freeVarT; tauto.
  - destruct r. (* is LT *)
    simpl. 
    destruct (consTerms _ _ t) as [(a,b) p].
    simpl in p; rewrite <- p.
    destruct (consTerms _ _ b) as [(a0, b0) p0].
    simpl in p0; rewrite <- p0.
    rewrite translateLT1.
    rewrite <- (nilTerms _ b0).
    unfold freeVarTs in |- *.
    fold (@freeVarT LNN) in |- *.
    rewrite app_nil_r.
    split.
    + intros H; decompose record (freeVarSubAllFormula1 _ _ _ _ H) /r.
      intros H x [H0| H0] H2.
      * rewrite <- H0 in H2.
        simpl in H2.
        rewrite LNN2LNT_freeVarT in H2; auto with datatypes.
      * destruct H0 as [H0| H0].
        -- rewrite <- H0 in H2.
           simpl in H2.
           rewrite LNN2LNT_freeVarT in H2.
           auto with datatypes.
        -- contradiction.
    + intro H; destruct (in_app_or _ _ _ H) as [H0 | H0].
      * eapply freeVarSubAllFormula2.
        simpl in |- *.
        left.
        reflexivity.
        simpl in |- *.
        rewrite LNN2LNT_freeVarT.
        auto.
      * eapply freeVarSubAllFormula2.
        simpl in |- *.
        right.
        left.
        reflexivity.
        simpl in |- *.
        rewrite LNN2LNT_freeVarT.
        auto.
  - simpl in |- *.
    induction Hrecf1 as (H, H0).
    induction Hrecf0 as (H1, H2).
    split.
    + intros H3; apply in_or_app.
      destruct (in_app_or _ _ _ H3); tauto.
    + intros H3; apply in_or_app.
      destruct (in_app_or _ _ _ H3); tauto.
  - assumption.
  - simpl in |- *.
    induction Hrecf as (H, H0).
    split.
    + intros H1; apply in_in_remove.
      * eapply in_remove_neq; apply H1.
      * apply H; eapply List.in_remove; apply H1.
    + intros H1; apply in_in_remove.
      * eapply in_remove_neq, H1.
      * apply H0.
        eapply in_remove, H1.
Qed.

Lemma LNN2LNT_freeVarF1 (f : fol.Formula LNN) (v : nat):
 In v (freeVarF (LNN2LNT_formula f)) -> 
 In v (freeVarF f).
Proof.
  intros ?; destruct (LNN2LNT_freeVarF f v); auto.
Qed.

Lemma LNN2LNT_freeVarF2 (f : fol.Formula LNN) (v : nat):
  In v (freeVarF f) -> 
  In v (freeVarF (LNN2LNT_formula f)).
Proof.
intros ? ; destruct (LNN2LNT_freeVarF f v); auto.
Qed.


Lemma LNN2LNT_subFormula 
 (T : System) (f : fol.Formula LNN) (v : nat) (s : fol.Term LNN):
 SysPrf T
   (iffH (LNN2LNT_formula (substF f v s))
      (substF (LNN2LNT_formula f) v (LNN2LNT_term s))).
Proof.
  apply sysExtend with (Empty_set Formula).
  -  intros x H; destruct H.
  - generalize f v s; clear T f v s; intro f.
    elim f using Formula_depth_ind2; intros.
    + simpl; rewrite (subFormulaEqual LNT).
      repeat rewrite LNN2LNT_subTerm; apply iffRefl.
    + induction r.
      rewrite subFormulaRelation; simpl.
      destruct (consTerms _ _ t) as [(a,b) p].
      simpl in p; rewrite <- p.
      destruct (consTerms _ _ b) as [(a0,b0) p0].
      simpl in p0; rewrite <- p0.
      rewrite translateLT1.
      apply iffSym; eapply iffTrans.
      * apply (subSubAllFormula LNT).
      * rewrite <- (nilTerms _ b0).
        replace
          (substTs (Tcons a (Tcons a0 (Tnil))) v s) 
          with
          (Tcons (substT a v s)
             (Tcons (substT a0 v s) (Tnil))).
        rewrite translateLT1.
        rewrite
          (subAllFormula_ext LNT LTFormula
             (fun H : nat =>
                nat_rec (fun _ : nat => fol.Term LNT)
                  (LNN2LNT_term (substT a v s))
                  (fun (H0 : nat) (_ : fol.Term LNT) =>
                     nat_rec (fun _ : nat => fol.Term LNT)
                       (LNN2LNT_term (substT a0 v s))
                       (fun (H1 : nat) (_ : fol.Term LNT) => var H1) H0) H)
             (fun n : nat =>
                substT 
                  (nat_rec (fun _ : nat => fol.Term LNT) (LNN2LNT_term a)
                     (fun (H0 : nat) (_ : fol.Term LNT) =>
                        nat_rec (fun _ : nat => fol.Term LNT) (LNN2LNT_term a0)
                          (fun (H1 : nat) (_ : fol.Term LNT) => var H1) H0) n) v
                  (LNN2LNT_term s))).
        -- apply iffRefl.
        -- intros m H; destruct m as [| n].
           ++ simpl; apply LNN2LNT_subTerm.
           ++ destruct n as [| n].
              ** simpl in |- *.
                 apply LNN2LNT_subTerm.
              ** simpl in H.
                 decompose sum H.
                 discriminate H0.
                 discriminate H1.
        -- reflexivity.
    + rewrite subFormulaImp; simpl.
      rewrite (subFormulaImp LNT).
      apply (reduceImp LNT).
      apply H.
      apply H0.
    + rewrite subFormulaNot.
      simpl; rewrite (subFormulaNot LNT).
      apply (reduceNot LNT).
      apply H.
    + simpl; decompose record (subFormulaForall2 LNN a v v0 s) /r.
      intros x H1 H0 H2 H4; rewrite H4; clear H4.
      decompose record
        (subFormulaForall2 LNT (LNN2LNT_formula a) v v0 (LNN2LNT_term s)) /r. 
      intros x0 H4 H3 H5 H7; rewrite H7; clear H7.
      destruct (eq_nat_dec v v0) as [e | ].
      * simpl; apply iffRefl.
      * simpl; apply iffTrans with
          (forallH x0
             (substF 
                (LNN2LNT_formula
                   (substF 
                      (substF a v (var x)) v0 s)) x 
                (var x0))).
        apply (rebindForall LNT).
        intros H6. 
        assert
          (H7: In x0
             (freeVarF 
                (LNN2LNT_formula
                   (substF 
                      (substF a v (var x))
                      v0 s))))
          by (eapply List.in_remove; apply H6). 
        assert
          (H8: In x0
                 (freeVarF 
                    (substF (substF a v (var x)) v0 s)))
          by (apply LNN2LNT_freeVarF1; assumption).
        induction (freeVarSubFormula3 _ _ _ _ _ H8).
        assert
          (H10: In x0 (freeVarF 
                         (substF a v (var x)))) 
          by (eapply in_remove; apply H9).
        induction (freeVarSubFormula3 _ _ _ _ _ H10).
        elim H5.
        eapply in_in_remove.
        { eapply in_remove_neq, H11. }
        { apply LNN2LNT_freeVarF2.
          eapply in_remove.
          apply H11.
        } 
        elim (in_remove_neq _ _ _ _ _ H6).
        destruct H11 as [H11| H11].
        -- auto.
        -- contradiction.
        -- elim H4.
        rewrite LNN2LNT_freeVarT.
        assumption.
        -- apply (reduceForall LNT).
           apply (notInFreeVarSys LNT).
           apply
             iffTrans
             with
             (substF 
                (substF 
                   (substF  (LNN2LNT_formula a) v 
                      (var x)) v0
                   (LNN2LNT_term s)) x (var x0)).
           apply (reduceSub LNT).
           apply (notInFreeVarSys LNT).
           eapply iffTrans.
           apply H.
           eapply eqDepth.
           symmetry  in |- *; rewrite subFormulaDepth; 
             symmetry  in |- *. (*Hack to rewrite the right occ*)
           reflexivity.
           apply depthForall.
           apply (reduceSub LNT).
           apply (notInFreeVarSys LNT).
           eapply iffTrans.
           apply H.
           apply depthForall.
           simpl in |- *.
           apply iffRefl.
           eapply iffTrans.
           apply (subFormulaExch LNT).
           auto.
           rewrite LNN2LNT_freeVarT.
           auto.
           simpl in |- *.
           tauto.
           apply (reduceSub LNT).
           apply (notInFreeVarSys LNT).
           apply (subFormulaTrans LNT).
           unfold not in |- *; intros; elim H2.
           apply  in_in_remove.
           { eapply in_remove_neq, H6. }
           { apply LNN2LNT_freeVarF1.
             eapply in_remove.
             apply H6.
           }            
           
Qed.

(** ** Inverse translation *)

Fixpoint LNT2LNN_formula (f : Formula) : fol.Formula LNN :=
  match f with
  | (t1 = t2)%nt => (LNT2LNN_term t1 = LNT2LNN_term t2)%fol
  | atomic r ts => match r with
                   end
  | (A -> B)%nt => (LNT2LNN_formula A -> LNT2LNN_formula B)%fol
  | (~  A)%nt =>   (~ LNT2LNN_formula A)%fol
  | (allH v, A)%nt => (allH v, LNT2LNN_formula A)%fol
  end.

(** *** Commutation lemmas *)

Lemma LNT2LNT_formula (f : Formula): 
 LNN2LNT_formula (LNT2LNN_formula f) = f.
Proof.
  induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
    simpl.
- now repeat rewrite LNT2LNT_term.
- destruct r.
- now rewrite Hrecf1, Hrecf0.
- now rewrite Hrecf.
- now rewrite Hrecf.
Qed.

Lemma LNT2LNN_subTerm  (t : Term) (v : nat) (s : Term):
  LNT2LNN_term (substT t v s) =
    substT (LNT2LNN_term t) v (LNT2LNN_term s).
Proof.
  elim t using
    Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms LNT n) =>
             LNT2LNN_terms n (substTs ts v s) =
               substTs (LNT2LNN_terms n ts) v 
                 (LNT2LNN_term s)); simpl.
  - intro n; destruct (eq_nat_dec v n); reflexivity.
  - intros f t0 H; rewrite H; reflexivity.
  - reflexivity. 
  - intros n t0 H t1 H0; now rewrite H, H0.
Qed.

Lemma LNT2LNN_freeVarT ( t : Term):
  freeVarT (LNT2LNN_term t) = freeVarT t.
Proof.
  elim t using
    Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms LNT n) =>
             freeVarTs  (LNT2LNN_terms n ts) = freeVarTs ts);
    simpl in |- *.  
  - reflexivity.
  - intros f t0 H; transitivity
                     (freeVarTs 
                        (LNT2LNN_terms (LNTFunctionArity f) t0)).
    + reflexivity.
    + now rewrite H.
  - reflexivity.
  - intros n t0 H t1 H0; transitivity
                           (freeVarT (LNT2LNN_term t0) ++
                              freeVarTs (LNT2LNN_terms n t1)).
    + reflexivity.
    + now rewrite H, H0.
Qed.

Lemma LNT2LNN_freeVarF (f : Formula):
  freeVarF (LNT2LNN_formula f) = freeVarF f.
Proof.
  induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
    simpl in |- *.
  - repeat rewrite LNT2LNN_freeVarT; reflexivity.
  - destruct r.
  - now rewrite Hrecf1,  Hrecf0.
  - assumption.
  - now rewrite Hrecf.
Qed.

Lemma LNT2LNN_subFormula :
  forall (f : Formula) (v : nat) (s : Term),
    LNT2LNN_formula (substF f v s) =
      substF (LNT2LNN_formula f) v (LNT2LNN_term s).
Proof.
  intro f.
  elim f using Formula_depth_ind2; simpl in |- *.
  - intros t t0 v s; now repeat rewrite LNT2LNN_subTerm.
  - intro r; destruct r.
  - intros f0 H f1 H0 v s; rewrite (subFormulaImp LNT).
    simpl; now rewrite H, H0, (subFormulaImp LNN).
  - intros f0 H n H0; rewrite (subFormulaNot LNT); simpl. 
    now rewrite H, (subFormulaNot LNN).
  - intros v a H v0 s; 
      rewrite (subFormulaForall LNT), (subFormulaForall LNN).
    destruct (eq_nat_dec v v0) as [e | n].
    + reflexivity.
    + rewrite LNT2LNN_freeVarT.
      destruct (In_dec eq_nat_dec v (freeVarT s)) as [i | i].
      * simpl; repeat rewrite H; simpl. 
        -- now rewrite LNT2LNN_freeVarF.
        -- apply depthForall.
        -- eapply eqDepth.
           ++ symmetry; rewrite subFormulaDepth; symmetry.
              reflexivity.
           ++ apply depthForall.
      * simpl; rewrite H.
        -- reflexivity.
        -- apply depthForall.
Qed.

(** * Proof translation *)

(* begin hide *)
Section Translate_Proof.

Variable U : fol.System LNN.
Variable V : System.

Hypothesis
  AxiomsOK :
    forall f : fol.Formula LNN, mem _ U f ->  
    exists Axm : Formulas,
    (exists prf : Prf LNT Axm (LNN2LNT_formula f),
       (forall g : Formula, In g Axm -> mem _ V g)) /\
    forall v, In v (freeVarListFormula LNT Axm) -> 
              (In v (freeVarF f)).

Lemma translatePrf f : 
 forall axm:fol.Formulas LNN, Prf LNN axm f -> 
  (forall g, In g axm -> mem _ U g) ->
  exists Axm : Formulas,
    (exists prf : Prf LNT Axm (LNN2LNT_formula f),
       (forall g : Formula, In g Axm -> mem _ V g)) /\
    forall v, In v (freeVarListFormula LNT Axm) -> 
              (In v (freeVarListFormula LNN axm)).
Proof.
  intros x x0 H; induction x0
    as
    [A|
      Axm1 Axm2 A B x0_1 Hrecx0_1 x0_0 Hrecx0_0|
      Axm A v n x0 Hrecx0|
      A B|
      A B C|
      A B|
      A v t|
      A v n|
      A B v|
    |
    |
    |
      R|
      f].
  - destruct (AxiomsOK A). 
    + apply H; now constructor. 
    + exists x; destruct H0 as [H0 H1].
      split.
      * apply H0.
      * intros v H2; simpl; rewrite app_nil_r.
        apply H1, H2.
  - assert (H0: forall g : fol.Formula LNN,
               In g Axm2 -> mem (fol.Formula LNN) U g).
    { intros g H0; apply H; apply in_or_app; now right.
    } 
    assert (H1: forall g : fol.Formula LNN,
               In g Axm1 -> mem (fol.Formula LNN) U g).
    { intros g H1; apply H; apply in_or_app; now left. }
    destruct (Hrecx0_0 H0) as [x [[x0 I0] Z0]].
    destruct (Hrecx0_1 H1) as [x1 [[x2 I1] Z1]].
    clear H0 H1; rename I0 into H0; rename I1 into H1.
    exists (x1 ++ x);  simpl in x2; split.
    + exists (MP LNT _ _ _ _ x2 x0).
      intros g H2; induction (in_app_or _ _ _ H2); auto.
    + intros v H2;  rewrite freeVarListFormulaApp.
      rewrite freeVarListFormulaApp in H2;  apply in_or_app.
      destruct (in_app_or _ _ _ H2); auto with *.
  - destruct (Hrecx0 H) as [x [[x1 H0] Z]]; exists x.
    assert (H1: ~ In v (freeVarListFormula LNT x)) by firstorder.
    split.
    + exists (GEN LNT _ _ _ H1 x1) ; assumption.
    + assumption.
  - exists (nil (A:=Formula)); split.
    + exists (IMP1 LNT (LNN2LNT_formula A) (LNN2LNT_formula B)).
      contradiction.
    + contradiction.
  - exists (nil (A:=Formula)); split.
    * exists (IMP2 LNT (LNN2LNT_formula A) (LNN2LNT_formula B) 
                (LNN2LNT_formula C)); contradiction.
    * contradiction.
  - exists (nil (A:=Formula)); split.
    * exists (CP LNT (LNN2LNT_formula A) (LNN2LNT_formula B)).
      contradiction.
    * contradiction.
  - assert (H0: SysPrf (Empty_set _)
                  (LNN2LNT_formula 
                     (impH (forallH v A) 
                        (substF A v t)))).
    { simpl in |- *.
      apply impE with
        (impH (forallH v (LNN2LNT_formula A))
           (substF (LNN2LNT_formula A) v 
              (LNN2LNT_term t))).
      apply iffE1.
      apply (reduceImp LNT).
      apply iffRefl.
      apply iffSym.
      apply LNN2LNT_subFormula.
      exists (nil (A:=Formula)).
      exists (FA1 LNT (LNN2LNT_formula A) v (LNN2LNT_term t)).
      contradiction.
    }
    destruct H0 as [x H0]; exists x; split.
    + destruct H0 as [x0 H0]; exists x0.
      intros g H1; elim (H0 g H1).
    + intros v0 H1; destruct H0.
      * destruct x. 
        -- assumption.
        -- assert (H2: In f (f::x)) by  auto with *.
           elim (H0 f H2).
  - exists (nil (A:=Formula)).
    assert (H0: ~ In v (freeVarF (LNN2LNT_formula A)))
    by (intro H0; elim n; now apply LNN2LNT_freeVarF1).
    split.
    + exists (FA2 LNT (LNN2LNT_formula A) v H0); contradiction.
    + contradiction.
  - exists (nil (A:=Formula)); split.
    + exists (FA3 LNT (LNN2LNT_formula A) (LNN2LNT_formula B) v);
        contradiction.
    + contradiction.
  - exists (nil (A:=Formula)); split.
    + exists (EQ1 LNT); contradiction.
    + contradiction.
  - exists (nil (A:=Formula)); split.
    + exists (EQ2 LNT); contradiction.
    + contradiction.
  - exists (nil (A:=Formula)); split.
    + exists (EQ3 LNT); contradiction.
    + contradiction.
  - assert (H0: SysPrf (Empty_set _) (LNN2LNT_formula (AxmEq4 LNN R))).
    { induction R; simpl; repeat apply impI.
       apply impE
        with
        (iffH
           (translateLT
              (Tcons (var 2)
                 (Tcons (var 0) (Tnil))))
           (translateLT
              (Tcons (var 3)
                 (Tcons (var 1) (Tnil))))).
      - apply impRefl.
      - repeat rewrite translateLT1; simpl; unfold newVar; simpl.  
        apply impE 
          with
          (iffH (existH 3 (equal (LNT.Plus (var 2) (LNT.Succ (var 3))) (var 0)))
             (existH 4 (equal (LNT.Plus (var 3) (LNT.Succ (var 4))) (var 1)))).
        + apply impRefl.
        + eapply iffTrans with
            (exH 4,
               (substF (v#2 + LNT.Succ v#3 = v#0)%nt 3 (v#4)))%nt.
          * apply (rebindExist LNT).
            simpl in |- *. intro H0; decompose sum H0.
            -- discriminate H1.
            -- discriminate H2.
          * apply (reduceExist LNT).
            intros (x, (H0, H1)).
            destruct H1 as [x H1| x H1]; [ destruct H1 as [x H1| x H1] | 
                                           destruct H1 ].
            -- elim H1.
            -- induction H1.
               simpl in H0.
               decompose sum H0.
               discriminate H1.
               discriminate H2.
            -- simpl in H0; decompose sum H0.
               discriminate H1.
               discriminate H2.
            -- repeat rewrite (subFormulaEqual LNT); simpl.
               apply iffI.
               ++ apply impI.
                  apply eqTrans with (var 0).
                  ** apply eqTrans with (LNT.Plus (var 2) (LNT.Succ (var 4))).
                     apply eqPlus.
                     apply eqSym.
                     apply Axm.
                     left.
                     left.
                     right.
                     constructor.
                     apply eqRefl.
                     apply Axm.
                     right; constructor.
                  ** apply Axm; left; right; constructor.
               ++ apply impI.
                  apply eqTrans with (var 1).
                  **  apply eqTrans with (v#3 + LNT.Succ v#4)%nt.
                      fold (LNT.Succ (var 4)) in |- *.
                      fold (LNT.Plus (var 2) (LNT.Succ (var 4))) in |- *.
                      apply eqPlus.
                      apply Axm.
                      left.
                      left.
                      right.
                      constructor.
                      apply eqRefl.
                      apply Axm.
                      right; constructor.
                  ** apply eqSym.
                     apply Axm; left; right; constructor.
    }    
    destruct H0 as [x H0]; exists x.
    destruct H0 as [x0 H0]; split.
    + exists x0; intros g H1; elim (H0 g H1).
    + intros v H1; destruct x.
      * assumption.
      * assert (H2: In f (f::x)) by auto with *.
        elim (H0 _ H2).
  - replace (LNN2LNT_formula (AxmEq5 LNN f)) with (AxmEq5 LNT f).
    + exists (nil (A:=Formula)); split.
      * exists (EQ5 LNT f); contradiction.
      * contradiction.
    + induction f; reflexivity.
Qed.

End Translate_Proof.

(* end hide *)

(**   If the translation of every axiom of a [LNN]-system [U] is provable in a closed 
      [LNT]-system [V], 
      then the translation of any [LNN]-formula in [U] is provable in [V].
*)

Lemma translateProof (U : fol.System LNN) (V : System):
    ClosedSystem LNT V ->
    (forall f : fol.Formula LNN,
        mem (fol.Formula LNN) U f -> SysPrf V (LNN2LNT_formula f)) ->
    forall f : fol.Formula LNN,
      folProof.SysPrf LNN U f -> SysPrf V (LNN2LNT_formula f).
Proof.
  intros H H0 f [x H1]. 
  assert (H2: forall f : fol.Formula LNN,
             mem (fol.Formula LNN) U f ->
             exists Axm : Formulas,
               ex
                 (fun _ : Prf LNT Axm (LNN2LNT_formula f) =>
                    forall g : Formula, In g Axm -> 
                                        mem (fol.Formula LNT) V g) /\
                 (forall v : nat,
                     In v (freeVarListFormula LNT Axm) -> 
                     In v (freeVarF f))).
  { intros f0 H2; destruct (H0 f0 H2) as [x0 H3]. 
    exists x0; split.
    - apply H3.
    - intros v H4; destruct H3.
      clear x1; induction x0.
      + elim H4.
      + destruct (in_app_or _ _ _ H4) as [H5 | H5].
        *  elim H with v a.
           apply H3.
           auto with *.
           assumption.
        * apply IHx0.
          firstorder.
          apply H5.
  }   
  destruct H1.
  destruct (translatePrf U V H2 f x x0 H1).
  exists x1; tauto.
Qed.



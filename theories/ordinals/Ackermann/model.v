Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import ListExt.
Require Import folProof.
Require Import folProp.
Require Vector.
Require Import Peano_dec.
Require Import misc.
Require Import Arith.

Section Model_Theory.

Variable L : Language.

Fixpoint naryFunc (A : Set) (n : nat) {struct n} : Set :=
  match n with
  | O => A
  | S m => A -> naryFunc A m
  end.

Fixpoint naryRel (A : Set) (n : nat) {struct n} : Type :=
  match n with
  | O => Prop
  | S m => A -> naryRel A m
  end.

Record Model : Type := model
  {U : Set;
   func : forall f : Functions L, naryFunc U (arity L (inr _ f));
   rel : forall r : Relations L, naryRel U (arity L (inl _ r))}.

Variable M : Model.

Fixpoint interpTerm (value : nat -> U M) (t : Term L) {struct t} : 
 U M :=
  match t with
  | var v => value v
  | apply f ts => interpTerms _ (func M f) value ts
  end
 
 with interpTerms (m : nat) (f : naryFunc (U M) m) 
 (value : nat -> U M) (ts : Terms L m) {struct ts} : 
 U M :=
  match ts in (Terms _ n) return (naryFunc (U M) n -> U M) with
  | Tnil => fun f => f
  | Tcons m t ts => fun f => interpTerms m (f (interpTerm value t)) value ts
  end f.

Fixpoint interpRels (m : nat) (r : naryRel (U M) m) 
 (value : nat -> U M) (ts : Terms L m) {struct ts} : Prop :=
  match ts in (Terms _ n) return (naryRel (U M) n -> Prop) with
  | Tnil => fun r => r
  | Tcons m t ts => fun r => interpRels m (r (interpTerm value t)) value ts
  end r.

Definition updateValue (value : nat -> U M) (n : nat) 
  (v : U M) (x : nat) : U M :=
  match eq_nat_dec n x with
  | left _ => v
  | right _ => value x
  end.

Fixpoint interpFormula (value : nat -> U M) (f : Formula L) {struct f} :
 Prop :=
  match f with
  | equal t s => interpTerm value t = interpTerm value s
  | atomic r ts => interpRels _ (rel M r) value ts
  | impH A B => interpFormula value A -> interpFormula value B
  | notH A => interpFormula value A -> False
  | forallH v A => forall x : U M, interpFormula (updateValue value v x) A
  end.

Lemma freeVarInterpTerm (v1 v2 : nat -> U M) (t : Term L):
 (forall x : nat, In x (freeVarTerm L t) -> v1 x = v2 x) ->
 interpTerm v1 t = interpTerm v2 t.
Proof.
  elim t using  Term_Terms_ind with
    (P0 := fun (n : nat) (ts : Terms L n) =>
             forall f : naryFunc (U M) n,
               (forall x : nat, In x (freeVarTerms L n ts) -> v1 x = v2 x) ->
               interpTerms n f v1 ts = interpTerms n f v2 ts); 
    simpl.
  - intros n H; apply H; left; auto.
  - intros f t0 H H0; apply H.
    intros x H1; apply H0, H1.
  - reflexivity. 
  - intros n t0 H t1 H0 f H1.
    rewrite H.  
    apply H0.
    intros x H2; apply H1.
    + unfold freeVarTerms; apply in_or_app.
      right; apply H2.
    + intros x H2; apply H1.
      unfold freeVarTerms; apply in_or_app; left.
      apply H2.
Qed.

Lemma freeVarInterpRel (v1 v2 : nat -> U M) (n : nat) 
  (ts : Terms L n) (r : naryRel (U M) n): 
  (forall x : nat, In x (freeVarTerms L n ts) -> v1 x = v2 x) ->
  interpRels n r v1 ts -> interpRels n r v2 ts.
Proof.
  intros H; induction ts as [| n t ts Hrects]; simpl in |- *.
  - auto.
  - rewrite (freeVarInterpTerm v1 v2).
    + apply Hrects.
      intros x H0; apply H.
      unfold freeVarTerms; apply in_or_app; right; apply H0.
    + intros x H0; apply H.
      unfold freeVarTerms; apply in_or_app; left; apply H0.
Qed.

Lemma freeVarInterpFormula (v1 v2 : nat -> U M) (g : Formula L):
 (forall x : nat, In x (freeVarFormula L g) -> v1 x = v2 x) ->
 interpFormula v1 g -> interpFormula v2 g.
Proof.
  revert v1 v2.
  induction g as [t t0| r t| g1 Hrecg1 g0 Hrecg0| g Hrecg| n g Hrecg];
    simpl in |- *; intros v1 v2 H.
  - repeat rewrite (freeVarInterpTerm v1 v2).
    + auto.
    + intros x H0; apply H.
      simpl; auto with datatypes.
    + intros x H0; apply H.
      simpl; auto with datatypes.
  - intros H0; apply (freeVarInterpRel v1 v2).
    + apply H. 
    + apply H0. 
  - assert (H0: interpFormula v2 g1 -> interpFormula v1 g1).
    { apply Hrecg1.
      intros x H0; symmetry; apply H.
      simpl; auto with datatypes.
    } 
    assert (H1: interpFormula v1 g0 -> interpFormula v2 g0).
    { apply Hrecg0.
      intros x H1; apply H; simpl; auto with datatypes.
    } 
    tauto.
  - intros H0 H1; apply H0.
    apply Hrecg with v2.
    intros x H2; symmetry; auto.
    assumption.
  - intros H0 x; apply Hrecg with (updateValue v1 n x).
    + intros x0 H1; unfold updateValue; induction (eq_nat_dec n x0).
      * reflexivity.
      * apply H.
        apply In_list_remove3; auto.
    + auto.
Qed.
 
Lemma subInterpTerm (value : nat -> U M) (t : Term L) (v : nat) (s : Term L):
 interpTerm (updateValue value v (interpTerm value s)) t =
 interpTerm value (substituteTerm L t v s).
Proof.
  elim t using  Term_Terms_ind  with
    (P0 := fun (n : nat) (ts : Terms L n) =>
             forall f : naryFunc (U M) n,
               interpTerms n f (updateValue value v (interpTerm value s)) ts =
                 interpTerms n f value (substituteTerms L n ts v s)); 
    simpl.
  - intro n; unfold updateValue; induction (eq_nat_dec v n); reflexivity.
  - intros f t0 H; rewrite H.
    + reflexivity.
  - reflexivity.
  - intros n t0 H t1 H0 f; rewrite H; apply H0.
Qed.                    

Lemma subInterpRel (value : nat -> U M) (n : nat) (ts : Terms L n) 
  (v : nat) (s : Term L) (r : naryRel (U M) n):
  interpRels n r (updateValue value v (interpTerm value s)) ts <->
    interpRels n r value (substituteTerms L n ts v s).
Proof.
  induction ts as [| n t ts Hrects].
  - simpl; tauto.
  - simpl; rewrite <- subInterpTerm; apply Hrects.
Qed.

Lemma subInterpFormula :
 forall (value : nat -> U M) (f : Formula L) (v : nat) (s : Term L),
 interpFormula (updateValue value v (interpTerm value s)) f <->
 interpFormula value (substituteFormula L f v s).
Proof.
  intros value f; revert value.
  elim f using Formula_depth_ind2; simpl.
  - intros t t0 value v s; repeat rewrite subInterpTerm.
    tauto.
  - intros r t value v s; apply subInterpRel.
  - intros f0 H f1 H0 value v s; rewrite (subFormulaImp L).
    simpl;
    assert
      (H1: interpFormula (updateValue value v (interpTerm value s)) f1 <->
         interpFormula value (substituteFormula L f1 v s)) by auto.
    assert
      (H2: interpFormula (updateValue value v (interpTerm value s)) f0 <->
         interpFormula value (substituteFormula L f0 v s)) by auto.
    tauto.
  - intros f0 H value v s; rewrite (subFormulaNot L).
    simpl in |- *.
    assert
      (interpFormula (updateValue value v (interpTerm value s)) f0 <->
         interpFormula value (substituteFormula L f0 v s)).
    auto.
    tauto.
  - intros v a H value v0 s; rewrite (subFormulaForall L).
    induction (eq_nat_dec v v0) as [a0 | b].
    + rewrite a0.
    simpl in |- *.
    unfold updateValue in |- *.
    split.
      *  intros H0 x;  apply freeVarInterpFormula with
           (fun x0 : nat =>
              match eq_nat_dec v0 x0 with
              | left _ => x
              | right _ =>
                  match eq_nat_dec v0 x0 with
                  | left _ => interpTerm value s
                  | right _ => value x0
                  end
              end).
         -- intros x0 H1; induction (eq_nat_dec v0 x0); reflexivity.
         -- auto.
      * intros H0 x; apply
          freeVarInterpFormula
          with
          (fun x0 : nat =>
             match eq_nat_dec v0 x0 with
             | left _ => x
             | right _ => value x0
             end).
        -- intros x0 H1; induction (eq_nat_dec v0 x0); reflexivity.
        --  auto.
    + induction (In_dec eq_nat_dec v (freeVarTerm L s)) as [a0 | b0].
      * simpl;
        set (nv := newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a)) in *.
        assert (~ In nv (v0 :: freeVarTerm L s ++ freeVarFormula L a)).
        { unfold nv in |- *.
          apply newVar1. }
        assert
              (forall (x : U M) (x0 : nat),
                  In x0 (freeVarFormula L a) ->
                  updateValue (updateValue value v0 (interpTerm value s)) v x x0 =
                    updateValue
                      (updateValue (updateValue value nv x) v0
                         (interpTerm (updateValue value nv x) s)) v
                      (interpTerm
                         (updateValue (updateValue value nv x) v0
                            (interpTerm (updateValue value nv x) s)) 
                         (var L nv)) x0).
    { intros x x0 H1; unfold updateValue in |- *; simpl in |- *.
      induction (eq_nat_dec v x0) as [a1 | ?].
      - induction (eq_nat_dec v0 nv) as [a2 | b0].
        + elim H0.
          rewrite a2.
          simpl in |- *.
          auto.
        + induction (eq_nat_dec nv nv) as [a2 | b1].
          * reflexivity.
          * elim b1; reflexivity.
      - induction (eq_nat_dec v0 x0) as [a1 | b1].
        + apply freeVarInterpTerm.
          intros x1 H2; induction (eq_nat_dec nv x1).
          * elim H0.
            rewrite a2.
            simpl in |- *.
            auto with datatypes.
          * reflexivity.
        + induction (eq_nat_dec nv x0) as [a1 | ?].
          * elim H0.
            rewrite a1.
            auto with datatypes.
          * reflexivity.
    }    
    assert
      (H2: (forall x : U M,
           interpFormula
             (updateValue
                (updateValue (updateValue value nv x) v0
                   (interpTerm (updateValue value nv x) s)) v
                (interpTerm
                   (updateValue (updateValue value nv x) v0
                      (interpTerm (updateValue value nv x) s)) 
                   (var L nv))) a) <->
         (forall x : U M,
             interpFormula (updateValue value nv x)
               (substituteFormula L (substituteFormula L a v (var L nv)) v0 s))).
    { split.
      - assert
          (H2: forall b : Formula L,
              lt_depth L b (forallH v a) ->
              forall (value : nat -> U M) (v : nat) (s : Term L),
                interpFormula (updateValue value v (interpTerm value s)) b ->
                interpFormula value (substituteFormula L b v s)).
        { intros b0 H2 value0 v1 s0 H3;
          induction (H b0 H2 value0 v1 s0); auto.
        }    
        intros H3 x; apply H2.
        + eapply eqDepth.
          * symmetry; apply subFormulaDepth.
          * apply depthForall.
        + apply H2.
          * apply depthForall.
          * apply H3.
      - intros H2 x.
        assert
          (H3: forall b : Formula L,
              lt_depth L b (forallH v a) ->
              forall (value : nat -> U M) (v : nat) (s : Term L),
                interpFormula value (substituteFormula L b v s) ->
                interpFormula (updateValue value v (interpTerm value s)) b) 
          by (intros; induction (H b0 H3 value0 v1 s0); auto).
        clear H; apply H3.
        + apply depthForall.
        + apply H3.
          * eapply eqDepth.
            -- symmetry; apply subFormulaDepth.
            -- apply depthForall.
          * auto.
    }    
    assert
      (H3: (forall x : U M,
           interpFormula
             (updateValue (updateValue value v0 (interpTerm value s)) v x) a) <->
         (forall x : U M,
             interpFormula
               (updateValue
                  (updateValue (updateValue value nv x) v0
                     (interpTerm (updateValue value nv x) s)) v
                  (interpTerm
                     (updateValue (updateValue value nv x) v0
                        (interpTerm (updateValue value nv x) s)) 
                     (var L nv))) a)).
    { split.
      - intros H3 x;
        apply
          freeVarInterpFormula
          with (updateValue (updateValue value v0 (interpTerm value s)) v x).
        auto.
        auto.
      - intros H3 x.
        apply
          freeVarInterpFormula
          with
          (updateValue
             (updateValue (updateValue value nv x) v0
                (interpTerm (updateValue value nv x) s)) v
             (interpTerm
                (updateValue (updateValue value nv x) v0
                   (interpTerm (updateValue value nv x) s)) 
                (var L nv))).
        + intros x0 H4;
          symmetry  in |- *.
          auto.
        + auto.
    }    
    tauto.
      * simpl in |- *.
        assert
          (forall (x : U M) (x0 : nat),
              In x0 (freeVarFormula L a) ->
              updateValue (updateValue value v0 (interpTerm value s)) v x x0 =
                updateValue (updateValue value v x) v0
                  (interpTerm (updateValue value v x) s) x0).
        { intros x x0 H0; unfold updateValue;
          induction (eq_nat_dec v x0) as [a0 | b1].
          - induction (eq_nat_dec v0 x0) as [a1 | ?].
            + elim b.
              transitivity x0; auto.
            +  reflexivity.
          - induction (eq_nat_dec v0 x0) as [a0 | ?].
            + apply freeVarInterpTerm.
              intros x1 H1; induction (eq_nat_dec v x1).
              * elim b0.
                rewrite a1.
                auto.
              * reflexivity.
            + reflexivity.
        }    
        split.
        --  intros H1 x;
        assert
          (H2: forall b : Formula L,
              lt_depth L b (forallH v a) ->
              forall (value : nat -> U M) (v : nat) (s : Term L),
                interpFormula (updateValue value v (interpTerm value s)) b ->
                interpFormula value (substituteFormula L b v s)).
        { intros b1 H2 value0 v1 s0 H3; induction (H b1 H2 value0 v1 s0); auto. }
        apply H2.
        ++ apply depthForall.
        ++ apply freeVarInterpFormula with 
             (updateValue (updateValue value v0 (interpTerm value s)) v x).
           ** apply (H0 x).
           ** apply H1.
    -- assert
        (forall b : Formula L,
            lt_depth L b (forallH v a) ->
            forall (value : nat -> U M) (v : nat) (s : Term L),
              interpFormula value (substituteFormula L b v s) ->
              interpFormula (updateValue value v (interpTerm value s)) b).
       { intros b1 H1 value0 v1 s0 H2; induction (H b1 H1 value0 v1 s0); auto. }
       intros H2 x; 
       apply
         freeVarInterpFormula
         with
         (updateValue (updateValue value v x) v0
            (interpTerm (updateValue value v x) s)).
       ++ intros; symmetry  in |- *; auto.
       ++ apply H1.
          ** apply depthForall.
          ** auto.
Qed.

Lemma subInterpFormula1 (value : nat -> U M) (f : Formula L) (v : nat) (s : Term L):
 interpFormula (updateValue value v (interpTerm value s)) f ->
 interpFormula value (substituteFormula L f v s).
Proof.
  induction (subInterpFormula value f v s); auto.
Qed.

Lemma subInterpFormula2 (value : nat -> U M) (f : Formula L) (v : nat) (s : Term L):
  interpFormula value (substituteFormula L f v s) ->
  interpFormula (updateValue value v (interpTerm value s)) f.
Proof.
  induction (subInterpFormula value f v s); auto.
Qed.

Fixpoint nnHelp (f : Formula L) : Formula L :=
  match f with
  | equal t s => equal L t s
  | atomic r ts => atomic L r ts
  | impH A B => impH (nnHelp A) (nnHelp B)
  | notH A => notH (nnHelp A)
  | forallH v A => forallH v (notH (notH (nnHelp A)))
  end.

Definition nnTranslate (f : Formula L) : Formula L :=
  notH (notH (nnHelp f)).

Lemma freeVarNNHelp (f : Formula L):  freeVarFormula L f = freeVarFormula L (nnHelp f).
Proof.
  induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
    try reflexivity.
  - simpl; now rewrite Hrecf1, Hrecf0.
  - simpl; assumption.
  - simpl; now rewrite Hrecf.
Qed.

Lemma subNNHelp :
 forall (f : Formula L) (v : nat) (s : Term L),
 substituteFormula L (nnHelp f) v s = nnHelp (substituteFormula L f v s).
Proof.
  intro f; elim f using Formula_depth_ind2; intros; try reflexivity.
  - simpl; rewrite subFormulaImp, H, H0. 
    now rewrite subFormulaImp.
  - simpl; rewrite subFormulaNot, H, subFormulaNot; easy.
  - simpl; do 2 rewrite subFormulaForall.
    simpl; induction (eq_nat_dec v v0).
    + simpl; reflexivity.
    + induction (In_dec eq_nat_dec v (freeVarTerm L s)) as [? | ?].
      * simpl; repeat rewrite subFormulaNot; repeat rewrite H.
        -- now rewrite <- freeVarNNHelp.
        -- eapply eqDepth.
           ++ symmetry; apply subFormulaDepth.
           ++ apply depthForall.
        -- apply depthForall.
      * repeat rewrite subFormulaNot.
        rewrite H; simpl.
        -- reflexivity.
        -- apply depthForall.
Qed.

Section Consistent_Theory.

  Variable T : System L.

  Fixpoint interpTermsVector (value : nat -> U M) (n : nat) 
    (ts : Terms L n) {struct ts} : Vector.t (U M) n :=
    match ts in (Terms _ n) return (Vector.t (U M) n) with
    | Tnil => Vector.nil (U M)
    | Tcons m t ts =>
        Vector.cons (U M) (interpTerm value t) m (interpTermsVector value m ts)
    end.

Lemma preserveValue (value : nat -> U M):
 (forall f : Formula L,
  mem _ T f -> interpFormula value (nnTranslate f)) ->
 forall g : Formula L, SysPrf L T g -> interpFormula value (nnTranslate g).
Proof.
  intros H g H0.
  induction H0 as (x, H0).
  induction H0 as (x0, H0).
  cut (forall g : Formula L, In g x -> interpFormula value (nnTranslate g)).
  - clear H H0; revert value.
    induction x0
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
        f]; intros; try (simpl in |- *; tauto).
    + apply H.
      auto with datatypes.
    + assert (H0: interpFormula value (nnTranslate A))
      by auto with datatypes.
      assert (H1: interpFormula value (nnTranslate (impH A B)))
        by auto with datatypes.
      clear Hrecx0_1 Hrecx0_0.
      simpl in H0, H1. 
      simpl in |- *.
      tauto.
    + simpl in |- *.
      intros.
      apply H0.
      clear H0.
      intros.
      simpl in Hrecx0.
      apply (Hrecx0 (updateValue value v x)).
      * intros.
        simpl in H.
        eapply H.
        -- apply H1.
        -- intros.
           apply H2.
           apply freeVarInterpFormula with value.
           ++ intros.
              rewrite <- freeVarNNHelp in H4.
              unfold updateValue in |- *.
              induction (eq_nat_dec v x1).
              ** elim n.
                 rewrite a.
                 clear n x0 Hrecx0 H.
                 induction Axm as [| a0 Axm HrecAxm].
                 apply H1.
                 simpl in |- *.
                 simpl in H1.
                 induction H1 as [H| H].
                 rewrite H.
                 auto with datatypes.
                 auto with datatypes.
              ** reflexivity.
           ++ assumption.
      * assumption.
    + simpl in |- *.
      intros.
      apply H0.
      intros.
      elim H1 with (interpTerm value t).
      intros.
      apply H0.
      intros.
      rewrite <- subNNHelp.
      apply subInterpFormula1.
      auto.
    + simpl in |- *.
      intros.
      apply H0.
      intros.
      apply H2.
      apply freeVarInterpFormula with value.
      * intros.
        unfold updateValue in |- *.
        induction (eq_nat_dec v x0).
        -- elim n.
           rewrite a.
           rewrite freeVarNNHelp.
           assumption.
        -- reflexivity.
      * assumption.
    + simpl in |- *.
      intros.
      apply H0.
      clear H0.
      intros.
      apply H0 with x.
      intros.
      apply H1 with x.
      auto.
    + simpl in |- *.
      auto.
    + simpl in |- *.
      intros.
      apply H0.
      intros.
      transitivity (value 1); auto.
    + simpl in |- *.
      intros.
      apply H0.
      clear H H0.
      unfold AxmEq4 in |- *.
      cut
        (forall a b : Terms L (arity L (inl (Functions L) R)),
            interpTermsVector value _ a = interpTermsVector value _ b ->
            interpFormula value (nnHelp (iffH L (atomic L R a) (atomic L R b)))).
      * assert
          (H: forall A,
              (forall a b : Terms L (arity L (inl (Functions L) R)),
                  interpTermsVector value (arity L (inl (Functions L) R)) a =
                    interpTermsVector value (arity L (inl (Functions L) R)) b ->
                  interpFormula value (nnHelp (A a b))) ->
              interpFormula value
                (nnHelp
                   (nat_rec (fun _ : nat => Formula L)
                      (prod_rec
                         (fun
                             _ : Terms L (arity L (inl (Functions L) R)) *
                                   Terms L (arity L (inl (Functions L) R)) => 
                             Formula L)
                         (fun a b : Terms L (arity L (inl (Functions L) R)) => A a b)
                         (nVars L (arity L (inl (Functions L) R))))
                      (fun (n : nat) (Hrecn : Formula L) =>
                         impH (equal L (var L (n + n)) (var L (S (n + n)))) Hrecn)
                      (arity L (inl (Functions L) R))))).
        { generalize (arity L (inl (Functions L) R)).
          simple induction n.
          - simpl; intros A H; now apply H.
          - intros n0 H A H0; simpl; induction (nVars L n0).
            simpl in H |- *.
            intro H1; apply
                        (H
                           (fun x y : Terms L n0 =>
                              A (Tcons L n0 (var L (n0 + n0)) x) 
                                (Tcons L n0 (var L (S (n0 + n0))) y))).
            intros a0 b0 H2; apply H0.
            simpl; rewrite H1.
            now rewrite H2.
        } 
        apply (H (fun a b => iffH L (atomic L R a) (atomic L R b))).
      * simpl; generalize (rel M R).
        generalize (arity L (inl (Functions L) R)).
        intros n n0 a b H H0.
        induction a as [| n t a Hreca].
        -- assert (H1: b = Tnil L) by (symmetry; apply nilTerms).
           rewrite H1 in H0; auto.
        -- induction (consTerms L n b) as [x p].
           induction x as (a0, b0).
           simpl in p.
           rewrite <- p in H0.
           rewrite <- p in H.
           simpl in H.
           inversion H.
           simpl in H0.
           rewrite H2 in H0.
           apply (Hreca (n0 (interpTerm value a0)) b0).
           ++ apply (inj_right_pair2 _ eq_nat_dec _ _ _ _ H3).
           ++ auto.
    + simpl in |- *.
      intros H0; apply H0.
      clear H H0.
      unfold AxmEq5 in |- *.
      cut
        (forall a b : Terms L (arity L (inr (Relations L) f)),
            interpTermsVector value _ a = interpTermsVector value _ b ->
            interpFormula value (nnHelp (equal L (apply L f a) (apply L f b)))).
      * assert
          (H: forall A,
              (forall a b : Terms L (arity L (inr (Relations L) f)),
                  interpTermsVector value (arity L (inr (Relations L) f)) a =
                    interpTermsVector value (arity L (inr (Relations L) f)) b ->
                  interpFormula value (nnHelp (A a b))) ->
              interpFormula value
                (nnHelp
                   (nat_rec (fun _ : nat => Formula L)
                      (prod_rec
                         (fun
                             _ : Terms L (arity L (inr (Relations L) f)) *
                                   Terms L (arity L (inr (Relations L) f)) => 
                             Formula L)
                         (fun a b : Terms L (arity L (inr (Relations L) f)) => A a b)
                         (nVars L (arity L (inr (Relations L) f))))
                      (fun (n : nat) (Hrecn : Formula L) =>
                         impH (equal L (var L (n + n)) (var L (S (n + n)))) Hrecn)
                      (arity L (inr (Relations L) f))))).
        { generalize (arity L (inr (Relations L) f)).
          simple induction n.
          - simpl; intros A H; auto. 
          - intros n0 H A H0; simpl.
            induction (nVars L n0).
            simpl in H |- *.
            intros H1; 
              apply  (H
                        (fun x y : Terms L n0 =>
                           A (Tcons L n0 (var L (n0 + n0)) x) 
                             (Tcons L n0 (var L (S (n0 + n0))) y))).
            intros a0 b0 H2; apply H0.
            simpl; rewrite H1.
            now rewrite H2.
        }
        apply (H (fun a b => equal L (apply L f a) (apply L f b))).
      * simpl; generalize (func M f).
        generalize (arity L (inr (Relations L) f)).
        intros n n0 a b H.
        induction a as [| n t a Hreca].
        -- assert (H0: b = Tnil L) by ( symmetry; apply nilTerms). 
           now rewrite H0.
        -- induction (consTerms L n b) as [x p];
           induction x as (a0, b0).
           simpl in p; rewrite <- p; rewrite <- p in H.
           simpl in H.
           inversion H.
           simpl; rewrite H1.
           apply Hreca.
           apply (inj_right_pair2 _ eq_nat_dec _ _ _ _ H2).
  - auto.
Qed.

Lemma ModelConsistent (value : nat -> U M):
  (forall f : Formula L,
      mem _ T f -> interpFormula value (nnTranslate f)) ->
  Consistent L T. 
Proof.
  intros H; unfold Consistent; exists (notH (equal L (var  L 0) (var L 0))).
  intros H0; assert
               (H1: interpFormula value
                      (nnTranslate (notH  (equal L (var L 0) (var L 0))))).
  { apply preserveValue.
    assumption.
    auto.
  }
  apply H1; simpl; auto. 
Qed.

End Consistent_Theory.

End Model_Theory.

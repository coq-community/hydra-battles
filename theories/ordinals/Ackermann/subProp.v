Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Peano_dec.
Require Import ListExt.
Require Import Arith.

Require Import folProof.
Require Import folLogic.
Require Import folProp.
Require Import folReplace.

Section Substitution_Properties.

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
Let SysPrf := SysPrf L.

Lemma freeVarSubTerm1 (t : Term):
  forall  (v : nat) (s : Term) (x : nat),
    In x (freeVarTerm L t) ->
    v <> x -> In x (freeVarTerm L (substituteTerm L t v s)).
Proof.
  elim t using
    Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             forall (v : nat) (s : Term) (x : nat),
               In x (freeVarTerms L n ts) ->
               v <> x -> In x (freeVarTerms L n (substituteTerms L n ts v s))).
  -  intros n v s x H H0; simpl.
     induction (eq_nat_dec v n) as [? | ?].
     + destruct H0; simpl in H; induction H as [H| H].
       * congruence.
       * contradiction.
     + assumption.
  - intros f t0 H v s x H0 H1; simpl in |- *.
    unfold freeVarTerm; apply H; auto.
  - intros; auto.
  - intros n t0 H t1 H0 v s x H1 H2; unfold freeVarTerms in H1.
    induction (in_app_or _ _ _ H1);
      unfold freeVarTerms; simpl; apply in_or_app; auto.
Qed.

Lemma freeVarSubTerms1 (n : nat) (ts : Terms n) (v : nat) (s : Term) (x : nat):
  In x (freeVarTerms L n ts) ->
  v <> x -> In x (freeVarTerms L n (substituteTerms L n ts v s)).
Proof.
  intros H H0; induction ts as [| n t ts Hrects].
  - auto.
  - unfold freeVarTerms in H; fold (freeVarTerm L t) in H.
    fold (freeVarTerms L _ ts) in H.
    unfold freeVarTerms; simpl;
      fold (freeVarTerm L (substituteTerm L t v s));
      fold (freeVarTerms L n (substituteTerms L n ts v s));
      apply in_or_app.
    induction (in_app_or _ _ _ H).
    + left; apply freeVarSubTerm1; auto.
    + auto.
Qed.

Lemma freeVarSubFormula1 (f : Formula):
 forall  (v : nat) (s : Term) (x : nat),
 v <> x ->
 In x (freeVarFormula L f) ->
 In x (freeVarFormula L (substituteFormula L f v s)).
Proof.
  elim f using Formula_depth_ind2. 
  - intros t t0 v s x H H0; rewrite subFormulaEqual.
    simpl in H0 |- *; induction (in_app_or _ _ _ H0) as [H1 | ?].
    + apply in_or_app; left; apply freeVarSubTerm1; auto.
    + apply in_or_app; right; apply freeVarSubTerm1; auto.
  - intros r t  v s x H H0; simpl in H0; rewrite subFormulaRelation.
    simpl; apply freeVarSubTerms1; auto.
  - intros f0 H f1 H0 v s x H1 H2; rewrite subFormulaImp.
    simpl in H2 |- *; destruct (in_app_or _ _ _ H2);  apply in_or_app; auto.
    - intros f0 H v s x H0 H1; rewrite subFormulaNot.
      simpl; apply H; auto.
    - intros v a H v0 s x H0 H1; rewrite subFormulaForall; 
        induction (eq_nat_dec v v0) as [? | b].
      + auto.
      + induction (In_dec eq_nat_dec v (freeVarTerm L s)) as [a0 | ?].
        * set (nv := newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a)).
          simpl; apply In_list_remove3.
          -- apply H.
             ++ unfold lt_depth; rewrite subFormulaDepth.
                simpl; apply Nat.lt_succ_diag_r .
             ++ auto.
             ++ apply H.
                ** unfold lt_depth; simpl; apply Nat.lt_succ_diag_r .
                ** intro H2; simpl in H1.
                   elim (In_list_remove2 _ eq_nat_dec _ _ _ H1); auto.
                ** eapply In_list_remove1; apply H1.
          --  intro H2; elim (newVar1 (v0 :: freeVarTerm L s ++ freeVarFormula L a)).
              fold nv; simpl; right; apply in_or_app; right; eapply In_list_remove1.
              rewrite <- H2; apply H1.
        * simpl; apply In_list_remove3.
          -- apply H; auto.
             ++ unfold lt_depth; simpl; apply Nat.lt_succ_diag_r .
             ++ eapply In_list_remove1; apply H1.
          -- intro H2; now elim (In_list_remove2 _ eq_nat_dec _ _ _ H1).
Qed.

Lemma freeVarSubTerm2 (t : Term) :
  forall  (v : nat) (s : Term) (x : nat),
    In x (freeVarTerm L s) ->
    In v (freeVarTerm L t) -> In x (freeVarTerm L (substituteTerm L t v s)).
Proof.
  elim t using Term_Terms_ind 
    with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             forall (v : nat) (s : Term) (x : nat),
               In x (freeVarTerm L s) ->
               In v (freeVarTerms L n ts) ->
               In x (freeVarTerms L n (substituteTerms L n ts v s))).
  - intros n v s x H H0; simpl; induction (eq_nat_dec v n) as [? | b].
    + assumption.
    +  elim b; induction H0 as [H0| H0].
          * auto.
          * contradiction.
  - intros f t0 H v s x H0 H1; simpl; unfold freeVarTerm;
      fold
        (freeVarTerms L _ (substituteTerms L (arity L (inr (Relations L) f)) t0 v s)).
    apply H; auto.
  - intros v s x H H0; auto.
  - intros n t0 H t1 H0 v s x H1 H2; simpl; unfold freeVarTerms in H2;
    fold (freeVarTerm L t0) in H2; fold (freeVarTerms L n t1) in H2.
    unfold freeVarTerms; fold (freeVarTerm L (substituteTerm L t0 v s));
      fold (freeVarTerms L n (substituteTerms L n t1 v s));
      apply in_or_app.
    induction (in_app_or _ _ _ H2).
    + left; apply H; auto.
    + right; apply H0; auto.
Qed.

Lemma freeVarSubTerms2 (n : nat) (ts : Terms n) (v : nat) (s : Term) (x : nat):
 In x (freeVarTerm L s) ->
 In v (freeVarTerms L n ts) ->
 In x (freeVarTerms L n (substituteTerms L n ts v s)).
Proof.
  intros H H0; induction ts as [| n t ts Hrects].
  - contradiction H0. 
  - simpl; unfold freeVarTerms in H0; fold (freeVarTerm L t) in H0.
    fold (freeVarTerms L n ts) in H0; unfold freeVarTerms.
    fold (freeVarTerm L (substituteTerm L t v s));
      fold (freeVarTerms L n (substituteTerms L n ts v s));
      apply in_or_app.
    destruct (in_app_or _ _ _ H0).
    + left; apply freeVarSubTerm2; auto.
    + right; apply Hrects; auto.
Qed.

Lemma freeVarSubFormula2 (f : Formula):
  forall  (v : nat) (s : Term) (x : nat),
    In x (freeVarTerm L s) ->
    In v (freeVarFormula L f) ->
    In x (freeVarFormula L (substituteFormula L f v s)).
Proof.
  elim f using Formula_depth_ind2.  
  - intros t t0 v s x H H0; rewrite subFormulaEqual.
    simpl in H0 |- *; apply in_or_app.
    induction (in_app_or _ _ _ H0) as [? | ?].
    + left; apply freeVarSubTerm2; auto.
    + right; apply freeVarSubTerm2; auto.
  - intros r t v s x H H0; rewrite subFormulaRelation; simpl in H0 |- *.
    apply freeVarSubTerms2; auto.
  - intros f0 H f1 H0 v s x H1 H2; rewrite subFormulaImp.
    simpl in H2 |- *; apply in_or_app.
    induction (in_app_or _ _ _ H2).
    + left; apply H; auto.
    + right; apply H0; auto.
  - intros f0 H v s x H0 H1; rewrite subFormulaNot; simpl; apply H; auto.
  - intros v a H v0 s x H0 H1; rewrite subFormulaForall.
    induction (eq_nat_dec v v0).
    + simpl in H1; elim (In_list_remove2 _ eq_nat_dec _ _ _ H1); auto. 
    + induction (In_dec eq_nat_dec v (freeVarTerm L s)) as [a0 | b0].
      * set (nv := newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a)).
        simpl; apply In_list_remove3.
        -- apply H.
           ++ unfold lt_depth; rewrite subFormulaDepth; simpl;
                apply Nat.lt_succ_diag_r.
           ++ assumption.
           ++ apply freeVarSubFormula1. 
              ** assumption.
              ** simpl in H1; eapply In_list_remove1.
                 apply H1.
        -- intro H2; 
             elim (newVar1 (v0 :: freeVarTerm L s ++ freeVarFormula L a)).
           fold nv; simpl; right.
           apply in_or_app.
           rewrite <- H2; auto.
      * simpl; eapply In_list_remove3.
        -- apply H.
           apply depthForall; auto.
           auto. 
           eapply In_list_remove1.
           simpl in H1; apply H1.
        -- unfold not in |- *; intros.  
           elim b0; now rewrite H2 in H0.
Qed.

Lemma freeVarSubTerm3  (t : Term):
  forall (v : nat) (s : Term) (x : nat),
    In x (freeVarTerm L (substituteTerm L t v s)) ->
    In x (list_remove _ eq_nat_dec v (freeVarTerm L t)) \/
      In x (freeVarTerm L s).
Proof.
  elim t using
    Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             forall (v : nat) (s : Term) (x : nat),
               In x (freeVarTerms L n (substituteTerms L n ts v s)) ->
               In x (list_remove _ eq_nat_dec v (freeVarTerms L n ts)) \/
                 In x (freeVarTerm L s)). 
  - intros n v s x H; simpl in H.
    induction (eq_nat_dec v n) as [a | b].
    + now right.
    + left; apply In_list_remove3.
      * assumption.
      *  intro H0; rewrite H0 in H; destruct H as [H| H].
         -- congruence.
         -- contradiction H.
  - intros f t0 H v s x H0; simpl in H0; induction (H _ _ _ H0); auto.
  - auto.
  - intros n t0 H t1 H0 v s x H1; simpl in H1;
      unfold freeVarTerms in H1;
      fold (freeVarTerm L (substituteTerm L t0 v s)) in H1;
      fold (freeVarTerms L n (substituteTerms L n t1 v s)) in H1.
    destruct (in_app_or _ _ _ H1) as [H2 | H2].
    + induction (H _ _ _ H2) as [H3 | H3].
      * left; apply In_list_remove3.
        -- unfold freeVarTerms; apply in_or_app; left.
           eapply In_list_remove1; apply H3.
        --  eapply In_list_remove2; apply H3.
      *  auto.
    + induction (H0 _ _ _ H2) as [H3 | H3].
      * left; apply In_list_remove3.
        -- unfold freeVarTerms; fold (freeVarTerm L t0);
             fold (freeVarTerms L n t1); apply in_or_app.
           right; eapply In_list_remove1; apply H3.
        -- eapply In_list_remove2; apply H3.
      * auto.
Qed.

Lemma freeVarSubTerms3 (n : nat) (ts : fol.Terms L n) (v : nat) (s : Term) 
  (x : nat):
 In x (freeVarTerms L n (substituteTerms L n ts v s)) ->
 In x (list_remove _ eq_nat_dec v (freeVarTerms L n ts)) \/
 In x (freeVarTerm L s).
Proof.
  intros H; induction ts as [| n t ts Hrects].
  - left; apply H. 
  - simpl in H; unfold freeVarTerms in H;
      fold (freeVarTerm L (substituteTerm L t v s)) in H;
      fold (freeVarTerms L n (substituteTerms L n ts v s)) in H;
      induction (in_app_or _ _ _ H) as [H0 | H0].
    + induction (freeVarSubTerm3 _ _ _ _ H0) as [H1 | H1].
      * left.
        apply In_list_remove3.
        -- unfold freeVarTerms; fold (freeVarTerm L t);
             fold (freeVarTerms L n ts); apply in_or_app.
           left; eapply In_list_remove1; apply H1.
        -- eapply In_list_remove2; apply H1.
      * now right.
    + induction (Hrects H0) as [H1 | H1].
      * left; apply In_list_remove3.
        -- unfold freeVarTerms; fold (freeVarTerm L t);
             fold (freeVarTerms L n ts); apply in_or_app; right.
           eapply In_list_remove1; apply H1.
        -- eapply In_list_remove2; apply H1.
      * now right.
Qed.

Lemma freeVarSubFormula3  (f : Formula):
 forall (v : nat) (s : Term) (x : nat),
 In x (freeVarFormula L (substituteFormula L f v s)) ->
 In x (list_remove _ eq_nat_dec v (freeVarFormula L f)) \/
 In x (freeVarTerm L s).
Proof.
  elim f using Formula_depth_ind2. 
  - intros t t0 v s x H; rewrite subFormulaEqual in H.
    simpl in H; induction (in_app_or _ _ _ H) as [H0 | H0].
    + simpl;induction (freeVarSubTerm3 _ _ _ _ H0) as [H1 | H1].
      * left; apply In_list_remove3.
        -- apply in_or_app; left; eapply In_list_remove1; apply H1.
        -- eapply In_list_remove2; apply H1.
      * now right.
    + simpl; induction (freeVarSubTerm3 _ _ _ _ H0) as [H1 | H1].
      * left; apply In_list_remove3.
        -- apply in_or_app; right; eapply In_list_remove1, H1.
        -- eapply In_list_remove2, H1.
      * now right. 
  - intros r t v s x H; rewrite subFormulaRelation in H; simpl in H |- *.
    eapply freeVarSubTerms3, H.
  - intros f0 H f1 H0 v s x H1;  rewrite subFormulaImp in H1.
    simpl in H1 |- *; induction (in_app_or _ _ _ H1) as [H2 | H2].
    + induction (H _ _ _ H2) as [H3 | H3]. 
      * left; apply In_list_remove3.
        -- apply in_or_app; left; eapply In_list_remove1, H3.
        -- eapply In_list_remove2, H3. 
      * now right.
    + induction (H0 _ _ _ H2) as [H3 | H3].
      * left; apply In_list_remove3.
        -- apply in_or_app; right; eapply In_list_remove1, H3.
        -- eapply In_list_remove2, H3. 
      * now right.
  - intros f0 H v s x H0; rewrite subFormulaNot in H0.
    eapply H, H0.
  - intros  v a H v0 s x H0; rewrite subFormulaForall in H0.
    induction (eq_nat_dec v v0) as [a0 | ?].
    + left; apply In_list_remove3.
      * apply H0.
      * eapply In_list_remove2; rewrite <- a0; apply H0.
    + induction (In_dec eq_nat_dec v (freeVarTerm L s)) as [a0 | ?].
      * set (nv := newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a)).
        induction (eq_nat_dec x v) as [a1 | ?].
        -- rewrite a1;  now right.
        -- assert
            (H1: lt_depth L (substituteFormula L a v (fol.var L nv))
                   (fol.forallH L v a)).
           { unfold lt_depth; rewrite subFormulaDepth.
             apply depthForall.
           }
           assert
             (H2: In x
                    (freeVarFormula L
                       (substituteFormula L 
                          (substituteFormula L a v (fol.var L nv)) v0 s))).
           { eapply In_list_remove1; apply H0. }
           assert (H3: x <> nv).
           { eapply In_list_remove2; apply H0. }
           clear H0.
           induction (H _ H1 _ _ _ H2) as [H0 | H0].
           ++ assert (H4: lt_depth L a (fol.forallH L v a)) by
              apply depthForall.
              assert (H5: In x (freeVarFormula L
                              (substituteFormula L a v (fol.var L nv)))).
              { eapply In_list_remove1; apply H0. }
              assert (H6: x <> v0).
              { eapply In_list_remove2, H0. }
              clear H0.
              induction (H _ H4 _ _ _ H5).
              ** left; apply In_list_remove3.
                 apply H0.
                 assumption.
              ** elim H3; simpl in H0; induction H0 as [H0| H0].
                 auto.
                 contradiction.
           ++ now right.
      * assert (H1: lt_depth L a (fol.forallH L v a)) 
          by apply depthForall.
        simpl in H0.
        assert (H2: In x (freeVarFormula L (substituteFormula L a v0 s))).
        { eapply In_list_remove1, H0. }
        induction (H _ H1 _ _ _ H2) as [H3 | H3].
        -- left; apply In_list_remove3.
           simpl; apply In_list_remove3.  
           ++ eapply In_list_remove1, H3.
           ++ eapply In_list_remove2, H0.
           ++ eapply In_list_remove2, H3.
        -- now right.
Qed.

Lemma freeVarSubTerm4 (t : Term) :
 forall  (v : nat) (s : Term) (x : nat),
 In x (freeVarTerm L (substituteTerm L t v s)) ->
 ~ In v (freeVarTerm L t) -> In x (freeVarTerm L t).
Proof.
  elim t using
    Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             forall (v : nat) (s : Term) (x : nat),
               In x (freeVarTerms L n (substituteTerms L n ts v s)) ->
               ~ In v (freeVarTerms L n ts) -> In x (freeVarTerms L n ts)).
  - intros n v s x H H0; simpl in H |- *.
    induction (eq_nat_dec v n) as [a | ?].
    + elim H0; rewrite a; simpl; now left. 
    + apply H.
  - intros f t0 H v s x  H0 H1; simpl in H0; eapply H.
    + apply H0.
    + apply H1.
  - intros; assumption.
  - intros n t0 H t1 H0 v s x H1 H2; simpl in H1.
    unfold freeVarTerms in H1;
    fold (freeVarTerm L (substituteTerm L t0 v s)) in H1;
    fold (freeVarTerms L n (substituteTerms L n t1 v s)) in H1;
    unfold freeVarTerms ;
      fold (freeVarTerm L t0); fold (freeVarTerms L n t1).
    induction (in_app_or _ _ _ H1) as [H3 | H3].
    + apply in_or_app; left; eapply H.
      * apply H3.
      * intro H4; elim H2.
        unfold freeVarTerms; fold (freeVarTerm L t0);
          fold (freeVarTerms L n t1); apply in_or_app.
        now left. 
    + apply in_or_app; right; eapply H0.
      * apply H3.
      *  intro H4; elim H2.
         unfold freeVarTerms; fold (freeVarTerm L t0); 
           fold (freeVarTerms L n t1); apply in_or_app; now right.
Qed.

Lemma freeVarSubTerms4 (n : nat) (ts : Terms n) (v : nat)
  (s : Term) (x : nat):
  In x (freeVarTerms L n (substituteTerms L n ts v s)) ->
  ~ In v (freeVarTerms L n ts) -> In x (freeVarTerms L n ts).
Proof.
  intros H H0; induction ts as [| n t ts Hrects].
  - auto.
  - simpl in H; unfold freeVarTerms in H;
      fold (freeVarTerm L (substituteTerm L t v s)) in H;
      fold (freeVarTerms L n (substituteTerms L n ts v s)) in H.
    unfold freeVarTerms; fold (freeVarTerm L t); fold (freeVarTerms L n ts).
    induction (in_app_or _ _ _ H) as [H1 | H1].
    + apply in_or_app; left; eapply freeVarSubTerm4.
      * apply H1.
      * intro H2; elim H0.
        unfold freeVarTerms; fold (freeVarTerm L t);
          fold (freeVarTerms L n ts); apply in_or_app; now left.
    + apply in_or_app; right; eapply Hrects. 
      * apply H1.
      * intro H2; elim H0; unfold freeVarTerms;
          fold (freeVarTerm L t); fold (freeVarTerms L n ts).
        apply in_or_app; now right.
Qed.

Lemma freeVarSubFormula4  (f : Formula) :
 forall (v : nat) (s : Term) (x : nat),
 In x (freeVarFormula L (substituteFormula L f v s)) ->
 ~ In v (freeVarFormula L f) -> In x (freeVarFormula L f).
Proof.
  elim f using Formula_depth_ind2.
  - intros t t0 v s x H H0; rewrite subFormulaEqual in H.
    simpl in H, H0 |- *; apply in_or_app.
    induction (in_app_or _ _ _ H) as [H1 | H1].
    + left; eapply freeVarSubTerm4.
      * apply H1.
      * intro H2; elim H0.
        apply in_or_app; now left. 
    + right; eapply freeVarSubTerm4.
      * apply H1; intro H2; elim H0; apply in_or_app; now right.
      *   intro H2; apply H0; apply in_or_app; now right. 
  - intros r t v s x H H0; rewrite subFormulaRelation in H.
    simpl in H |- *; eapply freeVarSubTerms4; [apply H | assumption].
  -  intros f0 H f1 H0 v s  x H1 H2; rewrite subFormulaImp in H1;
       simpl in H2, H1  |- *;  apply in_or_app.
     induction (in_app_or _ _ _ H1) as [H3 | H3].
     + left; eapply H. 
       * apply H3.
       * intro H4; elim H2; apply in_or_app; now left. 
     + right; eapply H0.  
       * apply H3.
       * intro H4; elim H2; apply in_or_app; now right.
  - intros f0 H v s x H0 H1; rewrite subFormulaNot in H0.
    simpl; eapply H.
    + apply H0.
    + apply H1.
  - intros v a H v0 s x H0 H1; simpl in |- *.
    simpl in H1; rewrite subFormulaForall in H0.
    induction (eq_nat_dec v v0) as [a0 | ?]. 
    + apply H0.
    + induction (In_dec eq_nat_dec v (freeVarTerm L s)) as [a0 | ?].
      * set (nv := newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a)).
        simpl in H0.
        assert
          (H2: In x
             (freeVarFormula L
                (substituteFormula L (substituteFormula L a v (fol.var L nv)) v0 s))).
        { eapply In_list_remove1; apply H0. } 
        assert (H3: In x (freeVarFormula L (substituteFormula L a v (fol.var L nv)))).
        { eapply H.
          - unfold lt_depth; rewrite subFormulaDepth.
            apply depthForall.
          - apply H2.
          - intros H3; induction (freeVarSubFormula3 _ _ _ _ H3).
            + auto.
            + elim (newVar1 (v0 :: freeVarTerm L s ++ freeVarFormula L a)).
              fold nv; induction H4 as [H4| H4].
              * rewrite H4; simpl; now left.  
              * elim H4.
        } 
        induction (freeVarSubFormula3 _ _ _ _ H3). 
       -- assumption. 
       -- induction H4 as [H4| H4].
          ++ elim (In_list_remove2 _ _ _ _ _ H0); now subst nv.
          ++ elim H4.
      * simpl in H0; apply In_list_remove3.
        -- eapply H.
           ++ apply depthForall.
           ++ eapply In_list_remove1, H0.
           ++ intro H2; elim H1.
               ** apply In_list_remove3; auto.
        -- eapply In_list_remove2, H0.
Qed.

Lemma subTermNil (t : Term) (v : nat) (s : Term):
 ~ In v (freeVarTerm L t) -> substituteTerm L t v s = t.
Proof.
  elim t using
    Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             ~ In v (freeVarTerms L n ts) -> substituteTerms L n ts v s = ts).
  - intros n H; simpl in H; rewrite subTermVar2.
    + reflexivity.
    + intro H0; apply H; left; auto. 
  - intros f t0 H H0; simpl; rewrite H.
    + reflexivity.
    + apply H0.
  - reflexivity. 
  - intros n t0 H t1 H0 H1; simpl; unfold freeVarTerms in H1.
    rewrite H0.
    + rewrite H.
      * reflexivity.
      *  intros H2; elim H1; apply in_or_app. auto. 
    +  intro H2; elim H1; apply in_or_app; now right. 
Qed.
 
Lemma subTermTrans  (t : Term) (v1 v2 : nat) (s : Term):
 ~ In v2 (list_remove _ eq_nat_dec v1 (freeVarTerm L t)) ->
 substituteTerm L (substituteTerm L t v1 (var v2)) v2 s =
 substituteTerm L t v1 s.
Proof.
  elim t using
    Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             ~ In v2 (list_remove _ eq_nat_dec v1 (freeVarTerms L n ts)) ->
             substituteTerms L n (substituteTerms L n ts v1 (var v2)) v2 s =
               substituteTerms L n ts v1 s).
  - intros n H; simpl; induction (eq_nat_dec v1 n) as [? | b].
    + now rewrite (subTermVar1 L).
    + rewrite (subTermVar2 L).
      * reflexivity.
      * simpl in H; induction (eq_nat_dec n v1).
        -- elim b; auto.
        -- intro H0; elim H. simpl; auto. 
  - intros f t0 H H0; simpl; rewrite H.
    + reflexivity.
    + apply H0.
  - auto.
  - intros n t0 H t1 H0 H1; simpl; unfold freeVarTerms in H1.
    rewrite H0.
    * rewrite H. 
      -- reflexivity.
      --  intros H2; elim H1; apply In_list_remove3.
          ++ apply in_or_app; left.
             eapply In_list_remove1, H2.
          ++ eapply In_list_remove2, H2. 
    * intro H2; elim H1; apply In_list_remove3.
      -- apply in_or_app; right; eapply In_list_remove1, H2.
      -- eapply In_list_remove2, H2.
Qed.

Lemma subTermExch  (t : Term) (v1 v2 : nat) (s1 s2 : Term):
 v1 <> v2 ->
 ~ In v2 (freeVarTerm L s1) ->
 ~ In v1 (freeVarTerm L s2) ->
 substituteTerm L (substituteTerm L t v1 s1) v2 s2 =
 substituteTerm L (substituteTerm L t v2 s2) v1 s1.
Proof.
  elim t using
    Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             v1 <> v2 ->
             ~ In v2 (freeVarTerm L s1) ->
             ~ In v1 (freeVarTerm L s2) ->
             substituteTerms L n (substituteTerms L n ts v1 s1) v2 s2 =
               substituteTerms L n (substituteTerms L n ts v2 s2) v1 s1).
 - intros n H H0 H1; simpl; induction (eq_nat_dec v1 n) as [a | ?].
   + induction (eq_nat_dec v2 n).
     * elim H; congruence. 
     * rewrite a; rewrite subTermVar1.
       rewrite subTermNil; auto.
   + induction (eq_nat_dec v2 n) as [a| ?].
     * rewrite a; rewrite subTermVar1.
       rewrite subTermNil; auto.
     * now repeat rewrite subTermVar2.
 -  intros f t0 H H0 H1 H2; simpl; rewrite H; auto.
 - reflexivity.
 - intros n t0 H t1 H0 H1 H2 H3; simpl; rewrite H; auto.
   now rewrite H0.
Qed.

Lemma subTermsNil :
 forall (n : nat) (ts : Terms n) (v : nat) (s : Term),
 ~ In v (freeVarTerms L n ts) -> substituteTerms L n ts v s = ts.
Proof.
intros.
induction ts as [| n t ts Hrects].
auto.
simpl in |- *.
unfold freeVarTerms in H.
rewrite Hrects.
rewrite subTermNil.
reflexivity.
unfold not in |- *; intros; elim H.
apply in_or_app.
auto.
unfold not in |- *; intros; elim H.
apply in_or_app.
auto.
Qed.

Lemma subTermsTrans :
 forall (n : nat) (ts : Terms n) (v1 v2 : nat) (s : Term),
 ~ In v2 (list_remove _ eq_nat_dec v1 (freeVarTerms L n ts)) ->
 substituteTerms L n (substituteTerms L n ts v1 (var v2)) v2 s =
 substituteTerms L n ts v1 s.
Proof.
intros.
induction ts as [| n t ts Hrects].
auto.
simpl in |- *.
unfold freeVarTerms in H.
rewrite Hrects.
rewrite subTermTrans.
reflexivity.
unfold not in |- *; intros; elim H.
apply In_list_remove3.
apply in_or_app.
left.
eapply In_list_remove1.
apply H0.
eapply In_list_remove2.
apply H0.
unfold not in |- *; intros; elim H.
apply In_list_remove3.
apply in_or_app.
right.
eapply In_list_remove1.
apply H0.
eapply In_list_remove2.
apply H0.
Qed.

Lemma subTermsExch :
 forall (n : nat) (ts : Terms n) (v1 v2 : nat) (s1 s2 : Term),
 v1 <> v2 ->
 ~ In v2 (freeVarTerm L s1) ->
 ~ In v1 (freeVarTerm L s2) ->
 substituteTerms L n (substituteTerms L n ts v1 s1) v2 s2 =
 substituteTerms L n (substituteTerms L n ts v2 s2) v1 s1.
Proof.
intros.
induction ts as [| n t ts Hrects].
auto.
simpl in |- *.
rewrite Hrects.
rewrite subTermExch; auto.
Qed.

Remark subFormulaNTEHelp :
 forall (f g : Formula) (v : nat) (s : Term),
 SysPrf (Ensembles.Add _ (Empty_set Formula) f) g ->
 SysPrf (Ensembles.Add _ (Empty_set Formula) (substituteFormula L f v s))
   (substituteFormula L g v s).
Proof.
intros.
apply (impE L) with (substituteFormula L f v s).
apply (sysWeaken L).
rewrite <- (subFormulaImp L).
apply forallE.
apply forallI.
apply (notInFreeVarSys L).
apply (impI L).
apply H.
apply Axm; right; constructor.
Qed.

Remark subFormulaNTE :
 forall (f : Formula) (T : System),
 (forall (v : nat) (s : Term),
  ~ In v (freeVarFormula L f) ->
  SysPrf T (iffH (substituteFormula L f v s) f)) /\
 (forall (v1 v2 : nat) (s : Term),
  ~ In v2 (list_remove _ eq_nat_dec v1 (freeVarFormula L f)) ->
  SysPrf T
    (iffH (substituteFormula L (substituteFormula L f v1 (var v2)) v2 s)
       (substituteFormula L f v1 s))) /\
 (forall (v1 v2 : nat) (s1 s2 : Term),
  v1 <> v2 ->
  ~ In v2 (freeVarTerm L s1) ->
  ~ In v1 (freeVarTerm L s2) ->
  SysPrf T
    (iffH (substituteFormula L (substituteFormula L f v1 s1) v2 s2)
       (substituteFormula L (substituteFormula L f v2 s2) v1 s1))).
Proof.
intro.
elim f using Formula_depth_ind2; (intros; split; [ idtac | split ]); intros.
rewrite (subFormulaEqual L).
simpl in H.
repeat rewrite subTermNil.
apply (iffRefl L).
unfold not in |- *; intros; elim H; apply in_or_app; auto.
unfold not in |- *; intros; elim H; apply in_or_app; auto.
repeat rewrite (subFormulaEqual L).
simpl in H.
repeat rewrite subTermTrans.
apply (iffRefl L).
unfold not in |- *; intros; elim H.
apply In_list_remove3.
apply in_or_app.
right.
eapply In_list_remove1.
apply H0.
eapply In_list_remove2.
apply H0.
unfold not in |- *; intros; elim H.
apply In_list_remove3.
apply in_or_app.
left.
eapply In_list_remove1.
apply H0.
eapply In_list_remove2.
apply H0.
repeat rewrite (subFormulaEqual L).
rewrite (subTermExch t); auto.
rewrite (subTermExch t0); auto.
apply (iffRefl L).
rewrite (subFormulaRelation L).
rewrite subTermsNil.
apply (iffRefl L).
assumption.
repeat rewrite (subFormulaRelation L).
rewrite subTermsTrans.
apply (iffRefl L).
assumption.
repeat rewrite (subFormulaRelation L).
rewrite subTermsExch; auto.
apply (iffRefl L).
decompose record (H T). 
decompose record (H0 T).
rewrite (subFormulaImp L).
simpl in H1.
apply (reduceImp L).
apply H2.
unfold not in |- *; intros; elim H1.
apply in_or_app.
auto.
apply H3.
unfold not in |- *; intros; elim H1.
apply in_or_app.
auto.
decompose record (H T). 
decompose record (H0 T).
repeat rewrite (subFormulaImp L).
simpl in H1.
apply (reduceImp L).
apply H4.
unfold not in |- *; intros; elim H1.
apply In_list_remove3.
apply in_or_app.
left.
eapply In_list_remove1.
apply H6.
eapply In_list_remove2.
apply H6.
apply H7.
unfold not in |- *; intros; elim H1.
apply In_list_remove3.
apply in_or_app.
right.
eapply In_list_remove1.
apply H6.
eapply In_list_remove2.
apply H6.
decompose record (H T). 
decompose record (H0 T).
repeat rewrite (subFormulaImp L).
apply (reduceImp L).
apply H7; auto.
apply H10; auto.
decompose record (H T).
rewrite (subFormulaNot L).
apply (reduceNot L).
apply H1.
auto.
decompose record (H T).
repeat rewrite (subFormulaNot L).
apply (reduceNot L).
apply H3.
auto.
decompose record (H T).
repeat rewrite (subFormulaNot L).
apply (reduceNot L).
apply H6; auto.
decompose record (subFormulaForall2 L a v v0 s).
rewrite H5.
clear H5.
induction (eq_nat_dec v v0).
apply (iffRefl L).
eapply (sysExtend L) with (Empty_set Formula).
unfold Included in |- *.
intros.
induction H4.
apply (iffI L).
apply (impI L).
apply (forallI L).
unfold not in |- *; intros.
induction H4 as (x0, H4); induction H4 as (H4, H5).
induction H5 as [x0 H5| x0 H5]; [ induction H5 | induction H5 ].
assert
 (In v
    (freeVarFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x)) v0 s))).
eapply In_list_remove1.
apply H4.
assert (In v (freeVarFormula L (substituteFormula L a v (fol.var L x)))).
eapply (freeVarSubFormula4 _ _ _ _ H5).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ H6).
auto.
induction H7 as [H7| H7].
auto.
auto.
induction (freeVarSubFormula3 _ _ _ _ H6).
elim (In_list_remove2 _ _ _ _ _ H7).
auto.
induction H7 as [H7| H7].
elim (In_list_remove2 _ _ _ _ _ H4).
auto.
auto.
assert (lt_depth L a (fol.forallH L v a)).
apply depthForall.
decompose record (H _ H4 (Empty_set Formula)).
set (A1 := substituteFormula L a v (fol.var L x)) in *.
rewrite <- (subFormulaId _ a v).
apply
 impE
  with
    (substituteFormula L (substituteFormula L a v (fol.var L x)) x (var v)).
apply sysWeaken.
apply (iffE1 L).
induction (eq_nat_dec v x).
rewrite a0.
repeat rewrite (subFormulaId L).
apply (iffRefl L).
apply H7.
unfold not in |- *; intros.
elim H3.
assumption.
auto.
fold A1 in |- *.
apply impE with (substituteFormula L (substituteFormula L A1 x (var v)) v0 s).
apply sysWeaken.
apply (iffE1 L).
assert (lt_depth L (substituteFormula L A1 x (var v)) (fol.forallH L v a)).
unfold lt_depth, A1 in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H6 (Empty_set Formula)).
apply H9.
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ H10).
assert (In v0 (freeVarFormula L A1)).
eapply In_list_remove1.
apply H13.
induction (freeVarSubFormula3 _ _ _ _ H14).
elim H0.
apply H15.
induction H15 as [H15| H15].
auto.
elim H15.
induction H13 as [H13| H13].
auto.
contradiction.
assert (lt_depth L A1 (fol.forallH L v a)).
unfold lt_depth, A1 in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H6 (Empty_set Formula)).
apply impE with (substituteFormula L (substituteFormula L A1 v0 s) x (var v)).
apply sysWeaken.
apply (iffE1 L).
apply H12.
auto.
auto.
unfold not in |- *; intros.
induction H10 as [H10| H10].
auto.
contradiction.
apply forallE.
apply Axm; right; constructor.
apply (impI L).
apply forallI.
unfold not in |- *; intros.
induction H4 as (x0, H4); induction H4 as (H4, H5).
induction H5 as [x0 H5| x0 H5]; [ induction H5 | induction H5 ].
auto.
apply impE with (substituteFormula L a v (fol.var L x)).
apply (iffE2 L).
apply sysWeaken.
assert
 (lt_depth L (substituteFormula L a v (fol.var L x)) (fol.forallH L v a)).
unfold lt_depth in |- *.
rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H4 (Empty_set Formula)).
apply H5.
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ H6).
auto.
induction H9 as [H9| H9].
auto.
contradiction.
apply forallE.
apply Axm; right; constructor.
eapply (sysExtend L) with (Empty_set Formula).
unfold Included in |- *.
intros.
induction H1.
induction (eq_nat_dec v1 v2).
rewrite a0.
rewrite (subFormulaId L).
apply (iffRefl L).
decompose record (subFormulaForall2 L a v v1 s).
rewrite H5; clear H5.
decompose record (subFormulaForall2 L a v v1 (var v2)).
rewrite H8; clear H8.
induction (eq_nat_dec v v1).
decompose record (subFormulaForall2 L a v v2 s).
rewrite H11; clear H11.
induction (eq_nat_dec v v2).
apply (iffRefl L).
apply (iffI L).
apply (impI L).
apply forallI.
unfold not in |- *; intros.
induction H10 as (x2, H10); induction H10 as (H10, H11).
induction H11 as [x2 H11| x2 H11]; [ induction H11 | induction H11 ].
assert
 (In v
    (freeVarFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x1)) v2 s))).
eapply In_list_remove1.
apply H10.
assert (In v (freeVarFormula L (substituteFormula L a v (fol.var L x1)))).
eapply freeVarSubFormula4.
apply H11.
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ H12).
elim H0.
apply In_list_remove3; auto.
induction H13.
auto.
contradiction.
induction (freeVarSubFormula3 _ _ _ _ H12).
apply (In_list_remove2 _ _ _ _ _ H13).
auto.
induction H13 as [H13| H13].
elim (In_list_remove2 _ _ _ _ _ H10).
auto.
contradiction.
set (A1 := substituteFormula L a v (fol.var L x1)) in *.
rewrite <- (subFormulaId L a v).
apply impE with (substituteFormula L A1 x1 (var v)).
apply sysWeaken.
apply (iffE1 L).
induction (eq_nat_dec x1 v).
unfold A1 in |- *.
rewrite a1.
repeat rewrite (subFormulaId L).
apply (iffRefl L).
assert (lt_depth L a (fol.forallH L v a)).
apply depthForall.
decompose record (H _ H10 (Empty_set Formula)).
unfold A1 in |- *.
apply H13.
unfold not in |- *; intros; elim H9.
assumption.
apply
 impE with (substituteFormula L (substituteFormula L A1 x1 (var v)) v2 s).
apply sysWeaken.
apply (iffE1 L).
assert (lt_depth L (substituteFormula L A1 x1 (var v)) (fol.forallH L v a)).
unfold lt_depth, A1 in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H10 (Empty_set Formula)).
apply H11; clear H11 H13 H14.
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ H11).
assert (In v2 (freeVarFormula L A1)).
eapply In_list_remove1.
apply H12.
unfold A1 in H13.
induction (freeVarSubFormula3 _ _ _ _ H13).
elim H0.
apply In_list_remove3; auto.
induction H14 as [H14| H14]; auto.
induction H12 as [H12| H12]; auto.
apply
 impE with (substituteFormula L (substituteFormula L A1 v2 s) x1 (var v)).
apply sysWeaken.
apply (iffE1 L).
assert (lt_depth L A1 (fol.forallH L v a)).
unfold lt_depth, A1 in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H10 (Empty_set Formula)).
apply H14; clear H11 H13 H14; auto.
unfold not in |- *; intros.
induction H11 as [H11| H11]; auto.
apply forallE.
apply Axm; right; constructor.
apply (impI L).
apply forallI.
unfold not in |- *; intros.
induction H10 as (x2, H10); induction H10 as (H10, H11).
induction H11 as [x2 H11| x2 H11]; [ induction H11 | induction H11 ].
auto.
apply impE with (substituteFormula L a v (fol.var L x1)).
apply sysWeaken.
apply (iffE2 L).
assert
 (lt_depth L (substituteFormula L a v (fol.var L x1)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H10 (Empty_set _)).
apply H11; clear H11 H13 H14.
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ H11).
elim H0.
apply In_list_remove3; auto.
induction H12 as [H12| H12]; auto.
apply forallE.
apply Axm; right; constructor.
decompose record
 (subFormulaForall2 L
    (substituteFormula L (substituteFormula L a v (fol.var L x0)) v1 (var v2))
    x0 v2 s).
rewrite H11; clear H11.
induction (eq_nat_dec x0 v2).
elim H5.
rewrite a0.
simpl in |- *.
auto.
apply (iffI L).
apply (impI L).
apply forallI.
unfold not in |- *; intros.
induction H10 as (x2, H10); induction H10 as (H10, H11).
induction H11 as [x2 H11| x2 H11]; [ induction H11 | induction H11 ].
assert
 (In x
    (freeVarFormula L
       (substituteFormula L
          (substituteFormula L
             (substituteFormula L (substituteFormula L a v (fol.var L x0)) v1
                (var v2)) x0 (fol.var L x1)) v2 s))).
eapply In_list_remove1.
apply H10.
induction (freeVarSubFormula3 _ _ _ _ H11).
assert
 (In x
    (freeVarFormula L
       (substituteFormula L
          (substituteFormula L (substituteFormula L a v (fol.var L x0)) v1
             (var v2)) x0 (fol.var L x1)))).
eapply In_list_remove1.
apply H12.
induction (freeVarSubFormula3 _ _ _ _ H13).
assert
 (In x
    (freeVarFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x0)) v1
          (var v2)))).
eapply In_list_remove1; apply H14.
induction (freeVarSubFormula3 _ _ _ _ H15).
assert (In x (freeVarFormula L (substituteFormula L a v (fol.var L x0)))).
eapply In_list_remove1; apply H16.
induction (freeVarSubFormula3 _ _ _ _ H17).
apply H3.
apply H18.
elim (In_list_remove2 _ _ _ _ _ H14).
induction H18.
symmetry  in |- *.
assumption.
contradiction.
elim (In_list_remove2 _ _ _ _ _ H12).
induction H16.
symmetry  in |- *.
assumption.
contradiction.
elim (In_list_remove2 _ _ _ _ _ H10).
induction H14.
symmetry  in |- *.
assumption.
contradiction.
elim H2.
assumption.
set (A1 := substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s)
 in *.
assert (lt_depth L A1 (fol.forallH L v a)).
unfold lt_depth, A1 in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
set
 (A2 :=
  substituteFormula L
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x0)) v1
          (var v2)) x0 (fol.var L x1)) v2 s) in *.
set (x2 := newVar (v1 :: v2 :: freeVarFormula L A1 ++ freeVarFormula L A2))
 in *.
assert
 (x2prop : ~ In x2 (v1 :: v2 :: freeVarFormula L A1 ++ freeVarFormula L A2)).
unfold x2 in |- *.
apply newVar1.
unfold In in x2prop.
fold (In x2 (freeVarFormula L A1 ++ freeVarFormula L A2)) in x2prop.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L
             (substituteFormula L
                (substituteFormula L (substituteFormula L a v (fol.var L x0))
                   v1 (var v2)) x0 (fol.var L x1)) v2 s) x1 
          (var x2)) x2 (var x)).
apply sysWeaken.
apply (impI L).
rewrite <- (subFormulaId _ A1 x).
apply
 impE
  with (substituteFormula L (substituteFormula L A1 x (var x2)) x2 (var x)).
apply sysWeaken.
decompose record (H _ H10 (Empty_set Formula)).
apply (iffE1 L).
apply H13; clear H11 H13 H14.
unfold not in |- *; intros.
apply x2prop.
repeat right.
apply in_or_app.
left.
eapply In_list_remove1.
apply H11.
apply subFormulaNTEHelp.
unfold A1 in |- *.
apply
 (impE L)
  with
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x)) x
          (var x2)) v1 s).
apply (sysWeaken L).
apply (iffE1 L).
assert
 (lt_depth L (substituteFormula L a v (fol.var L x)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H11 (Empty_set Formula)).
apply H15; clear H12 H14 H15; auto.
unfold not in |- *; intros.
induction H12 as [H12| H12]; auto.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L (substituteFormula L a v (fol.var L x)) x
             (var x2)) v1 (var v2)) v2 s).
apply (sysWeaken L).
apply (iffE1 L).
assert
 (lt_depth L
    (substituteFormula L (substituteFormula L a v (fol.var L x)) x (var x2))
    (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H11 (Empty_set Formula)).
apply H14; clear H12 H14 H15; auto.
unfold not in |- *; intros.
assert
 (In v2
    (freeVarFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x)) x
          (var x2)))).
eapply In_list_remove1.
apply H12.
induction (freeVarSubFormula3 _ _ _ _ H13).
assert (In v2 (freeVarFormula L (substituteFormula L a v (fol.var L x)))).
eapply In_list_remove1.
apply H14.
induction (freeVarSubFormula3 _ _ _ _ H15).
auto.
elim H0.
apply In_list_remove3; auto.
induction H16 as [H16| H16].
elim (In_list_remove2 _ _ _ _ _ H14).
auto.
contradiction.
induction H14 as [H14| H14]; auto.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L
             (substituteFormula L (substituteFormula L a v (fol.var L x0)) v1
                (var v2)) x0 (fol.var L x1)) x1 (var x2)) v2 s).
apply (sysWeaken L).
apply (impI L).
apply subFormulaNTEHelp.
apply
 (impE L)
  with
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x0)) x0
          (var x2)) v1 (var v2)).
apply (sysWeaken L).
apply (impI L).
apply subFormulaNTEHelp.
apply (impE L) with (substituteFormula L a v (fol.var L x2)).
apply (sysWeaken L).
apply (iffE2 L).
assert (lt_depth L a (fol.forallH L v a)).
apply depthForall.
decompose record (H _ H11 (Empty_set _)).
apply H14; clear H12 H14 H15.
unfold not in |- *; intros; elim H3.
auto.
apply
 impE
  with
    (substituteFormula L (substituteFormula L a v (fol.var L x0)) x0 (var x2)).
apply (iffE1 L).
apply (sysWeaken L).
assert (lt_depth L a (fol.forallH L v a)).
apply depthForall.
decompose record (H _ H11 (Empty_set _)).
apply H14; clear H12 H14 H15.
unfold not in |- *; intros; elim H6.
auto.
apply Axm; right; constructor.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x0)) v1
          (var v2)) x0 (var x2)).
apply (sysWeaken L).
apply (iffE1 L).
assert
 (lt_depth L (substituteFormula L a v (fol.var L x0)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H11 (Empty_set _)).
apply H15; clear H12 H14 H15; auto.
unfold not in |- *; intros.
induction H12 as [H12| H12]; auto.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L (substituteFormula L a v (fol.var L x0)) v1
             (var v2)) x0 (fol.var L x1)) x1 (var x2)).
apply (sysWeaken L).
apply (iffE1 L).
assert
 (lt_depth L
    (substituteFormula L (substituteFormula L a v (fol.var L x0)) v1 (var v2))
    (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H11 (Empty_set _)).
apply H14; clear H12 H14 H15.
unfold not in |- *; intros; elim H9.
auto.
apply Axm; right; constructor.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L
             (substituteFormula L (substituteFormula L a v (fol.var L x0)) v1
                (var v2)) x0 (fol.var L x1)) v2 s) x1 
       (var x2)).
apply (sysWeaken L).
apply (iffE1 L).
assert
 (lt_depth L
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x0)) v1
          (var v2)) x0 (fol.var L x1)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H11 (Empty_set _)).
apply H15; clear H12 H14 H15; auto.
unfold not in |- *; intros.
induction H12 as [H12| H12]; auto.
apply Axm; right; constructor.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L
             (substituteFormula L (substituteFormula L a v (fol.var L x0)) v1
                (var v2)) x0 (fol.var L x1)) v2 s) x1 
       (var x)).
apply (sysWeaken L).
apply (iffE2 L).
assert (lt_depth L A2 (fol.forallH L v a)).
unfold lt_depth, A2 in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H11 (Empty_set _)).
apply H14; clear H12 H14 H15.
unfold not in |- *; intros.
elim x2prop.
repeat right.
apply in_or_app.
right.
eapply In_list_remove1.
apply H12.
fold A2 in |- *.
apply (forallE L).
apply Axm; right; constructor.
apply (impI L).
apply forallI.
unfold not in |- *; intros.
induction H10 as (x2, H10); induction H10 as (H10, H11).
induction H11 as [x2 H11| x2 H11]; [ induction H11 | induction H11 ].
assert
 (In x1
    (freeVarFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s))).
eapply In_list_remove1.
apply H10.
induction (freeVarSubFormula3 _ _ _ _ H11).
assert (In x1 (freeVarFormula L (substituteFormula L a v (fol.var L x)))).
eapply In_list_remove1.
apply H12.
induction (freeVarSubFormula3 _ _ _ _ H13).
elim H9.
apply In_list_remove3.
apply freeVarSubFormula1.
unfold not in |- *; intros.
elim (In_list_remove2 _ _ _ _ _ H12).
auto.
apply freeVarSubFormula1.
unfold not in |- *; intros.
elim (In_list_remove2 _ _ _ _ _ H14).
auto.
eapply In_list_remove1.
apply H14.
unfold not in |- *; intros.
rewrite H15 in H14.
auto.
induction H14 as [H14| H14].
elim (In_list_remove2 _ _ _ _ _ H10).
auto.
auto.
auto.
set
 (A1 :=
  substituteFormula L
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x0)) v1
          (var v2)) x0 (fol.var L x1)) v2 s) in *.
set (A2 := substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s)
 in *.
unfold A2 in |- *.
set (x2 := newVar (v1 :: v2 :: freeVarFormula L A1 ++ freeVarFormula L A2))
 in *.
assert
 (x2prop : ~ In x2 (v1 :: v2 :: freeVarFormula L A1 ++ freeVarFormula L A2)).
unfold x2 in |- *.
apply newVar1.
unfold In in x2prop.
fold (In x2 (freeVarFormula L A1 ++ freeVarFormula L A2)) in x2prop.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s)
          x (var x2)) x2 (var x1)).
apply sysWeaken.
apply (impI L).
rewrite <- (subFormulaId L A1 x1).
apply
 impE
  with (substituteFormula L (substituteFormula L A1 x1 (var x2)) x2 (var x1)).
apply sysWeaken.
apply (iffE1 L).
assert (lt_depth L A1 (fol.forallH L v a)).
unfold lt_depth, A1 in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H10 (Empty_set _)).
apply H13; clear H11 H13 H14.
unfold not in |- *; intros; elim x2prop.
do 2 right.
apply in_or_app.
left.
eapply In_list_remove1.
apply H11.
apply subFormulaNTEHelp.
apply
 (impE L) with (substituteFormula L (substituteFormula L a v (var x2)) v1 s).
apply (sysWeaken L).
apply (impI L).
unfold A1 in |- *.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L
             (substituteFormula L (substituteFormula L a v (fol.var L x0)) v1
                (var v2)) x0 (fol.var L x1)) x1 (var x2)) v2 s).
apply sysWeaken.
apply (iffE1 L).
assert
 (lt_depth L
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x0)) v1
          (var v2)) x0 (fol.var L x1)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H10 (Empty_set _)).
apply H14; clear H11 H13 H14; auto.
unfold not in |- *; intros. 
induction H11 as [H11| H11]; auto.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L (substituteFormula L a v (fol.var L x0)) v1
             (var v2)) x0 (fol.var L x2)) v2 s).
apply sysWeaken.
apply (impI L).
apply subFormulaNTEHelp.
apply
 (impE L)
  with
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x0)) v1
          (var v2)) x0 (fol.var L x2)).
apply (sysWeaken L).
apply (iffE2 L).
assert
 (lt_depth L
    (substituteFormula L (substituteFormula L a v (fol.var L x0)) v1 (var v2))
    (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H10 (Empty_set _)).
apply H13; clear H11 H13 H14; auto.
apply Axm; right; constructor.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L (substituteFormula L a v (fol.var L x0)) x0
             (var x2)) v1 (var v2)) v2 s).
apply sysWeaken.
apply (impI L).
apply subFormulaNTEHelp.
apply
 (impE L)
  with
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x0)) x0
          (var x2)) v1 (var v2)).
apply (sysWeaken L).
apply (iffE1 L).
assert
 (lt_depth L (substituteFormula L a v (fol.var L x0)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H10 (Empty_set _)).
apply H14; clear H11 H13 H14; auto.
unfold not in |- *; intros.
induction H11 as [H11| H11]; auto.
apply Axm; right; constructor.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x0)) x0
          (var x2)) v1 s).
apply sysWeaken.
apply (iffE2 L).
assert
 (lt_depth L
    (substituteFormula L (substituteFormula L a v (fol.var L x0)) x0 (var x2))
    (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H10 (Empty_set _)).
apply H13; clear H11 H13 H14; auto.
unfold not in |- *; intros.
assert
 (In v2
    (freeVarFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x0)) x0
          (var x2)))).
eapply In_list_remove1.
apply H11.
induction (freeVarSubFormula3 _ _ _ _ H12).
assert (In v2 (freeVarFormula L (substituteFormula L a v (fol.var L x0)))).
eapply In_list_remove1.
apply H13.
induction (freeVarSubFormula3 _ _ _ _ H14).
elim H0.
apply In_list_remove3; auto.
induction H15 as [H15| H15]; auto.
induction H13 as [H13| H13]; auto.
apply subFormulaNTEHelp.
apply (impE L) with (substituteFormula L a v (var x2)).
apply (sysWeaken L).
apply (iffE2 L).
assert (lt_depth L a (fol.forallH L v a)).
apply depthForall.
decompose record (H _ H10 (Empty_set _)).
apply H13; clear H11 H13 H14; auto.
apply Axm; right; constructor.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x)) x
          (var x2)) v1 s).
apply (sysWeaken L).
apply (impI L).
apply subFormulaNTEHelp.
apply
 (impE L)
  with
    (substituteFormula L (substituteFormula L a v (fol.var L x)) x (var x2)).
apply (sysWeaken L).
apply (iffE1 L).
assert (lt_depth L a (fol.forallH L v a)).
apply depthForall.
decompose record (H _ H10 (Empty_set _)).
apply H13; clear H11 H13 H14; auto.
apply Axm; right; constructor.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s) x
       (var x2)).
apply (sysWeaken L).
apply (iffE1 L).
assert
 (lt_depth L (substituteFormula L a v (fol.var L x)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H10 (Empty_set _)).
apply H14; clear H11 H13 H14; auto.
unfold not in |- *; intros.
induction H11 as [H11| H11]; auto.
apply Axm; right; constructor.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s) x
       (var x1)).
apply sysWeaken.
apply (iffE2 L).
assert
 (lt_depth L
    (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s)
    (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H10 (Empty_set _)).
apply H13; clear H11 H13 H14; auto.
fold A2 in |- *.
unfold not in |- *; intros; elim x2prop.
do 2 right.
apply in_or_app.
right.
eapply In_list_remove1.
apply H11.
apply forallE.
apply Axm; right; constructor.
assert
 (forall (v1 v2 : nat) (s1 s2 : Term),
  v1 <> v2 ->
  ~ In v2 (freeVarTerm L s1) ->
  ~ In v1 (freeVarTerm L s2) ->
  SysPrf T
    (impH
       (substituteFormula L (substituteFormula L (fol.forallH L v a) v1 s1)
          v2 s2)
       (substituteFormula L (substituteFormula L (fol.forallH L v a) v2 s2)
          v1 s1))).
clear H2 H1 H0 s2 s1 v2 v1.
intros.
eapply (sysExtend L) with (Empty_set Formula).
unfold Included in |- *.
intros.
induction H3.
decompose record (subFormulaForall2 L a v v1 s1).
rewrite H7.
induction (eq_nat_dec v v1).
decompose record (subFormulaForall2 L a v v2 s2).
rewrite H11; clear H11.
induction (eq_nat_dec v v2).
rewrite H7.
apply (impRefl L).
clear H7.
decompose record
 (subFormulaForall2 L
    (substituteFormula L (substituteFormula L a v (fol.var L x0)) v2 s2) x0
    v1 s1).
rewrite H13; clear H13.
induction (eq_nat_dec x0 v1).
apply (impRefl L).
apply (impI L).
apply forallI.
unfold not in |- *; intros.
induction H12 as (x2, H12); induction H12 as (H12, H13).
induction H13 as [x2 H13| x2 H13]; [ induction H13 | induction H13 ].
auto.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x0)) v2 s2)
       x0 (fol.var L x1)).
apply sysWeaken.
apply (iffE2 L).
assert
 (lt_depth L
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x0)) v2 s2)
       x0 (fol.var L x1)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H12 (Empty_set _)).
apply H13; clear H13 H15 H16.
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ H13).
assert
 (In v1
    (freeVarFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x0)) v2 s2))).
eapply In_list_remove1.
apply H14.
induction (freeVarSubFormula3 _ _ _ _ H15).
assert (In v1 (freeVarFormula L (substituteFormula L a v (fol.var L x0)))).
eapply In_list_remove1.
apply H16.
induction (freeVarSubFormula3 _ _ _ _ H17).
elim (In_list_remove2 _ _ _ _ _ H18).
auto.
induction H18 as [H18| H18]; auto.
auto.
induction H14 as [H14| H14]; auto.
apply forallE.
apply Axm; right; constructor.
decompose record (subFormulaForall2 L a v v2 s2).
rewrite H11; clear H11.
induction (eq_nat_dec v v2).
rewrite H7; clear H7.
decompose record
 (subFormulaForall2 L
    (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1) x v2
    s2).
rewrite H13; clear H13.
induction (eq_nat_dec x v2).
apply (impRefl L).
apply (impI L).
apply forallI.
unfold not in |- *; intros.
induction H12 as (x2, H12); induction H12 as (H12, H13).
induction H13 as [x2 H13| x2 H13]; [ induction H13 | induction H13 ].
assert
 (In x
    (freeVarFormula L
       (substituteFormula L
          (substituteFormula L
             (substituteFormula L (substituteFormula L a v (fol.var L x)) v1
                s1) x (fol.var L x1)) v2 s2))).
eapply In_list_remove1.
apply H12.
assert
 (In x
    (freeVarFormula L
       (substituteFormula L
          (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1)
          x (fol.var L x1)))).
eapply freeVarSubFormula4.
apply H13.
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ H14).
assert
 (In v2
    (freeVarFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1))).
eapply In_list_remove1.
apply H15.
induction (freeVarSubFormula3 _ _ _ _ H16).
assert (In v2 (freeVarFormula L (substituteFormula L a v (fol.var L x)))).
eapply In_list_remove1.
apply H17.
induction (freeVarSubFormula3 _ _ _ _ H18).
elim (In_list_remove2 _ _ _ _ _ H19).
symmetry  in |- *; assumption.
induction H19 as [H19| H19].
elim b0; assumption.
contradiction.
elim H1; assumption.
induction H15 as [H15| H15].
elim H7; assumption.
contradiction.
induction (freeVarSubFormula3 _ _ _ _ H14).
elim (In_list_remove2 _ _ _ _ _ H15).
reflexivity.
elim (In_list_remove2 _ _ _ _ _ H12).
induction H15 as [H15| H15].
symmetry  in |- *; assumption.
contradiction.
set
 (A1 :=
  substituteFormula L
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1) x
       (fol.var L x1)) v2 s2) in *.
rewrite <-
 (subFormulaId L
    (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1) x)
 .
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1)
          x (var x1)) x1 (fol.var L x)).
apply sysWeaken.
apply (iffE1 L).
assert
 (lt_depth L
    (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1)
    (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H12 (Empty_set _)).
apply H15; clear H13 H15 H16.
auto.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L
             (substituteFormula L (substituteFormula L a v (fol.var L x)) v1
                s1) x (var x1)) x1 (fol.var L x)) v2 s2).
apply sysWeaken.
apply (iffE1 L).
assert
 (lt_depth L
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1)
          x (var x1)) x1 (fol.var L x)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H12 (Empty_set _)).
apply H13; clear H13 H15 H16.
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ H13).
assert
 (In v2
    (freeVarFormula L
       (substituteFormula L
          (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1)
          x (var x1)))).
eapply In_list_remove1.
apply H14.
induction (freeVarSubFormula3 _ _ _ _ H15).
assert
 (In v2
    (freeVarFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1))).
eapply In_list_remove1.
apply H16.
induction (freeVarSubFormula3 _ _ _ _ H17).
assert (In v2 (freeVarFormula L (substituteFormula L a v (fol.var L x)))).
eapply In_list_remove1.
apply H18.
induction (freeVarSubFormula3 _ _ _ _ H19).
elim (In_list_remove2 _ _ _ _ _ H20).
symmetry  in |- *; assumption.
induction H20 as [H20| H20].
elim b0; assumption.
contradiction.
elim H1; assumption.
induction H16 as [H16| H16].
elim H7; assumption.
contradiction.
induction H14 as [H14| H14].
elim b0; assumption.
contradiction.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L
             (substituteFormula L (substituteFormula L a v (fol.var L x)) v1
                s1) x (var x1)) v2 s2) x1 (fol.var L x)).
apply sysWeaken.
apply (iffE1 L).
assert
 (lt_depth L
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1) x
       (var x1)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H12 (Empty_set _)).
apply H16; clear H13 H15 H16; auto.
unfold not in |- *; intros.
induction H13 as [H13| H13]; auto.
apply forallE.
apply Axm; right; constructor.
clear H7.
decompose record
 (subFormulaForall2 L
    (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1) x v2
    s2).
rewrite H13; clear H13.
induction (eq_nat_dec x v2).
decompose record
 (subFormulaForall2 L
    (substituteFormula L (substituteFormula L a v (fol.var L x0)) v2 s2) x0
    v1 s1).
rewrite H16; clear H16.
induction (eq_nat_dec x0 v1).
apply (impI L).
apply forallI.
unfold not in |- *; intros.
induction H15 as (x3, H15); induction H15 as (H15, H16).
induction H16 as [x3 H16| x3 H16]; [ induction H16 | induction H16 ].
assert
 (In x0
    (freeVarFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1))).
eapply In_list_remove1.
apply H15.
assert (In x0 (freeVarFormula L (substituteFormula L a v (fol.var L x)))).
eapply freeVarSubFormula4.
apply H16.
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ H17).
rewrite <- a1 in H18.
auto.
induction H18 as [H18| H18]; auto.
induction (freeVarSubFormula3 _ _ _ _ H17).
auto.
rewrite a1 in H18.
induction H18 as [H18| H18]; auto.
apply impE with (substituteFormula L a v (fol.var L x0)).
apply sysWeaken.
apply (iffE2 L).
assert
 (lt_depth L (substituteFormula L a v (fol.var L x0)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H16; clear H16 H18 H19; auto.
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ H16).
rewrite <- a0 in H17.
auto.
induction H17 as [H17| H17]; auto.
rewrite <- (subFormulaId L (substituteFormula L a v (fol.var L x0)) x0).
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x0)) x0
          (var x)) x (fol.var L x0)).
apply sysWeaken.
apply (iffE1 L).
assert
 (lt_depth L (substituteFormula L a v (fol.var L x0)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H18; clear H16 H18 H19; auto.
unfold not in |- *; intros.
assert (In x (freeVarFormula L (substituteFormula L a v (fol.var L x0)))).
eapply In_list_remove1.
apply H16.
induction (freeVarSubFormula3 _ _ _ _ H17).
auto.
rewrite a1 in H18.
induction H18 as [H18| H18]; auto.
apply
 impE
  with
    (substituteFormula L (substituteFormula L a v (var x)) x (fol.var L x0)).
apply sysWeaken.
apply (impI L).
apply subFormulaNTEHelp.
apply (impE L) with (substituteFormula L a v (var x)).
apply (sysWeaken L).
apply (iffE2 L).
assert (lt_depth L a (fol.forallH L v a)).
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H18; clear H16 H18 H19; auto.
apply Axm; right; constructor.
apply forallE.
apply
 impE
  with
    (fol.forallH L x
       (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1)).
apply sysWeaken.
apply (iffE1 L).
apply (reduceForall L).
unfold not in |- *; intros.
induction H15 as (x3, H15); induction H15 as (H15, H16).
induction H16; simple induction H16.
assert
 (lt_depth L (substituteFormula L a v (fol.var L x)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H16; clear H16 H18 H19; auto.
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ H16).
rewrite <- a1 in H17.
auto.
induction H17 as [H17| H17]; auto.
apply Axm; right; constructor.
apply (impI L).
apply forallI.
unfold not in |- *; intros.
induction H15 as (x3, H15); induction H15 as (H15, H16).
induction H16 as [x3 H16| x3 H16]; [ induction H16 | induction H16 ].
assert
 (In x2
    (freeVarFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1))).
eapply In_list_remove1.
apply H15.
induction (freeVarSubFormula3 _ _ _ _ H16).
assert (In x2 (freeVarFormula L (substituteFormula L a v (fol.var L x)))).
eapply In_list_remove1.
apply H17.
induction (freeVarSubFormula3 _ _ _ _ H18).
elim H14.
apply In_list_remove3.
apply freeVarSubFormula1.
rewrite <- a0.
unfold not in |- *; intros.
apply (In_list_remove2 _ _ _ _ _ H15).
auto.
apply freeVarSubFormula1.
unfold not in |- *; intros.
apply (In_list_remove2 _ _ _ _ _ H19).
auto.
eapply In_list_remove1.
apply H19.
unfold not in |- *; intros.
rewrite H20 in H19.
auto.
induction H19 as [H19| H19].
elim (In_list_remove2 _ _ _ _ _ H15).
auto.
contradiction.
auto.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x0)) x0
          (fol.var L x2)) v1 s1).
apply sysWeaken.
apply (impI L).
repeat apply subFormulaNTEHelp.
apply (impE L) with (substituteFormula L a v (fol.var L x0)).
apply (sysWeaken L).
apply (iffE2 L).
assert
 (lt_depth L (substituteFormula L a v (fol.var L x0)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H16; clear H16 H18 H19; auto.
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ H16).
rewrite <- a0 in H17.
auto.
induction H17 as [H17| H17]; auto.
apply Axm; right; constructor.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (var x)) x
          (fol.var L x2)) v1 s1).
apply sysWeaken.
apply (impI L).
apply subFormulaNTEHelp.
apply (impE L) with (substituteFormula L a v (var x2)).
apply (sysWeaken L).
apply (iffE2 L).
assert (lt_depth L a (fol.forallH L v a)).
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H18; clear H16 H18 H19; auto.
apply
 impE
  with
    (substituteFormula L (substituteFormula L a v (var x)) x (fol.var L x2)).
apply (sysWeaken L).
apply (iffE1 L).
assert (lt_depth L a (fol.forallH L v a)).
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H18; clear H16 H18 H19; auto.
apply Axm; right; constructor.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (var x)) v1 s1) x
       (fol.var L x2)).
apply sysWeaken.
apply (iffE1 L).
assert (lt_depth L (substituteFormula L a v (var x)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H19; clear H16 H18 H19; auto.
unfold not in |- *; intros.
induction H16 as [H16| H16]; auto.
apply forallE.
apply Axm; right; constructor.
decompose record
 (subFormulaForall2 L
    (substituteFormula L (substituteFormula L a v (fol.var L x0)) v2 s2) x0
    v1 s1).
rewrite H16; clear H16.
induction (eq_nat_dec x0 v1).
apply (impI L).
apply forallI.
unfold not in |- *; intros.
induction H15 as (x3, H15); induction H15 as (H15, H16).
induction H16 as [x3 H16| x3 H16]; [ induction H16 | induction H16 ].
assert
 (In x0
    (freeVarFormula L
       (substituteFormula L
          (substituteFormula L
             (substituteFormula L (substituteFormula L a v (fol.var L x)) v1
                s1) x (fol.var L x1)) v2 s2))).
eapply In_list_remove1.
apply H15.
induction (freeVarSubFormula3 _ _ _ _ H16).
assert
 (In x0
    (freeVarFormula L
       (substituteFormula L
          (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1)
          x (fol.var L x1)))).
eapply In_list_remove1.
apply H17.
induction (freeVarSubFormula3 _ _ _ _ H18).
assert
 (In x0
    (freeVarFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1))).
eapply In_list_remove1.
apply H19.
assert (In x0 (freeVarFormula L (substituteFormula L a v (fol.var L x)))).
eapply freeVarSubFormula4.
apply H20.
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ H21).
rewrite <- a0 in H22.
elim H9; assumption.
rewrite <- a0 in H22.
induction H22 as [H22| H22].
elim (In_list_remove2 _ _ _ _ _ H19).
symmetry  in |- *; assumption.
contradiction.
induction (freeVarSubFormula3 _ _ _ _ H21).
elim H9; assumption.
rewrite a0 in H22.
induction H22 as [H22| H22].
elim H3; assumption.
contradiction.
induction H19 as [H19| H19].
elim (In_list_remove2 _ _ _ _ _ H15).
symmetry  in |- *; assumption.
contradiction.
elim H8; assumption.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1)
          x (fol.var L x0)) v2 s2).
apply sysWeaken.
apply (impI L).
apply subFormulaNTEHelp.
apply
 (impE L)
  with
    (substituteFormula L (substituteFormula L a v (fol.var L x)) x
       (fol.var L x0)).
apply (sysWeaken L).
apply (iffE1 L).
assert (lt_depth L a (fol.forallH L v a)).
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H18; clear H16 H18 H19; auto.
apply subFormulaNTEHelp.
apply
 (impE L)
  with (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1).
apply (sysWeaken L).
apply (iffE1 L).
assert
 (lt_depth L (substituteFormula L a v (fol.var L x)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H16; clear H16 H18 H19; auto.
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ H16).
rewrite <- a0 in H17.
auto.
induction H17 as [H17| H17]; auto.
apply Axm; right; constructor.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L
             (substituteFormula L (substituteFormula L a v (fol.var L x)) v1
                s1) x (fol.var L x1)) v2 s2) x1 (var x0)).
apply sysWeaken.
apply
 (impTrans L)
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L
             (substituteFormula L (substituteFormula L a v (fol.var L x)) v1
                s1) x (fol.var L x1)) x1 (var x0)) v2 s2).
apply (iffE1 L).
assert
 (lt_depth L
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1) x
       (fol.var L x1)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H19; clear H16 H18 H19; auto.
rewrite a0.
unfold not in |- *; intros.
induction H16 as [H16| H16]; auto.
apply (impI L).
apply subFormulaNTEHelp.
apply
 (impE L)
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1)
          x (fol.var L x1)) x1 (var x0)).
apply (sysWeaken L).
apply (iffE1 L).
assert
 (lt_depth L
    (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1)
    (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H18; clear H16 H18 H19; auto.
apply Axm; right; constructor.
apply forallE.
apply Axm; right; constructor.
apply (impI L).
set
 (z1 :=
  newVar
    (v2
     :: v1
        :: freeVarFormula L
             (fol.forallH L x2
                (substituteFormula L
                   (substituteFormula L
                      (substituteFormula L
                         (substituteFormula L a v (fol.var L x0)) v2 s2) x0
                      (fol.var L x2)) v1 s1)) ++
           freeVarFormula L
             (fol.forallH L x1
                (substituteFormula L
                   (substituteFormula L
                      (substituteFormula L
                         (substituteFormula L a v (fol.var L x)) v1 s1) x
                      (fol.var L x1)) v2 s2)))) in *.
assert
 (z1prop :
  ~
  In z1
    (v2
     :: v1
        :: freeVarFormula L
             (fol.forallH L x2
                (substituteFormula L
                   (substituteFormula L
                      (substituteFormula L
                         (substituteFormula L a v (fol.var L x0)) v2 s2) x0
                      (fol.var L x2)) v1 s1)) ++
           freeVarFormula L
             (fol.forallH L x1
                (substituteFormula L
                   (substituteFormula L
                      (substituteFormula L
                         (substituteFormula L a v (fol.var L x)) v1 s1) x
                      (fol.var L x1)) v2 s2)))).
unfold z1 in |- *; apply newVar1.
unfold In in z1prop.
fold
 (In z1
    (freeVarFormula L
       (fol.forallH L x2
          (substituteFormula L
             (substituteFormula L
                (substituteFormula L (substituteFormula L a v (fol.var L x0))
                   v2 s2) x0 (fol.var L x2)) v1 s1)) ++
     freeVarFormula L
       (fol.forallH L x1
          (substituteFormula L
             (substituteFormula L
                (substituteFormula L (substituteFormula L a v (fol.var L x))
                   v1 s1) x (fol.var L x1)) v2 s2)))) 
 in z1prop.
apply
 impE
  with
    (forallH z1
       (substituteFormula L
          (substituteFormula L
             (substituteFormula L
                (substituteFormula L (substituteFormula L a v (fol.var L x))
                   v1 s1) x (fol.var L x1)) v2 s2) x1 
          (var z1))).
apply sysWeaken.
apply
 (impTrans L)
  with
    (forallH z1
       (substituteFormula L
          (substituteFormula L
             (substituteFormula L
                (substituteFormula L (substituteFormula L a v (fol.var L x0))
                   v2 s2) x0 (fol.var L x2)) v1 s1) x2 
          (var z1))).
apply (impI L).
apply (forallI L).
unfold not in |- *; intros.
induction H15 as (x3, H15); induction H15 as (H15, H16).
induction H16 as [x3 H16| x3 H16]; [ induction H16 | induction H16 ].
elim (In_list_remove2 _ _ _ _ _ H15).
reflexivity.
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L
             (substituteFormula L (substituteFormula L a v (fol.var L x)) v1
                s1) x (fol.var L x1)) v2 s2) x1 (var z1)).
apply sysWeaken.
apply
 (impTrans L)
  with
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L z1)) v1 s1)
       v2 s2).
apply
 (impTrans L)
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L (substituteFormula L a v (var x)) x
             (fol.var L z1)) v1 s1) v2 s2).
apply
 (impTrans L)
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L (substituteFormula L a v (var x)) v1 s1) x
          (fol.var L z1)) v2 s2).
apply
 (impTrans L)
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L
             (substituteFormula L (substituteFormula L a v (var x)) v1 s1) x
             (var x1)) x1 (fol.var L z1)) v2 s2).
apply (iffE1 L).
assert
 (lt_depth L
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x)) v1 s1) x
       (fol.var L x1)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H19; clear H16 H18 H19; auto.
unfold not in |- *; intros.
induction H16 as [H16| H16]; auto.

apply (impI L).
apply subFormulaNTEHelp.
apply
 (impE L)
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L (substituteFormula L a v (var x)) v1 s1) x
          (var x1)) x1 (fol.var L z1)).
apply (sysWeaken L).
apply (iffE1 L).
assert
 (lt_depth L (substituteFormula L (substituteFormula L a v (var x)) v1 s1)
    (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H18; clear H16 H18 H19; auto.
apply Axm; right; constructor.
apply (impI L).
apply subFormulaNTEHelp.
apply
 (impE L)
  with
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (var x)) v1 s1) x
       (fol.var L z1)).
apply (sysWeaken L).
apply (iffE1 L).
assert (lt_depth L (substituteFormula L a v (var x)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H19; clear H16 H18 H19; auto.
unfold not in |- *; intros.
induction H16 as [H16| H16]; auto.
apply Axm; right; constructor.
apply (impI L).
repeat apply subFormulaNTEHelp.
apply
 (impE L)
  with
    (substituteFormula L (substituteFormula L a v (var x)) x (fol.var L z1)).
apply (sysWeaken L).
apply (iffE1 L).
assert (lt_depth L a (fol.forallH L v a)).
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H18; clear H16 H18 H19; auto.
apply Axm; right; constructor.
apply
 (impTrans L)
  with
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L z1)) v2 s2)
       v1 s1).
apply (iffE1 L).
assert
 (lt_depth L (substituteFormula L a v (fol.var L z1)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H19; clear H16 H18 H19; auto.
apply
 (impTrans L)
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L (substituteFormula L a v (var x0)) x0
             (fol.var L z1)) v2 s2) v1 s1).
apply (impI L).
repeat apply subFormulaNTEHelp.
apply (impE L) with (substituteFormula L a v (fol.var L z1)).
apply (sysWeaken L).
apply (iffE2 L).
assert (lt_depth L a (fol.forallH L v a)).
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H18; clear H16 H18 H19; auto.
apply Axm; right; constructor.
apply
 (impTrans L)
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L (substituteFormula L a v (var x0)) v2 s2) x0
          (fol.var L z1)) v1 s1).
apply (impI L).
apply subFormulaNTEHelp.
apply
 (impE L)
  with
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (var x0)) x0
          (fol.var L z1)) v2 s2).
apply (sysWeaken L).
apply (iffE2 L).
assert (lt_depth L (substituteFormula L a v (var x0)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H19; clear H16 H18 H19; auto.
unfold not in |- *; intros.
induction H16 as [H16| H16]; auto.
apply Axm; right; constructor.
apply
 (impTrans L)
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L
             (substituteFormula L (substituteFormula L a v (fol.var L x0)) v2
                s2) x0 (fol.var L x2)) x2 (var z1)) v1 s1).
apply (impI L).
repeat apply subFormulaNTEHelp.
apply
 (impE L)
  with
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (var x0)) v2 s2) x0
       (fol.var L z1)).
apply (sysWeaken L).
apply (iffE2 L).
assert
 (lt_depth L
    (substituteFormula L (substituteFormula L a v (fol.var L x0)) v2 s2)
    (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H18; clear H16 H18 H19; auto.
apply Axm; right; constructor.
apply (iffE1 L).
assert
 (lt_depth L
    (substituteFormula L
       (substituteFormula L (substituteFormula L a v (fol.var L x0)) v2 s2)
       x0 (fol.var L x2)) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H19; clear H16 H18 H19; auto.
unfold not in |- *; intros.
induction H16 as [H16| H16]; auto.
eapply forallSimp.
apply Axm; right; constructor.
apply (impI L).
apply forallI.
unfold not in |- *; intros.
induction H15 as (x3, H15); induction H15 as (H15, H16).
induction H16 as [x3 H16| x3 H16]; [ induction H16 | induction H16 ].
assert
 (In x2
    (freeVarFormula L
       (substituteFormula L
          (substituteFormula L
             (substituteFormula L
                (substituteFormula L (substituteFormula L a v (fol.var L x0))
                   v2 s2) x0 (fol.var L x2)) v1 s1) x2 
          (var z1)))).
eapply In_list_remove1.
apply H15.
induction (freeVarSubFormula3 _ _ _ _ H16).
elim (In_list_remove2 _ _ _ _ _ H17).
reflexivity.
induction H17 as [H17| H17].
elim (In_list_remove2 _ _ _ _ _ H15).
symmetry  in |- *; assumption.
contradiction.
set
 (A1 :=
  forallH z1
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L
             (substituteFormula L (substituteFormula L a v (fol.var L x0)) v2
                s2) x0 (fol.var L x2)) v1 s1) x2 (var z1))) 
 in *.
rewrite <-
 (subFormulaId L
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L (substituteFormula L a v (fol.var L x0)) v2 s2)
          x0 (fol.var L x2)) v1 s1) x2).
apply
 impE
  with
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L
             (substituteFormula L
                (substituteFormula L (substituteFormula L a v (fol.var L x0))
                   v2 s2) x0 (fol.var L x2)) v1 s1) x2 
          (var z1)) z1 (fol.var L x2)).
apply sysWeaken.
apply (iffE1 L).
assert
 (lt_depth L
    (substituteFormula L
       (substituteFormula L
          (substituteFormula L (substituteFormula L a v (fol.var L x0)) v2 s2)
          x0 (fol.var L x2)) v1 s1) (fol.forallH L v a)).
unfold lt_depth in |- *.
repeat rewrite subFormulaDepth.
apply depthForall.
decompose record (H _ H15 (Empty_set _)).
apply H18; clear H16 H18 H19.
unfold not in |- *; intros; elim z1prop.
do 2 right.
apply in_or_app.
tauto.
apply forallE.
unfold A1 in |- *.
apply Axm; right; constructor.
apply (forallI L).
unfold not in |- *; intros.
induction H15 as (x3, H15); induction H15 as (H15, H16).
induction H16 as [x3 H16| x3 H16]; [ induction H16 | induction H16 ].
elim z1prop.
do 2 right.
apply in_or_app.
tauto.
apply forallE.
apply Axm; right; constructor.
apply (iffI L).
apply H3; auto.
apply H3; auto.
Qed.

Lemma subFormulaNil :
 forall (f : Formula) (T : System) (v : nat) (s : Term),
 ~ In v (freeVarFormula L f) -> SysPrf T (iffH (substituteFormula L f v s) f).
Proof.
intros f T.
eapply proj1.
apply subFormulaNTE.
Qed.

Lemma subFormulaTrans :
 forall (f : Formula) (T : System) (v1 v2 : nat) (s : Term),
 ~ In v2 (list_remove _ eq_nat_dec v1 (freeVarFormula L f)) ->
 SysPrf T
   (iffH (substituteFormula L (substituteFormula L f v1 (var v2)) v2 s)
      (substituteFormula L f v1 s)).
Proof.
intros f T.
eapply proj1.
eapply proj2.
apply subFormulaNTE.
Qed.

Lemma subFormulaExch :
 forall (f : Formula) (T : System) (v1 v2 : nat) (s1 s2 : Term),
 v1 <> v2 ->
 ~ In v2 (freeVarTerm L s1) ->
 ~ In v1 (freeVarTerm L s2) ->
 SysPrf T
   (iffH (substituteFormula L (substituteFormula L f v1 s1) v2 s2)
      (substituteFormula L (substituteFormula L f v2 s2) v1 s1)).
Proof.
intros f T.
eapply proj2.
eapply proj2.
apply subFormulaNTE.
Qed.

End Substitution_Properties.

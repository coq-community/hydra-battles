
Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import Peano_dec.
Require Import ListExt.

Require Import folProof.
Require Import folLogic2.
Require Import folProp.
Require Import folReplace.
Require Import subProp.
Require Import Compat815.
From Coq Require Import Lia.

From LibHyps Require Export LibHyps.
From hydras Require Export MoreLibHyps. 

Section SubAllVars.

Variable L : Language.
Notation Formula := (Formula L) (only parsing).
Notation Formulas := (Formulas L) (only parsing).
Notation System := (System L) (only parsing).
Notation Term := (Term L) (only parsing).
Notation Terms := (Terms L) (only parsing).
Notation SysPrf := (SysPrf L) (only parsing).

Fixpoint subAllTerm (t : fol.Term L) : (nat -> fol.Term L) -> fol.Term L :=
  match t return ((nat -> fol.Term L) -> fol.Term L) with
  | var x => fun m => m x
  | apply f ts => fun m => apply f (subAllTerms _ ts m)
  end
 
 with subAllTerms (n : nat) (ts : fol.Terms L n) {struct ts} :
 (nat -> fol.Term L) -> fol.Terms L n :=
  match
    ts in (fol.Terms _ n) return ((nat -> fol.Term L) -> fol.Terms L n)
  with
  | Tnil => fun _ => Tnil
  | Tcons n' t ss =>
      fun m => Tcons (subAllTerm t m) (subAllTerms _ ss m)
  end.

Lemma subAllTerm_ext (t : fol.Term L) :
  forall (m1 m2 : nat -> fol.Term L),
    (forall m : nat, In m (freeVarTerm L t) -> m1 m = m2 m) ->
    subAllTerm t m1 = subAllTerm t m2.
Proof.
  elim t using
    Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             forall m1 m2 : nat -> fol.Term L,
               (forall m : nat, In m (freeVarTerms L n ts) -> m1 m = m2 m) ->
               subAllTerms n ts m1 = subAllTerms n ts m2); simpl. 
  - intros n m1 m2 H; apply H; auto.
  - intros f t0 H m1 m2 H0; rewrite (H m1 m2).
    + reflexivity.
    + intros m H1;  apply H0; apply H1.
  - reflexivity. 
  - intros n t0 H t1 H0 m1 m2 H1; rewrite (H m1 m2).
    + rewrite (H0 m1 m2).
      * reflexivity. 
      * intros m H2;  apply H1.
        unfold freeVarTerms; fold (freeVarTerms L n t1).
        apply in_or_app; auto.
    + intros m H2; apply H1.
      unfold freeVarTerms; fold (freeVarTerms L n t1); apply in_or_app; auto.
Qed.

Lemma subAllTerms_ext (n : nat) (ts : fol.Terms L n) (m1 m2 : nat -> fol.Term L):
 (forall m : nat, In m (freeVarTerms L n ts) -> m1 m = m2 m) ->
 subAllTerms n ts m1 = subAllTerms n ts m2.
Proof.
  intros H; induction ts as [| n t ts Hrects].
  - reflexivity. 
  - simpl; rewrite Hrects.
    + rewrite (subAllTerm_ext t m1 m2); [reflexivity| ].
      intros m H0; apply H.
      unfold freeVarTerms; fold (freeVarTerms L n ts); apply in_or_app; auto.
    + intros m H0; apply H.
      unfold freeVarTerms; fold (freeVarTerms L n ts); apply in_or_app; auto.
Qed.

Fixpoint freeVarMap (l : list nat) : (nat -> fol.Term L) -> list nat :=
  match l with
  | nil => fun _ => nil
  | a :: l' => fun m => freeVarTerm L (m a) ++ freeVarMap l' m
  end.

Lemma freeVarMap_ext (l : list nat) (f1 f2 : nat -> fol.Term L):
 (forall m : nat, In m l -> f1 m = f2 m) -> freeVarMap l f1 = freeVarMap l f2.
Proof.
  intros H; induction l as [| a l Hrecl].
  - reflexivity.
  - simpl; rewrite Hrecl, H. 
    + reflexivity.
    + auto with datatypes.
    + intros m H0; apply H; auto with datatypes.
Qed.

Lemma freeVarMap1 (l : list nat) (m : nat -> fol.Term L) (v n : nat):
 In v (freeVarTerm L (m n)) -> In n l -> In v (freeVarMap l m).
Proof.
  intros H H0; induction l as [| a l Hrecl].
  - elim H0.
  - induction H0 as [H0| H0].
    + simpl; rewrite H0; auto with datatypes.
    + simpl; auto with datatypes.
Qed.

Fixpoint subAllFormula (f : Formula) (m : (nat -> Term)) {struct f} : Formula :=
  match f with
  | equal t s => equal (subAllTerm t m) (subAllTerm s m)
  | atomic r ts => atomic r (subAllTerms _ ts m)
  | impH f g =>
      impH (subAllFormula f m) (subAllFormula g m)
  | fol.notH f => notH (subAllFormula f m)
  | fol.forallH n f =>
      let nv :=
        newVar
          (freeVarFormula L f ++
           freeVarMap (freeVarFormula L (forallH n f)) m) in
      forallH nv
        (subAllFormula f
           (fun v : nat =>
            match eq_nat_dec v n with
            | left _ => var nv
            | right _ => m v
            end))
  end.


Lemma subAllFormula_ext :
 forall (f : fol.Formula L) (m1 m2 : nat -> fol.Term L),
 (forall m : nat, In m (freeVarFormula L f) -> m1 m = m2 m) ->
 subAllFormula f m1 = subAllFormula f m2.
Proof.
  intro f; induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
    simpl.
  - intros m1 m2 H; rewrite (subAllTerm_ext t m1 m2).
    + rewrite (subAllTerm_ext t0 m1 m2).
      * reflexivity.
      * intros m H0; apply H.
        apply in_or_app; auto.
    + intros m H0; apply H.
      apply in_or_app; auto.
  - intros m1 m2 H; rewrite (subAllTerms_ext _ t m1 m2).
    + reflexivity.
    + apply H.
  - intros m1 m2 H; rewrite (Hrecf1 m1 m2).
    + rewrite (Hrecf0 m1 m2).
      * reflexivity.
      * intros m H0; apply H.
        apply in_or_app; auto.
    + intros m H0; apply H.
      apply in_or_app; auto.
  - intros m1 m2 H; rewrite (Hrecf m1 m2).
    + reflexivity.
    + apply H.
  - intros m1 m2 H;  rewrite
        (freeVarMap_ext (List.remove eq_nat_dec n (freeVarFormula L f)) m1 m2).
    + set
        (m1' :=
           fun v : nat =>
             match eq_nat_dec v n with
             | left _ =>
                 var 
                   (newVar
                      (freeVarFormula L f ++
                         freeVarMap (List.remove  eq_nat_dec n 
                                       (freeVarFormula L f)) m2))
             | right _ => m1 v
             end). 
      set
        (m2' :=
           fun v : nat =>
             match eq_nat_dec v n with
             | left _ =>
                 var 
                   (newVar
                      (freeVarFormula L f ++
                         freeVarMap (List.remove eq_nat_dec n 
                                       (freeVarFormula L f)) m2))
             | right _ => m2 v
             end).
      rewrite (Hrecf m1' m2').
      * reflexivity.
      * intros m H0; unfold m1', m2'; clear m1' m2'.
        induction (eq_nat_dec m n).
        -- reflexivity.
        -- apply H; apply in_in_remove; auto.
    + intros m H0; apply H, H0. 
Qed.

Lemma freeVarSubAllTerm1 (t : fol.Term L) (m : nat -> fol.Term L) (v : nat):
 In v (freeVarTerm L (subAllTerm t m)) ->
 exists n : nat, In n (freeVarTerm L t) /\ In v (freeVarTerm L (m n)).
Proof.
  elim t using Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             In v (freeVarTerms L n (subAllTerms n ts m)) ->
             exists a : nat,
               In a (freeVarTerms L n ts) /\ In v (freeVarTerm L (m a))).
  - intros n H; simpl in H; exists n.
    simpl; auto.
  - intros f t0 H H0; simpl in H0; auto.
  - intros H; contradiction. 
  - intros n t0 H t1 H0 H1; simpl in H1.
    unfold freeVarTerms in H1; fold (freeVarTerm L (subAllTerm t0 m)) in H1.
    fold (freeVarTerms L n (subAllTerms n t1 m)) in H1.
    induction (in_app_or _ _ _ H1) as [H2 | H2].
    + induction (H H2) as [x H3]; exists x; split.
      * unfold freeVarTerms; fold (freeVarTerm L t0);fold (freeVarTerms L n t1).
        apply in_or_app; tauto.
      * tauto.
    + induction (H0 H2) as [x H3]; exists x; split.
      * unfold freeVarTerms; fold (freeVarTerm L t0); fold (freeVarTerms L n t1). 
        apply in_or_app.
        tauto.
      * tauto.
Qed.

Lemma freeVarSubAllTerms1 (n : nat) (ts : fol.Terms L n) (m : nat -> fol.Term L) (v : nat):
 In v (freeVarTerms L n (subAllTerms n ts m)) ->
 exists a : nat, In a (freeVarTerms L n ts) /\ In v (freeVarTerm L (m a)).
Proof.
  induction ts as [| n t ts Hrects].
  - intros H; contradiction. 
  - intros H; simpl in H.
    unfold freeVarTerms in H; 
      fold (freeVarTerm L (subAllTerm t m)) in H;
      fold (freeVarTerms L n (subAllTerms n ts m)) in H.
    induction (in_app_or _ _ _ H) as [H0 | H0].
    + induction (freeVarSubAllTerm1 _ _ _ H0) as [x H1]; exists x; split.
      * unfold freeVarTerms; fold (freeVarTerm L t); fold (freeVarTerms L n ts). 
        apply in_or_app;  tauto.
      * tauto.
    + induction (Hrects H0) as [x H1]; exists x; split.
      * unfold freeVarTerms; fold (freeVarTerm L t); fold (freeVarTerms L n ts).
        apply in_or_app; tauto.
      * tauto.
Qed.

Lemma freeVarSubAllTerm2 (t : fol.Term L) (m : nat -> fol.Term L) (v n : nat):
 In n (freeVarTerm L t) ->
 In v (freeVarTerm L (m n)) -> In v (freeVarTerm L (subAllTerm t m)).
Proof.
  elim t using Term_Terms_ind with
    (P0 := fun (a : nat) (ts : fol.Terms L a) =>
             In n (freeVarTerms L a ts) ->
             In v (freeVarTerm L (m n)) ->
             In v (freeVarTerms L a (subAllTerms a ts m))).
  - intros n0 [H | H] H0; simpl in H |- *.
    + now rewrite H.
    + contradiction H.
  - auto.
  - auto.
  - intros n0 t0 H t1 H0 H1 H2;
      simpl; unfold freeVarTerms; fold (freeVarTerm L (subAllTerm t0 m)).
    fold (freeVarTerms L n0 (subAllTerms n0 t1 m)); apply in_or_app.
    unfold freeVarTerms in H1.
    fold (freeVarTerm L t0) in H1.
    fold (freeVarTerms L n0 t1) in H1.
    induction (in_app_or _ _ _ H1); auto.
Qed.

Lemma freeVarSubAllTerms2 (a : nat) (ts : fol.Terms L a) (m : nat -> fol.Term L) 
  (v n : nat): 
  In n (freeVarTerms L a ts) ->
  In v (freeVarTerm L (m n)) -> In v (freeVarTerms L a (subAllTerms a ts m)).
Proof.
  intros H H0; induction ts as [| n0 t ts Hrects].
  - apply H.
  - simpl; unfold freeVarTerms;
      fold (freeVarTerm L (subAllTerm t m)); 
      fold (freeVarTerms L n0 (subAllTerms n0 ts m)).
    apply in_or_app.
    unfold freeVarTerms in H; fold (freeVarTerm L t) in H; 
      fold (freeVarTerms L n0 ts) in H.
    induction (in_app_or _ _ _ H) as [H1 | H1].
    + left; eapply freeVarSubAllTerm2.
      * apply H1.
      * assumption.
    + auto.
Qed.

Lemma freeVarSubAllFormula1 :
 forall (f : fol.Formula L) (m : nat -> fol.Term L) (v : nat),
 In v (freeVarFormula L (subAllFormula f m)) ->
 exists n : nat, In n (freeVarFormula L f) /\ In v (freeVarTerm L (m n)).
Proof.
  intro f;
    induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf]; simpl.
  - intros m v H; induction (in_app_or _ _ _ H);
 (induction (freeVarSubAllTerm1 _ _ _ H0); exists x; split;
   [ apply in_or_app; tauto | tauto ]).
  - intros m v H;  apply freeVarSubAllTerms1; apply H.
- intros m v H; induction (in_app_or _ _ _ H) as [H0 | H0];
 (induction (Hrecf1 _ _ H0) || induction (Hrecf0 _ _ H0); exists x; split;
   [ apply in_or_app; tauto | tauto ]).
- intros m v H; apply Hrecf.
  apply H. 
-  intros m v H; set
    (nv :=
       newVar
         (freeVarFormula L f ++
            freeVarMap (List.remove eq_nat_dec n (freeVarFormula L f)) m)). 
 
   assert
     (H0: In v
            (freeVarFormula L
               (subAllFormula f
                  (fun v : nat =>
                     match eq_nat_dec v n with
                     | left _ => var nv
                     | right _ => m v
                     end)))) by ( eapply in_remove; apply H). 
   destruct  (Hrecf _ _ H0) as [x [H2 H3]].
   induction (eq_nat_dec x n) as [a | ?].
   + elim (in_remove_neq _ _ _ _ _ H).
     induction H3 as [H1| H1].
     auto.
     contradiction.
   + exists x.
     split.
     * apply in_in_remove; auto.
     * auto.
Qed.

Lemma freeVarSubAllFormula2 :
 forall (f : fol.Formula L) (m : nat -> fol.Term L) (v n : nat),
 In n (freeVarFormula L f) ->
 In v (freeVarTerm L (m n)) -> 
 In v (freeVarFormula L (subAllFormula f m)).
Proof.
  intro f; induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
    simpl.
  - intros m v n H H0; apply in_or_app.
    induction (in_app_or _ _ _ H) as [H1 | H1].
    + left; eapply freeVarSubAllTerm2.
      * apply H1.
      * apply H0.
    + right; eapply freeVarSubAllTerm2.
      * apply H1.
      * apply H0.
  - intros m v n H H0; eapply freeVarSubAllTerms2.
    + apply H.
    + apply H0.
  - intros m v n H H0; apply in_or_app.
    induction (in_app_or _ _ _ H) as [H1 | H1].
    + left; eapply Hrecf1.
      * apply H1.
      * apply H0.
    + right; eapply Hrecf0.
      * apply H1.
      * apply H0.
  - intros m v n H H0; eapply Hrecf.
    + apply H.
    + apply H0.
  - intros m v n0 H H0; apply in_in_remove.
     + intro H1; 
        eapply
          (newVar1
             (freeVarFormula L f ++
                freeVarMap (List.remove eq_nat_dec n 
                              (freeVarFormula L f)) m)).
      rewrite <-  H1; clear H1; apply in_or_app.
      right.
      clear Hrecf.
      induction (List.remove eq_nat_dec n (freeVarFormula L f)); 
        simpl in |- *.
      * contradiction H.
      * apply in_or_app; simpl in H.
        destruct  H as [H | H].
        -- rewrite H; auto.
        -- auto. 
     + eapply Hrecf.
       * eapply in_remove; apply H.
       * induction (eq_nat_dec n0 n) as [a | b].
         -- now elim (in_remove_neq _ _ _ _ _ H).
         -- auto.
Qed.

Lemma subSubAllTerm (t : fol.Term L) (m : nat -> fol.Term L) (v : nat) (s : fol.Term L):
 substT L (subAllTerm t m) v s =
 subAllTerm t (fun n : nat => substT L (m n) v s).
Proof.
  elim t using
    Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             substituteTerms L n (subAllTerms n ts m) v s =
               subAllTerms n ts (fun n : nat => substT L (m n) v s)). 
   - intro n; simpl; auto.
   - intros f t0 H; simpl; rewrite H; auto.
   - auto. 
   - intros n t0 H t1 H0; simpl; now rewrite H, H0.
Qed.

Lemma subSubAllTerms (n : nat) (ts : fol.Terms L n) (m : nat -> fol.Term L) 
  (v : nat) (s : fol.Term L) :
  substituteTerms L n (subAllTerms n ts m) v s =
    subAllTerms n ts (fun n : nat => substT L (m n) v s).
Proof.
  induction ts as [| n t ts Hrects].
  - auto.
  - simpl; now rewrite subSubAllTerm, Hrects.
Qed.

Lemma subSubAllFormula :
  forall (T : fol.System L) (f : fol.Formula L) (m : nat -> fol.Term L)
         (v : nat) (s : fol.Term L),
    folProof.SysPrf L T
      (iffH (substituteFormula L (subAllFormula f m) v s)
         (subAllFormula f (fun n : nat => substT L (m n) v s))).
Proof.
  intros T f.  revert T. 
  elim f using Formula_depth_ind2; simpl in |- *. 
  -  intros t t0 T m v s; rewrite (subFormulaEqual L).
     do 2 rewrite subSubAllTerm.
     apply (iffRefl L).
  - intros r t T m v s; rewrite (subFormulaRelation L).
    rewrite subSubAllTerms;  apply (iffRefl L).
  - intros f0 H f1 H0 T m v s; rewrite (subFormulaImp L).
    apply (reduceImp L).
    + apply H.
    + apply H0.
  - intros f0 H T m v s; rewrite (subFormulaNot L).
    apply (reduceNot L).
    apply H.
  - intros v a H T m v0 s; 
      set
        (nv1 :=
           newVar
             (freeVarFormula L a ++
                freeVarMap (List.remove eq_nat_dec v (freeVarFormula L a)) m)). 
    set
      (nv2 :=
         newVar
           (freeVarFormula L a ++
              freeVarMap (List.remove eq_nat_dec v (freeVarFormula L a))
              (fun n : nat => substT L (m n) v0 s))).
    apply (sysExtend L) with (Empty_set (fol.Formula L)).
    + unfold Included; intros x H0; destruct H0.
    + decompose record
        (subFormulaForall2 L
           (subAllFormula a
              (fun v1 : nat =>
                 match eq_nat_dec v1 v with
                 | left _ => var nv1
                 | right _ => m v1
                 end)) nv1 v0 s) /r; intros x H1  H0 H2 H4.
      rewrite H4; clear H4.
      induction (eq_nat_dec nv1 v0) as [a0 | ?].
      * assert
          (H3: forall n : nat,
              In n (freeVarFormula L (forallH  v a)) ->
              substT L (m n) v0 s = m n).
        { intros n H3;  apply subTermNil.
           intros H4.
           elim
             (newVar1
                (freeVarFormula L a ++
                   freeVarMap (List.remove eq_nat_dec v (freeVarFormula L a)) m)).
           fold nv1; rewrite a0.
           apply in_or_app; right.
           eapply freeVarMap1.
           apply H4.
           apply H3.
        }     
        assert (H4: nv1 = nv2).
        { unfold nv1, nv2; 
            rewrite
              (freeVarMap_ext (List.remove eq_nat_dec v (freeVarFormula L a))
                 (fun n : nat => substT L (m n) v0 s) m).
          - reflexivity.
          - apply H3.
        }    
        rewrite H4.
        rewrite
          (subAllFormula_ext a
             (fun v1 : nat =>
                match eq_nat_dec v1 v with
                | left _ => var nv2
                | right _ => substT L (m v1) v0 s
                end)
             (fun v1 : nat =>
                match eq_nat_dec v1 v with
                | left _ => var nv2
                | right _ => m v1
                end)).
      -- apply (iffRefl L).
      --    intros m0 H5; induction (eq_nat_dec m0 v).
            ++ reflexivity.
            ++ apply H3; simpl; apply in_in_remove; auto.
       *  apply (iffTrans L) with
           (forallH x
              (substituteFormula L
                 (subAllFormula a
                    (fun v1 : nat =>
                       match eq_nat_dec v1 v with
                       | left _ => var x
                       | right _ => m v1
                       end)) v0 s)).
         -- apply (reduceForall L).
            ++ apply (notInFreeVarSys L).
            ++ apply (reduceSub L).
               ** apply (notInFreeVarSys L).
               ** apply (iffTrans L) with
                    (subAllFormula a
                       (fun v1 : nat =>
                          substT L
                            match eq_nat_dec v1 v with
                            | left _ => var nv1
                            | right _ => m v1
                            end nv1 (var x))).
                  ---  fold (folProof.SysPrf L); 
                       apply
                         H
                         with
                         (b := a)
                         (v := nv1)
                         (s := var x)
                         (m := fun v1 : nat =>
                                 match eq_nat_dec v1 v with
                                 | left _ => var nv1
                                 | right _ => m v1
                                 end).
                       apply depthForall.
                  --- rewrite
                      (subAllFormula_ext a
                         (fun v1 : nat =>
                            match eq_nat_dec v1 v with
                            | left _ => var x
                            | right _ => m v1
                            end)
                         (fun v1 : nat =>
                            substT L
                              match eq_nat_dec v1 v with
                              | left _ => var nv1
                              | right _ => m v1
                              end nv1 (var x))).
                      +++ apply (iffRefl L).
                      +++    intros m0 H3. 
                             induction (eq_nat_dec m0 v).
                             *** rewrite (subTermVar1 L); reflexivity.
                             *** rewrite (subTermNil L). 
                                 reflexivity.
                                 intro H4;
                                   elim
                                     (newVar1
                                        (freeVarFormula L a ++
                                           freeVarMap (List.remove eq_nat_dec v 
                                                         (freeVarFormula L a)) m)).
                                 fold nv1; apply in_or_app.
                                 right.
                                 eapply freeVarMap1.
                                 apply H4.
                                 apply in_in_remove; auto.
         -- apply (iffTrans L)
              with
              (forallH x
                 (subAllFormula a
                    (fun v1 : nat =>
                       match eq_nat_dec v1 v with
                       | left _ => var x
                       | right _ => substT L (m v1) v0 s
                       end))).
            ++ apply (reduceForall L).
               ** apply (notInFreeVarSys L).
               ** eapply (iffTrans L). 
                  --- apply H with
                        (b := a)
                        (v := v0)
                        (s := s)
                        (m := fun v1 : nat =>
                                match eq_nat_dec v1 v with
                                | left _ => var x
                                | right _ => m v1
                                end).
                      apply depthForall.
                  ---    rewrite
                      (subAllFormula_ext a
                         (fun v1 : nat =>
                            match eq_nat_dec v1 v with
                            | left _ => var x
                            | right _ => substT L (m v1) v0 s
                            end)
                         (fun n : nat =>
                            substT L
                              match eq_nat_dec n v with
                              | left _ => var x
                              | right _ => m n
                              end v0 s)).
                         +++ apply (iffRefl L).
                         +++    intros m0 H3; induction (eq_nat_dec m0 v).
                                ***  rewrite subTermNil.
                                     reflexivity.
                                     simpl; tauto.
                                *** reflexivity.
            ++ apply (iffTrans L) with
                 (forallH nv2
                    (substituteFormula L
                       (subAllFormula a
                          (fun v1 : nat =>
                             match eq_nat_dec v1 v with
                             | left _ => var x
                             | right _ => substT L (m v1) v0 s
                             end)) x (var nv2))).
               ** apply (rebindForall L).
                  intros H3; simpl in H3.
                  assert
                    (H4: In nv2
                           (freeVarFormula L
                              (subAllFormula a
                                 (fun v1 : nat =>
                                    match eq_nat_dec v1 v with
                                    | left _ => var x
                                    | right _ => substT L (m v1) v0 s
                                    end)))) 
                  by (eapply in_remove; apply H3). 
                  decompose record (freeVarSubAllFormula1 _ _ _ H4) /r; intros x0 H6 H7.
                  induction (eq_nat_dec x0 v) as [a0 | ?].
                  --- induction H7 as [H5| H5].
                      +++ elim (in_remove_neq _ _ _ _ _ H3); auto.
                      +++    auto.
                  --- 
                    elim
                      (newVar1
                         (freeVarFormula L a ++
                            freeVarMap (List.remove  eq_nat_dec v (freeVarFormula L a))
                            (fun n : nat => substT L (m n) v0 s))).
                    fold nv2; apply in_or_app.
                    right;  eapply freeVarMap1.
                    +++ apply H7.
                    +++ apply in_in_remove; auto.
               ** apply (reduceForall L).
                  --- apply (notInFreeVarSys L).
                  --- eapply (iffTrans L).
                      +++ apply H.
                          apply depthForall.
                      +++ simpl;
                            rewrite
                              (subAllFormula_ext a
                                 (fun v1 : nat =>
                                    match eq_nat_dec v1 v with
                                    | left _ => var nv2
                                    | right _ => substT L (m v1) v0 s
                                    end)
                                 (fun n : nat =>
                                    substT L
                                      match eq_nat_dec n v with
                                      | left _ => var x
                                      | right _ => substT L (m n) v0 s
                                      end x (var nv2))).
                          *** apply (iffRefl L).
                          *** intros m0 H3; induction (eq_nat_dec m0 v).
                              rewrite (subTermVar1 L).
                              reflexivity.
                              rewrite (subTermNil L (substT L (m m0) v0 s)).
                              reflexivity.
                              intros H4; induction (freeVarSubTerm3 _ _ _ _ _ H4).
                              elim H2.
                              apply in_in_remove.
                             intros H6;
                                elim
                                  (newVar1
                                     (freeVarFormula L a ++
                                        freeVarMap (List.remove  eq_nat_dec v 
                                                      (freeVarFormula L a)) m)).
                              fold nv1; rewrite <- H6.
                              apply in_or_app.
                              right; eapply freeVarMap1.
                              eapply in_remove.
                              apply H5.
                              apply in_in_remove; auto.
                              eapply freeVarSubAllFormula2.
                              apply H3.
                              induction (eq_nat_dec m0 v).
                              elim b0; auto.
                              eapply in_remove.
                              apply H5. 
                              auto.
Qed.

Lemma subAllTermId (t : fol.Term L):
  subAllTerm t (fun x : nat => var x) = t.
Proof.
  elim t using  Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             subAllTerms n ts (fun x : nat => var x) = ts); 
    simpl. 
  - reflexivity.
  - intros f t0 H; now rewrite H.
  - reflexivity.
  - intros n t0 H t1 H0; now rewrite H, H0. 
Qed.

Lemma subAllTermsId  (n : nat) (ts : fol.Terms L n):
  subAllTerms n ts (fun x : nat => var x) = ts.
Proof.
  induction ts as [| n t ts Hrects].
  - reflexivity.
  - simpl; now rewrite Hrects, subAllTermId.
Qed.

Lemma subAllFormulaId (T : fol.System L) (f : fol.Formula L):
 folProof.SysPrf L T
   (iffH (subAllFormula f (fun x : nat => var x)) f).
Proof.
  apply (sysExtend L) with (Empty_set (fol.Formula L)).
  - intros x H; contradiction H.
  - induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf];
      simpl.
    + repeat rewrite subAllTermId; apply (iffRefl L).
    + rewrite subAllTermsId; apply (iffRefl L).
    + apply (reduceImp L).
      * apply Hrecf1.
      * apply Hrecf0.
    + apply (reduceNot L).
      apply Hrecf.
    + set
        (nv :=
           newVar
             (freeVarFormula L f ++
                freeVarMap (List.remove  eq_nat_dec n (freeVarFormula L f))
                (fun x : nat => var x))).
      apply
        (iffTrans L)
        with (forallH n (subAllFormula f (fun x : nat => var x))).
      * apply (iffTrans L) with
          (forallH nv
             (substituteFormula L (subAllFormula f (fun x : nat => var x)) n
                (var nv))).
        -- replace
            (subAllFormula f
               (fun v : nat =>
                  match eq_nat_dec v n with
                  | left _ => var nv
                  | right _ => var v
                  end)) 
            with
            (subAllFormula f
               (fun x : nat => substT L (var x) n (var nv))).
           ++ apply (reduceForall L).
              ** apply (notInFreeVarSys L).
              ** apply (iffSym L).
                 apply subSubAllFormula with (m := fun x : nat => var x).
           ++ apply subAllFormula_ext.
              intros m H; simpl.
              induction (eq_nat_dec n m); induction (eq_nat_dec m n);
                reflexivity || (assert False by auto; contradiction).
        -- apply (iffSym L).
           apply (rebindForall L).
           intro H;
             assert
               (H0: In nv (freeVarFormula L (subAllFormula f 
                                               (fun x : nat => var x))))
           by (eapply in_remove; apply H). 
           decompose record (freeVarSubAllFormula1 _ _ _ H0) /r; intros x H2 H3.
           elim
             (newVar1
                (freeVarFormula L f ++
                   freeVarMap (List.remove eq_nat_dec n (freeVarFormula L f))
                   (fun x : nat => var x))).
           fold nv; apply in_or_app; right.
           eapply freeVarMap1.
           ++ apply H3.
           ++ apply in_in_remove.
              ** destruct H3 as [H1| H1].
                 --- rewrite H1.
                     eapply in_remove_neq.
                     apply H.
                 --- contradiction.
              ** apply H2.
      * apply (reduceForall L).
        -- apply (notInFreeVarSys L).
        -- apply Hrecf.
Qed.

Lemma subAllSubAllTerm (t : fol.Term L) :
 forall  (m1 m2 : nat -> fol.Term L),
 subAllTerm (subAllTerm t m1) m2 =
 subAllTerm t (fun n : nat => subAllTerm (m1 n) m2).
Proof.
  elim t using
    Term_Terms_ind
    with
    (P0 := fun (n : nat) (ts : fol.Terms L n) =>
             forall m1 m2 : nat -> fol.Term L,
               subAllTerms n (subAllTerms n ts m1) m2 =
                 subAllTerms n ts (fun n : nat => subAllTerm (m1 n) m2));
    simpl.
  - reflexivity.
  - intros f t0 H m1 m2; now rewrite H.
  - reflexivity.
  - intros n t0 H t1 H0 m1 m2; now rewrite H, H0. 
Qed.

Lemma subAllSubAllTerms (n : nat) (ts : fol.Terms L n) (m1 m2 : nat -> fol.Term L):
 subAllTerms n (subAllTerms n ts m1) m2 =
 subAllTerms n ts (fun n : nat => subAllTerm (m1 n) m2).
Proof.
  induction ts as [| n t ts Hrects]; simpl.
  - reflexivity.
  - now rewrite Hrects, subAllSubAllTerm.
Qed.

Lemma subAllSubAllFormula (T : fol.System L) (f : fol.Formula L):
 forall  (m1 m2 : nat -> fol.Term L),
 folProof.SysPrf L T
   (iffH (subAllFormula (subAllFormula f m1) m2)
      (subAllFormula f (fun n : nat => subAllTerm (m1 n) m2))).
Proof.
  revert T.
  induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf]. 
  - intros T m1 m2; simpl; repeat rewrite subAllSubAllTerm; apply (iffRefl L).
  - intros T m1 m2; simpl; rewrite subAllSubAllTerms.
    apply (iffRefl L).
  - intros T m1 m2; simpl; apply (reduceImp L).
    + apply Hrecf1.
    + apply Hrecf0.
  - intros T m1 m2; simpl; apply (reduceNot L).
    apply Hrecf.
  - intros T m1 m2; simpl;
      set
        (nv1 :=
           freeVarFormula L f ++
             freeVarMap (List.remove eq_nat_dec n (freeVarFormula L f)) m1).
    set
      (nv2 :=
         freeVarFormula L f ++
           freeVarMap (List.remove eq_nat_dec n (freeVarFormula L f))
           (fun n0 : nat => subAllTerm (m1 n0) m2)).
    set
      (nv3 :=
         freeVarFormula L
           (subAllFormula f
              (fun v : nat =>
                 match eq_nat_dec v n with
                 | left _ => var (newVar nv1)
                 | right _ => m1 v
                 end)) ++
           freeVarMap
           (List.remove eq_nat_dec (newVar nv1)
              (freeVarFormula L
                 (subAllFormula f
                    (fun v : nat =>
                       match eq_nat_dec v n with
                       | left _ => var (newVar nv1)
                       | right _ => m1 v
                       end)))) m2).
    apply
      (iffTrans L)
      with
      (forallH (newVar nv3)
         (substituteFormula L
            (subAllFormula f
               (fun v : nat =>
                  match eq_nat_dec v n with
                  | left _ => var (newVar nv2)
                  | right _ => subAllTerm (m1 v) m2
                  end)) (newVar nv2) (var (newVar nv3)))).
    + eapply (sysExtend L) with (Empty_set (fol.Formula L)).
      * intros x H; contradiction  H.
      * apply (reduceForall L).
        -- apply (notInFreeVarSys L).
        -- eapply (iffTrans L).
           ++ apply Hrecf.
           ++ set
               (a1 :=
                  fun v : nat =>
                    match eq_nat_dec v n with
                    | left _ => var (newVar nv2)
                    | right _ => subAllTerm (m1 v) m2
                    end).
              simpl; set
                       (a2 :=
                          fun n0 : nat =>
                            subAllTerm
                              match eq_nat_dec n0 n with
                              | left _ => var (newVar nv1)
                              | right _ => m1 n0
                              end
                              (fun v : nat =>
                                 match eq_nat_dec v (newVar nv1) with
                                 | left _ => var (newVar nv3)
                                 | right _ => m2 v
                                 end)).
              replace (subAllFormula f a2) with
                (subAllFormula f
                   (fun x : nat =>
                      substT L (a1 x) (newVar nv2) (var (newVar nv3)))).
           ** apply (iffSym L).
              apply subSubAllFormula.
           ** apply subAllFormula_ext.
              intros m H. 
              unfold a1, a2; induction (eq_nat_dec m n).
              --- rewrite (subTermVar1 L).
                  simpl; induction (eq_nat_dec (newVar nv1) (newVar nv1)) as [? | b].
                  +++ reflexivity.
                  +++ now elim b.
              --- auto.
                  rewrite subSubAllTerm.
                  apply subAllTerm_ext.
                  intros m0 H0; induction (eq_nat_dec m0 (newVar nv1)) as [a | ?].
                  +++ elim (newVar1 nv1).
                      rewrite <- a.
                      unfold nv1; apply in_or_app; right.
                      eapply freeVarMap1.
                      *** apply H0.
                      *** apply in_in_remove; auto.
                  +++ apply (subTermNil L).
                      intro H1.
                      elim (newVar1 nv2).
                      unfold nv2 at 2; apply in_or_app; right.
                      eapply freeVarMap1.
                      *** eapply freeVarSubAllTerm2.
                          apply H0.
                          apply H1.
                      *** apply in_in_remove; auto.
    + apply (iffSym L).
      apply (rebindForall L).
      intro H;
        assert
          (H0:In (newVar nv3)
                (freeVarFormula L
                   (subAllFormula f
                      (fun v : nat =>
                         match eq_nat_dec v n with
                         | left _ => var (newVar nv2)
                         | right _ => subAllTerm (m1 v) m2
                         end))))
        by (eapply in_remove; apply H). 
      decompose record (freeVarSubAllFormula1 _ _ _ H0) /r; intros x H2 H3.
      induction (eq_nat_dec x n).
      * induction H3 as [H1| H1].
        -- elim (in_remove_neq _ _ _ _ _ H).
           ++ auto.
        -- contradiction.
      * decompose record (freeVarSubAllTerm1 _ _ _ H3) /r; intros x0 H4 H5.
        elim (newVar1 nv3).
        unfold nv3 at 2; apply in_or_app.
        right; eapply freeVarMap1.
        -- apply H5.
        -- apply in_in_remove.
           ++ intro H1; elim (newVar1 nv1).
              rewrite <- H1; unfold nv1; apply in_or_app; right.
              eapply freeVarMap1.
              apply H4.
              apply in_in_remove; auto.
           ++ eapply freeVarSubAllFormula2.
              ** apply H2.
              ** induction (eq_nat_dec x n) as [a | ?].
                 --- now elim b.
                 --- assumption. 
Qed.

Section subAllCloseFrom.

Fixpoint closeFrom (a n : nat) (f : fol.Formula L) {struct n} :
 fol.Formula L :=
  match n with
  | O => f
  | S m => forallH (a + m) (closeFrom a m f)
  end.

Opaque le_lt_dec.

Lemma liftCloseFrom  (n : nat) :
 forall(f : fol.Formula L) (T : fol.System L) (m : nat),
 (forall v : nat, In v (freeVarFormula L f) -> v < m) ->
 n <= m ->
 folProof.SysPrf L T (closeFrom 0 n f) ->
 folProof.SysPrf L T
   (closeFrom m n
      (subAllFormula f
         (fun x : nat =>
          match le_lt_dec n x with
          | left _ => var x
          | right _ => var (m + x)
          end))).
Proof.
  induction n as [| n Hrecn]; simpl.
  - intros; replace
              (subAllFormula f
                 (fun x : nat =>
                    match le_lt_dec 0 x with
                    | left _ => var x
                    | right _ => var (m + x)
                    end)) with (subAllFormula f (fun x : nat => var x)).
    + apply (impE L) with f.
      * apply (iffE2 L).
        apply subAllFormulaId.
      * apply H1.
    + apply subAllFormula_ext.
      intros m0 H2; induction (le_lt_dec 0 m0) as [? | b].
      * reflexivity.
      * elim (Nat.nlt_0_r _ b).
  - intros f T m H H0 H1; 
      apply (impE L) with (forallH n (closeFrom 0 n f)).
    + apply sysExtend with (Empty_set (fol.Formula L)).
      * intros x H2; contradiction H2. 
      * apply (impI L);  apply (forallI L).
        -- intros [x [H2 H3]];
             destruct H3 as [x H3| x H3]; destruct H3. 
           assert
             (H3:forall q : nat,
                 n <= q ->
                 m <= q -> 
                 ~ In q (freeVarFormula L (forallH n (closeFrom 0 n f)))).
           { clear H2 H1 T Hrecn.
             induction n as [| n Hrecn]; simpl in |- *.
           - intros q H1 H2 H3; assert (H': q < m). 
             { apply H; eapply in_remove; apply H3; lia. }
             lia. 
           - intros q H1 H2 H3; elim Hrecn with (q := q).
             + apply le_S_n.
               apply le_S.
               auto.
             + apply le_S_n.
               apply le_S.
               auto.
             + auto.
             + simpl; eapply in_remove.
               apply H3.
           }            
           apply H3 with (q := m + n).
           ++ apply Compat815.le_plus_r.
           ++ apply Nat.le_add_r.
           ++ apply H2.
        -- apply (impE L) with
             (closeFrom m n
                (substituteFormula L
                   (subAllFormula f
                      (fun x : nat =>
                         match le_lt_dec n x with
                         | left _ => var x
                         | right _ => var (m + x)
                         end)) n (var (m + n)))).
           ++ apply sysWeaken; clear H1 H T Hrecn.
              cut
                (folProof.SysPrf L (Empty_set (fol.Formula L))
                   (impH 
                      (substituteFormula L
                         (subAllFormula f
                            (fun x : nat =>
                               match le_lt_dec n x with
                               | left _ => var x
                               | right _ => var (m + x)
                               end)) n (var (m + n)))
                      (subAllFormula f
                         (fun x : nat =>
                            match le_lt_dec (S n) x with
                            | left _ => var x
                            | right _ => var (m + x)
                            end)))).
              ** generalize
                  (substituteFormula L
                     (subAllFormula f
                        (fun x : nat =>
                           match le_lt_dec n x with
                           | left _ => var x
                           | right _ => var (m + x)
                           end)) n (var (m + n))).
                 generalize
                   (subAllFormula f
                      (fun x : nat =>
                         match le_lt_dec (S n) x with
                         | left _ => var x
                         | right _ => var (m + x)
                         end)).
           clear f H0; intros f f0 H.
           induction n as [| n Hrecn]; simpl.
           --- apply H.
           --- apply (impI L).
               apply (forallI L).
               intros [x [H0 H1]];
                 induction H1 as [x H1| x H1]; [ induction H1 | induction H1 ].
               +++ now elim (in_remove_neq _ _ _ _ _ H0).
               +++ apply impE with (closeFrom m n f0).
                   *** apply sysWeaken.
                       apply Hrecn.
                   *** eapply forallSimp.
                       apply Axm; right; constructor.
              ** replace
                  (subAllFormula f
                     (fun x : nat =>
                        match le_lt_dec (S n) x with
                        | left _ => var x
                        | right _ => var (m + x)
                        end)) 
                  with
                  (subAllFormula f
                     (fun x : nat =>
                        substT L
                          match le_lt_dec n x with
                          | left _ => var x
                          | right _ => var (m + x)
                          end n (var (m + n)))).
                 --- apply (iffE1 L).
                     apply
                       subSubAllFormula
                       with
                       (m := fun x : nat =>
                               match le_lt_dec n x with
                               | left _ => var x
                               | right _ => var (m + x)
                               end).
                 --- apply subAllFormula_ext.
                     intros m0 H1; induction (le_lt_dec n m0) as [a | ?].
                     +++  induction (le_lt_dec (S n) m0).
                          *** apply (subTermVar2 L); lia.
                          *** rewrite Nat.lt_eq_cases in a.
                              destruct a. 
                              assert False by lia; contradiction.
                              rewrite H; apply (subTermVar1 L).
                     +++  induction (le_lt_dec (S n) m0). 
                          lia. 
                          apply (subTermVar2 L).
                          unfold not in |- *; intros.
                          rewrite H in H0.
                          rewrite Nat.le_ngt in H0. 
                          lia. 
           ++  assert
             (H2: forall (f : fol.Formula L) (s r m p : nat),
                 m < s ->
                 s + r <= p ->
                 folProof.SysPrf L (Empty_set (fol.Formula L))
                   (impH  (substituteFormula L (closeFrom s r f) m (var p))
                      (closeFrom s r (substituteFormula L f m (var p))))).
               { clear H0 H H1 m T f n Hrecn.
                 intros f s n.
                 induction n as [| n Hrecn]; simpl.  
                 - intros m p H H0; apply (impRefl L).
                 - intros m p H H0; rewrite (subFormulaForall L).
                   induction (eq_nat_dec (s + n) m) as [a | b].
                   + rewrite <- a in H; lia.
                   + induction (In_dec eq_nat_dec (s + n) (freeVarTerm L (var p)))
                       as [a | ?].
                     * induction a as [H1| H1].
                       -- rewrite Nat.add_succ_r in H0; simpl in H0.
                          rewrite <- H1 in H0; lia. 
                       -- contradiction.
                     * apply (impI L).
                       apply (forallI L).
                       intros [x [H1 H2]];
                         induction H2 as [x H2| x H2]; [ induction H2 | induction H2 ].
                       -- now elim (in_remove_neq _ _ _ _ _ H1).
                       -- apply impE 
                            with (substituteFormula L (closeFrom s n f) m (var p)).
                          ++ apply sysWeaken.
                             ** apply Hrecn.
                                --- auto.
                                --- apply le_S_n.
                                    apply le_S; lia.
                          ++ eapply (forallSimp L).
                             apply Axm; right; constructor.
               }           
               apply (impE L) with
                 (substituteFormula L
                    (closeFrom m n
                       (subAllFormula f
                          (fun x : nat =>
                             match le_lt_dec n x with
                             | left _ => var x
                             | right _ => var (m + x)
                             end))) n (var (m + n))).
               ** apply sysWeaken, H2. 
           --- apply H0;  auto.
           --- auto.
               ** apply (forallE L).
                  apply (impE L) with (forallH n (closeFrom 0 n f)).
                  --- apply sysExtend with (Empty_set (fol.Formula L)).
                      +++ intros x H3; destruct H3.
                      +++ apply (impI L), (forallI L).
                          *** intros [x [H3 H4]];
                                induction H4 as [x H4| x H4];
                                [ induction H4 | induction H4 ].
                              now elim (in_remove_neq _ _ _ _ _ H3).
                          *** apply Hrecn.
                              apply H.
                              apply le_S_n.
                              apply le_S.
                              auto.
                              eapply (forallSimp L).
                              apply Axm; right; constructor.
                  --- apply Axm; right; constructor.
    + apply H1.
Qed.

Lemma subAllCloseFrom1 :
  forall (n m : nat) (map : nat -> fol.Term L) (f : fol.Formula L)
         (T : fol.System L),
    (forall v : nat,
        v < n -> forall w : nat, In w (freeVarTerm L (map (m + v))) -> w < m) ->
    folProof.SysPrf L T (closeFrom m n f) ->
    folProof.SysPrf L T
      (subAllFormula f
         (fun x : nat =>
            match le_lt_dec m x with
            | left _ =>
                match le_lt_dec (m + n) x with
                | left _ => var x
                | right _ => map x
                end
            | right _ => var x
            end)).
Proof.
  intro n; induction n as [| n Hrecn]; simpl.
  - intros m map f T H H0; replace
      (subAllFormula f
         (fun x : nat =>
            match le_lt_dec m x with
            | left _ =>
                match le_lt_dec (m + 0) x with
                | left _ => var x
                | right _ => map x
                end
            | right _ => var x
            end)) 
      with (subAllFormula f (fun x : nat => var x)).
    + apply (impE L) with f.
      * apply (iffE2 L); apply subAllFormulaId.
      * apply H0.
    + apply subAllFormula_ext.
      intros m0 H1; rewrite <- plus_n_O.
      destruct (le_lt_dec m m0); reflexivity. 
  - intros m map f T H H0; apply  (impE L)  with
      (substituteFormula L
         (subAllFormula f
            (fun x : nat =>
               match le_lt_dec m x with
               | left _ =>
                   match le_lt_dec (m + n) x with
                   | left _ => var x
                   | right _ => map x
                   end
               | right _ => var x
               end)) (m + n) (map (m + n))).
    + replace
        (subAllFormula f
           (fun x : nat =>
              match le_lt_dec m x with
              | left _ =>
                  match le_lt_dec (m + S n) x with
                  | left _ => var x
                  | right _ => map x
                  end
              | right _ => var x
              end)) 
        with
        (subAllFormula f
           (fun x : nat =>
              substT L
                match le_lt_dec m x with
                | left _ =>
                    match le_lt_dec (m + n) x with
                    | left _ => var x
                    | right _ => map x
                    end
                | right _ => var x
                end (m + n) (map (m + n)))).
      * apply (iffE1 L); 
          apply subSubAllFormula with
          (m := fun x : nat =>
                  match le_lt_dec m x with
                  | left _ =>
                      match le_lt_dec (m + n) x with
                      | left _ => var x
                      | right _ => map x
                      end
                  | right _ => var x
                  end).
      * apply subAllFormula_ext.
        intros m0 H1; induction (le_lt_dec m m0) as [a | ?].
        -- rewrite  <-  Compat815.plus_Snm_nSm. 
           induction (le_lt_dec (S m + n) m0) as [a0 | ?].
           ++ simpl in a0; induction (le_lt_dec (m + n) m0).
              ** apply (subTermVar2 L).
               intros H2; rewrite H2 in a0; lia.
              ** lia.
           ++ induction (le_lt_dec (m + n) m0) as [a0 | ?].
              ** replace (m + n) with m0.
                 apply (subTermVar1 L).
                 simpl in b.
                 rewrite Nat.lt_eq_cases in a0. 
                 destruct a0. 
                 --- lia. 
                 --- auto.
              ** apply (subTermNil L).
                 intros H2; assert (H3: m + (m0 - m) = m0)
                 by (rewrite Nat.add_comm; apply Nat.sub_add, a).
                 assert (H4: m + n < m). 
                 { apply H with (m0 - m).
                   apply Nat.add_lt_mono_l with m. 
                   rewrite H3.
                   rewrite Nat.add_succ_r .
                   apply b.
                   rewrite H3.
                   apply H2.
                 } 
                 lia. 
        -- apply (subTermVar2 L).
            intro H2; rewrite <- H2 in b; elim (Compat815.lt_not_le _ _ b).
            apply Nat.le_add_r.
    + apply (forallE L).
      apply (impE L) with (forallH (m + n) (closeFrom m n f)).
      * apply sysExtend with (Empty_set (fol.Formula L)).
        -- intros x H1; induction H1.
        -- apply (impI L), (forallI L).
           ++ intros [x [H1 H2]];
                induction H2 as [x H2| x H2]; [ induction H2 | induction H2 ].
              now elim (in_remove_neq _ _ _ _ _ H1).
           ++ apply Hrecn.
              ** intros v H1; eapply H; apply Nat.lt_lt_succ_r, H1. 
              ** eapply (forallSimp L).
                 apply Axm; right; constructor.
      * apply H0.
Qed.

Lemma subAllCloseFrom :
  forall (n : nat) (m : nat -> fol.Term L) (f : fol.Formula L)
         (T : fol.System L),
    folProof.SysPrf L T (closeFrom 0 n f) ->
    folProof.SysPrf L T
      (subAllFormula f
         (fun x : nat =>
            match le_lt_dec n x with
            | left _ => var x
            | right _ => m x
            end)).
Proof.
  intros n m f T H;
    assert
      (H0: exists r : nat,
          (forall v : nat, v < n -> newVar (freeVarTerm L (m v)) <= r)).
  { clear H T f; induction n as [| n Hrecn].
    - exists 0; intros v H; lia.
    - destruct Hrecn as [x H]; exists (max (newVar (freeVarTerm L (m n))) x).
      + intros v H0; assert (H1: v <= n) by lia.
        induction (Compat815.le_lt_or_eq _ _ H1).
        * apply Nat.le_trans with x.
          -- apply H; auto.
          -- apply Nat.le_max_r.
        * rewrite H2; apply Nat.le_max_l.
  } 
  destruct H0 as (x, H0).
  set (r := max (max n (newVar (freeVarFormula L f))) x).
  set
    (f' :=
       subAllFormula f
         (fun x : nat =>
            match le_lt_dec n x with
            | left _ => var x
            | right _ => var (r + x)
            end)).
  set (m' := fun x : nat => m (x - r)).
  apply
    (impE L)
    with
    (subAllFormula f'
       (fun x : nat =>
          match le_lt_dec r x with
          | left _ =>
              match le_lt_dec (r + n) x with
              | left _ => var x
              | right _ => m' x
              end
          | right _ => var x
          end)).
  - replace
      (subAllFormula f
         (fun x0 : nat =>
            match le_lt_dec n x0 with
            | left _ => var x0
            | right _ => m x0
            end)) 
      with
      (subAllFormula f
         (fun x : nat =>
            subAllTerm
              match le_lt_dec n x with
              | left _ => var x
              | right _ => var (r + x)
              end
              (fun x0 : nat =>
                 match le_lt_dec r x0 with
                 | left _ =>
                     match le_lt_dec (r + n) x0 with
                     | left _ => var x0
                     | right _ => m' x0
                     end
                 | right _ => var x0
                 end))).
    + apply (iffE1 L).
      unfold f'; apply subAllSubAllFormula with
        (m1 := fun x0 : nat =>
                 match le_lt_dec n x0 with
                 | left _ => var x0
                 | right _ => var (r + x0)
                 end)
        (m2 := fun x0 : nat =>
                 match le_lt_dec r x0 with
                 | left _ =>
                     match le_lt_dec (r + n) x0 with
                     | left _ => var x0
                     | right _ => m' x0
                     end
                 | right _ => var x0
                 end).
    + unfold m'; apply subAllFormula_ext; intros m0 H1.
      induction (le_lt_dec n m0) as [a | ?].
      * simpl; induction (le_lt_dec r m0) as [a0 | ?].
        -- rewrite  Nat.le_ngt in a0; destruct a0.
           apply Nat.lt_le_trans with (newVar (freeVarFormula L f)).
           ++ now apply newVar2.
           ++ unfold r; eapply Nat.le_trans.
              ** apply Nat.le_max_r.
              ** apply Nat.le_max_l.
        -- reflexivity.
      * simpl; induction (le_lt_dec r (r + m0)) as [a | ?].
        -- induction (le_lt_dec (r + n) (r + m0)).
           ++ lia.
           ++ f_equal; lia. 
        -- lia. 
  - apply subAllCloseFrom1.  
    + intros v H1 w H2; apply Nat.lt_le_trans with (newVar (freeVarTerm L (m v))).
      * apply newVar2.
        unfold m' in H2; now replace (r + v - r) with v in H2 by lia.  
      * apply Nat.le_trans with x.
        -- now apply H0.
        -- unfold r; apply Nat.le_max_r.
    + unfold f'; clear f'; apply liftCloseFrom.
      * intros v H1; apply Nat.lt_le_trans with (newVar (freeVarFormula L f)).
        -- now apply newVar2.
        -- unfold r; eapply Nat.le_trans.
           ++ apply Nat.le_max_r.
           ++ apply Nat.le_max_l.
      * unfold r; eapply Nat.le_trans.
        -- apply Nat.le_max_l.
        -- apply Nat.le_max_l.
      * apply H.
Qed.

Lemma reduceSubAll :
  forall (T : fol.System L) (map : nat -> fol.Term L) (A B : fol.Formula L),
    (forall v : nat, ~ In_freeVarSys L v T) ->
    folProof.SysPrf L T (iffH A B) ->
    folProof.SysPrf L T (iffH (subAllFormula A map) (subAllFormula B map)).
Proof.
  assert
    (H: forall (T : fol.System L) (map : nat -> fol.Term L) (A B : fol.Formula L),
        (forall v : nat, ~ In_freeVarSys L v T) ->
        folProof.SysPrf L T (iffH  A B) ->
        folProof.SysPrf L T
          (impH  (subAllFormula A map) (subAllFormula B map))).
  { intros T map A B H H0;
      replace (impH  (subAllFormula A map) (subAllFormula B map)) 
      with
      (subAllFormula (impH  A B) map).
    - set (n := newVar (freeVarFormula L (impH A B))).
      replace (subAllFormula (impH A B) map) 
        with
        (subAllFormula (impH A B)
           (fun x : nat =>
              match le_lt_dec n x with
              | left _ => var x
              | right _ => map x
              end)).
      + apply subAllCloseFrom.
        induction n as [| n Hrecn].
        * simpl; apply (iffE1 L), H0. 
        * simpl; apply (forallI L).
          -- apply H.
          -- apply Hrecn. 
      + apply subAllFormula_ext.
        intros m H1; induction (le_lt_dec n m) as [a | ?].
        * rewrite Nat.le_ngt in a; destruct a. 
          unfold n; now apply newVar2.
        * auto.
    - reflexivity.
  } 
  intros T map A B H0 H1; apply (iffI L).
  - apply H; auto.
  - apply H; auto.
    now apply (iffSym L).
Qed.

End subAllCloseFrom.

Lemma subToSubAll (T : fol.System L) (A : fol.Formula L) (v : nat) (s : fol.Term L):
 folProof.SysPrf L T
   (iffH (substituteFormula L A v s)
      (subAllFormula A
         (fun x : nat =>
          match eq_nat_dec v x with
          | left _ => s
          | right _ => var x
          end))).
Proof.
  apply (iffTrans L) with
    (substituteFormula L (subAllFormula A (fun x : nat => var x)) v s).
  apply sysExtend with (Empty_set (fol.Formula L)).
  - intros x H; contradiction H.
  - apply (reduceSub L).
    intros [x [H H0]]; induction H0.
    apply (iffSym L),  subAllFormulaId.
  - eapply (iffTrans L).
    + apply subSubAllFormula.
    + replace
        (subAllFormula A
           (fun x : nat =>
              match eq_nat_dec v x with
              | left _ => s
              | right _ => var x
              end)) 
        with
        (subAllFormula A
           (fun n : nat => substT L ((fun x : nat => var x) n) v s)).
      * apply (iffRefl L).
      * apply subAllFormula_ext; intros m H; now simpl.
Qed.

Lemma subAllSubFormula :
  forall (T : fol.System L) (A : fol.Formula L) (v : nat) 
         (s : fol.Term L) (map : nat -> fol.Term L),
    folProof.SysPrf L T
      (iffH (subAllFormula (substituteFormula L A v s) map)
         (subAllFormula A
            (fun x : nat =>
               match eq_nat_dec v x with
               | left _ => subAllTerm s map
               | right _ => map x
               end))).
Proof.
  intros T A v s map; apply (sysExtend L) with (Empty_set (fol.Formula L)).
  - intros x H; contradiction H.
  - eapply (iffTrans L).
    + apply reduceSubAll.
      * intros v0 [x [H H0]]; contradiction H0. 
      * apply subToSubAll.
    + eapply (iffTrans L).
      * apply subAllSubAllFormula.
      * replace
          (subAllFormula A
             (fun x : nat =>
                match eq_nat_dec v x with
                | left _ => subAllTerm s map
                | right _ => map x
                end)) 
          with
          (subAllFormula A
             (fun n : nat =>
                subAllTerm
                  ((fun x : nat =>
                      match eq_nat_dec v x with
                      | left _ => s
                      | right _ => var x
                      end) n) map)).
        -- apply (iffRefl L).
        -- apply subAllFormula_ext.
           intros m H; induction (eq_nat_dec v m); auto.
Qed.

End SubAllVars.

